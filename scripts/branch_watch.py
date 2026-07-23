#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
branch_watch.py  —  Report which files are being changed on which branches.

Walks every remote branch, finds the commits not yet in `main`, and builds a
picture of who is touching what:

  * a per-branch table — PR, author, last activity, commits ahead, files
    touched, whether the branch still merges cleanly into `main`, and which
    *other* active branches it overlaps (⚠️ = those overlaps would actually
    conflict, computed with a real in-memory merge, not a filename guess);
  * a "hot files" view — files edited on more than one branch, conflicting
    files first;
  * an always-on list of merged / inactive branches (0 commits ahead of main).

Conflicts are computed with `git merge-tree --write-tree` (git >= 2.38): a true
three-way merge in memory, so "9 shared files but no conflict" is reported
correctly where a filename-overlap heuristic would cry wolf.

USAGE
  python3 scripts/branch_watch.py                 # print markdown to stdout
  python3 scripts/branch_watch.py --fetch         # `git fetch` first
  python3 scripts/branch_watch.py --update-issue   # PATCH the pinned issue
      # (finds the open issue whose body carries the ISSUE_MARKER below, or the
      #  issue given by --issue N; needs GITHUB_TOKEN in the environment)

PR data and issue updates use the GitHub REST API over stdlib urllib — no `gh`
or `jq` needed. Without a token the PR column is left blank and the git-only
analysis still runs.
"""

import argparse
import itertools
import json
import os
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone

# A branch is updated in place by locating the one open issue whose body
# contains this marker. Keep it stable; it is how the updater finds "its" issue.
ISSUE_MARKER = "<!-- branch-watch:auto -->"
REMOTE = "origin"


# --------------------------------------------------------------------------
# git helpers
# --------------------------------------------------------------------------
def git(*args):
    """Run a git command, return stripped stdout."""
    r = subprocess.run(["git", *args], capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(f"git {' '.join(args)} failed:\n{r.stderr}")
        raise SystemExit(1)
    return r.stdout.strip()


def merges_clean(a, b):
    """True if a three-way merge of refs a and b has no conflicts."""
    r = subprocess.run(
        ["git", "merge-tree", "--write-tree", a, b],
        capture_output=True, text=True,
    )
    # 0 = clean, 1 = conflicts. Anything else (e.g. unrelated histories) we
    # treat conservatively as "cannot cleanly merge".
    return r.returncode == 0


def main_ref():
    """Remote-tracking ref for the default branch."""
    return f"{REMOTE}/main"


def collect_branches():
    """Return {ref: info} for every remote branch except HEAD and main."""
    main = main_ref()
    refs = git(
        "for-each-ref", "--format=%(refname:short)", f"refs/remotes/{REMOTE}"
    ).splitlines()
    branches = {}
    for ref in refs:
        ref = ref.strip()
        # `refs/remotes/origin/HEAD` shortens to bare `origin`; skip it too.
        if ref in (REMOTE, f"{REMOTE}/HEAD", main) or "->" in ref:
            continue
        base = git("merge-base", main, ref)
        ahead = int(git("rev-list", "--count", f"{main}..{ref}") or "0")
        files = (
            set(git("diff", "--name-only", base, ref).splitlines()) if base else set()
        )
        author = git("log", "-1", "--format=%an", ref)
        when = git("log", "-1", "--format=%ad", "--date=relative", ref)
        clean_to_main = merges_clean(main, ref) if ahead else True
        branches[ref] = {
            "short": ref[len(REMOTE) + 1:],
            "ahead": ahead,
            "files": files,
            "author": author,
            "when": when,
            "clean_to_main": clean_to_main,
        }
    return branches


def pairwise_conflicts(branches):
    """Return {ref: set(conflicting refs)} over active branches sharing files."""
    conf = {r: set() for r in branches}
    active = [r for r, b in branches.items() if b["ahead"] > 0]
    for a, b in itertools.combinations(active, 2):
        if branches[a]["files"] & branches[b]["files"] and not merges_clean(a, b):
            conf[a].add(b)
            conf[b].add(a)
    return conf


# --------------------------------------------------------------------------
# GitHub API (optional enrichment)
# --------------------------------------------------------------------------
def repo_slug():
    """owner/name, from GITHUB_REPOSITORY or the origin remote."""
    if os.environ.get("GITHUB_REPOSITORY"):
        return os.environ["GITHUB_REPOSITORY"]
    url = git("remote", "get-url", REMOTE)
    slug = url.split("github.com", 1)[-1].lstrip(":/")
    return slug[:-4] if slug.endswith(".git") else slug


def api(method, path, token, body=None):
    """Minimal GitHub REST call. Returns parsed JSON (or None on 4xx/5xx)."""
    req = urllib.request.Request(
        f"https://api.github.com{path}",
        method=method,
        data=json.dumps(body).encode() if body is not None else None,
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "Content-Type": "application/json",
            "User-Agent": "branch-watch",
        },
    )
    try:
        with urllib.request.urlopen(req) as resp:
            return json.load(resp)
    except urllib.error.HTTPError as e:
        sys.stderr.write(f"GitHub API {method} {path} -> {e.code}: {e.read()[:200]}\n")
        return None


def fetch_prs(slug, token):
    """Map branch short-name -> {num, url, draft} for open PRs."""
    prs = {}
    page = 1
    while True:
        batch = api(
            "GET",
            f"/repos/{slug}/pulls?state=open&per_page=100&page={page}",
            token,
        )
        if not batch:
            break
        for pr in batch:
            prs[pr["head"]["ref"]] = {
                "num": pr["number"],
                "url": pr["html_url"],
                "draft": pr.get("draft", False),
            }
        if len(batch) < 100:
            break
        page += 1
    return prs


# --------------------------------------------------------------------------
# markdown rendering
# --------------------------------------------------------------------------
def pr_cell(short, prs):
    pr = prs.get(short)
    if not pr:
        return "—"
    tag = " _(draft)_" if pr["draft"] else ""
    return f"[#{pr['num']}]({pr['url']}){tag}"


def branch_link(short, slug):
    """A Markdown link from a branch's name to its page on GitHub.

    Points at the branch's tree view (`/tree/<branch>`); the separate PR column
    links the branch's open PR, if any.  Works without a token, since the URL is
    derived purely from the branch name.  The slash in a name like
    `bcp/versification5` is kept (GitHub tree paths use it); other reserved
    characters are percent-encoded.  Falls back to a bare code span if the repo
    slug could not be determined."""
    if not slug:
        return f"`{short}`"
    quoted = urllib.parse.quote(short, safe="/")
    return f"[`{short}`](https://github.com/{slug}/tree/{quoted})"


def files_cell(files):
    """A <details> expander listing files, valid inside a Markdown table cell."""
    n = len(files)
    if n == 0:
        return "0"
    inner = "<br>".join(f"`{f}`" for f in sorted(files))
    return f"<details><summary>{n}</summary>{inner}</details>"


def render(branches, conf, prs, have_token, slug):
    active = {r: b for r, b in branches.items() if b["ahead"] > 0}
    merged = {r: b for r, b in branches.items() if b["ahead"] == 0}

    # file -> [active refs]
    fmap = {}
    for r, b in active.items():
        for f in b["files"]:
            fmap.setdefault(f, []).append(r)
    hot = {f: rs for f, rs in fmap.items() if len(rs) > 1}

    def file_conflicts(refs):
        return any(a in conf[b] for a, b in itertools.combinations(refs, 2))

    conflicting_files = {f: rs for f, rs in hot.items() if file_conflicts(rs)}
    clean_files = {f: rs for f, rs in hot.items() if not file_conflicts(rs)}

    n_conf_main = sum(1 for b in active.values() if not b["clean_to_main"])
    n_conf_pairs = sum(len(v) for v in conf.values()) // 2

    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    summary = (
        f"_Auto-updated {now} · {len(active)} active branch(es) · "
        f"{n_conf_main} conflict with `main` · {n_conf_pairs} conflicting "
        f"branch-pair(s) · {len(conflicting_files)} contested file(s)_"
    )
    out = [ISSUE_MARKER, "", "## 🔭 Branch & file activity", ""]
    if not have_token:
        out.append("> ⚠️ No `GITHUB_TOKEN` available — PR column left blank.")
        out.append("")

    # ---- per-branch table (most commits ahead first) ----
    out.append("### Branches")
    out.append("")
    out.append("| Branch | PR | Author | Last activity | Ahead | Files | → main | Overlaps |")
    out.append("|---|---|---|---|--:|--:|:--:|---|")
    for r, b in sorted(active.items(), key=lambda x: -x[1]["ahead"]):
        overlaps = sorted(
            o for o in active if o != r and active[o]["files"] & b["files"]
        )
        ov = ", ".join(
            ("⚠️ " if o in conf[r] else "") + branch_link(active[o]["short"], slug)
            for o in overlaps
        ) or "—"
        main_flag = "✅" if b["clean_to_main"] else "⚠️"
        out.append(
            f"| {branch_link(b['short'], slug)} | {pr_cell(b['short'], prs)} | {b['author']} | "
            f"{b['when']} | {b['ahead']} | {files_cell(b['files'])} | "
            f"{main_flag} | {ov} |"
        )
    out.append("")

    # ---- hot files: conflicting first, then clean co-edits ----
    out.append("### Hot files")
    out.append("")

    def hot_table(files):
        rows = ["| File | # | Branches |", "|---|--:|---|"]
        for f, refs in sorted(files.items(), key=lambda x: -len(x[1])):
            labels = []
            for o in sorted(refs):
                clash = any(o in conf[p] for p in refs if p != o)
                labels.append(("⚠️ " if clash else "") + branch_link(active[o]["short"], slug))
            rows.append(f"| `{f}` | {len(refs)} | {', '.join(labels)} |")
        return rows

    if conflicting_files:
        out.append("#### ⚠️ Conflicting")
        out.append("")
        out += hot_table(conflicting_files)
        out.append("")
    if clean_files:
        out.append("#### Co-edited (merges clean)")
        out.append("")
        out += hot_table(clean_files)
        out.append("")
    if not hot:
        out.append("_No file is touched by more than one active branch._")
        out.append("")

    # ---- merged / inactive branches (always shown) ----
    out.append("### Merged / inactive branches")
    out.append("")
    if merged:
        out.append("_0 commits ahead of `main` — fully merged or pointing at an ancestor._")
        out.append("")
        for r, b in sorted(merged.items()):
            out.append(f"- {branch_link(b['short'], slug)} — last activity {b['when']} ({b['author']})")
    else:
        out.append("_None._")
    out.append("")

    out.append("---")
    out.append(summary)

    return "\n".join(out)


# --------------------------------------------------------------------------
# issue update
# --------------------------------------------------------------------------
def find_issue(slug, token, explicit):
    if explicit:
        return explicit
    issues = api("GET", f"/repos/{slug}/issues?state=open&per_page=100", token)
    for it in issues or []:
        if "pull_request" not in it and ISSUE_MARKER in (it.get("body") or ""):
            return it["number"]
    return None


ISSUE_TITLE = "🔭 Branch & file activity"


def update_issue(slug, token, number, body):
    if not number:
        # First run: create the tracking issue. The marker in `body` lets every
        # later run find it. (Pinning is a one-time manual click in the UI —
        # the REST API cannot pin; do it once and updates land in place.)
        res = api("POST", f"/repos/{slug}/issues", token,
                  {"title": ISSUE_TITLE, "body": body})
        if res is None:
            raise SystemExit(1)
        print(f"Created issue #{res['number']}: {res['html_url']} "
              f"(pin it once in the UI)", file=sys.stderr)
        return
    res = api("PATCH", f"/repos/{slug}/issues/{number}", token, {"body": body})
    if res is None:
        raise SystemExit(1)
    print(f"Updated issue #{number}: {res['html_url']}", file=sys.stderr)


# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fetch", action="store_true", help="git fetch before analysis")
    ap.add_argument("--update-issue", action="store_true",
                    help="PATCH the pinned issue instead of printing to stdout")
    ap.add_argument("--issue", type=int, default=None,
                    help="explicit issue number (default: find by marker)")
    args = ap.parse_args()

    if args.fetch:
        git("fetch", "--prune", REMOTE)

    token = os.environ.get("GITHUB_TOKEN")
    slug = repo_slug()
    branches = collect_branches()
    conf = pairwise_conflicts(branches)

    prs = {}
    if token:
        prs = fetch_prs(slug, token)

    body = render(branches, conf, prs, have_token=bool(token), slug=slug)

    if args.update_issue:
        if not token:
            sys.stderr.write("--update-issue needs GITHUB_TOKEN.\n")
            raise SystemExit(1)
        slug = repo_slug()
        update_issue(slug, token, find_issue(slug, token, args.issue), body)
    else:
        print(body)


if __name__ == "__main__":
    main()
