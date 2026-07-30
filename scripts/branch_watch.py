#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
branch_watch.py  —  Report which files are being changed on which branches.

Walks every remote branch, finds the commits not yet in `main`, and builds a
picture of who is touching what:

  * a per-PR table (most recently active first) — the branch (linked to its
    PR) with its author beneath in small type, a Status column, any `#Note: …`
    lines reviewers left on the PR, activity, which *other* PR branches it
    shares files with (⚠️ = those overlaps would actually conflict, computed
    with a real in-memory merge, not a filename guess), and a compact Changes
    count.  The Status cell reports the open PR's readiness: "N comments" (open
    review threads), "Ready to merge" (approved, nothing unresolved), a
    "🚧 auto-merge held" flag when auto-merge is enabled but the PR is *not*
    sitting in the merge queue because something is holding it up, and a
    "⚠️ conflicts with `main`" flag when the branch no longer merges cleanly.
    Only branches with an open PR appear, and only they are weighed when marking
    overlaps and conflicts;
  * a "hot files" view — files edited on more than one PR branch, conflicting
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

PR data is read via the GitHub GraphQL API (review decision, unresolved
threads, auto-merge, merge-queue membership); issue updates use the REST API.
Both go over stdlib urllib — no `gh` or `jq` needed. Because the report now
shows PR branches only, a run without a token (which cannot see PRs) produces
an empty report.
"""

import argparse
import itertools
import json
import os
import re
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


_ANCESTRY_CACHE = {}


def contains(container, ref):
    """True if `container` includes every commit of `ref` — i.e. `ref` is an
    ancestor of `container` (or they are the same commit)."""
    key = (container, ref)
    if key not in _ANCESTRY_CACHE:
        r = subprocess.run(
            ["git", "merge-base", "--is-ancestor", ref, container],
            capture_output=True, text=True,
        )
        _ANCESTRY_CACHE[key] = r.returncode == 0
    return _ANCESTRY_CACHE[key]


def independent_branches(refs):
    """Reduce a set of branches that all touched one file to the independent
    lines of work: drop any branch whose commits are already contained in
    another branch in the set (it has been merged into, or is an ancestor of,
    that other branch).  Without this, a file edited only on branch A is
    reported as "co-edited" by every downstream branch that has since pulled A
    in — not a real concurrent edit.  Two branches at the same commit (mutually
    contained) keep the lexicographically smaller name."""
    refs = list(refs)
    keep = []
    for x in refs:
        subsumed = any(
            y != x and contains(y, x) and not (contains(x, y) and x < y)
            for y in refs
        )
        if not subsumed:
            keep.append(x)
    return keep


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
        short = ref[len(REMOTE) + 1:]
        # `refs/remotes/origin/HEAD` shortens to bare `origin`; skip it too.
        # `archive/*` branches are point-in-time snapshots, not active work, so
        # they are left out of the activity table.
        if (ref in (REMOTE, f"{REMOTE}/HEAD", main) or "->" in ref
                or short.startswith("archive/")):
            continue
        base = git("merge-base", main, ref)
        ahead = int(git("rev-list", "--count", f"{main}..{ref}") or "0")
        files = (
            set(git("diff", "--name-only", base, ref).splitlines()) if base else set()
        )
        author = git("log", "-1", "--format=%an", ref)
        email = git("log", "-1", "--format=%ae", ref)
        sha = git("log", "-1", "--format=%H", ref)
        when = git("log", "-1", "--format=%ad", "--date=relative", ref)
        # Git's relative dates end in " ago"; drop it for a tighter column.
        if when.endswith(" ago"):
            when = when[:-4]
        # Committer timestamp (unix) of the branch tip, for "most recent
        # activity" sorting — the relative `when` string can't be sorted.
        ts = int(git("log", "-1", "--format=%ct", ref) or "0")
        clean_to_main = merges_clean(main, ref) if ahead else True
        branches[ref] = {
            "short": short,
            "ahead": ahead,
            "files": files,
            "author": author,
            "email": email,
            "sha": sha,
            "login": None,  # GitHub username, filled in later when a token is set
            "when": when,
            "ts": ts,
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


def graphql(query, variables, token):
    """Minimal GitHub GraphQL call. Returns the parsed `data` object, or None on
    transport/GraphQL error."""
    req = urllib.request.Request(
        "https://api.github.com/graphql",
        method="POST",
        data=json.dumps({"query": query, "variables": variables}).encode(),
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "Content-Type": "application/json",
            "User-Agent": "branch-watch",
        },
    )
    try:
        with urllib.request.urlopen(req) as resp:
            payload = json.load(resp)
    except urllib.error.HTTPError as e:
        sys.stderr.write(f"GitHub GraphQL -> {e.code}: {e.read()[:200]}\n")
        return None
    if payload.get("errors"):
        sys.stderr.write(f"GitHub GraphQL errors: {payload['errors']}\n")
    return payload.get("data")


def login_from_email(email):
    """GitHub username parsed from a `…@users.noreply.github.com` commit email
    (`user@…` or `12345+user@…`), or None for any other address."""
    if not email.endswith("@users.noreply.github.com"):
        return None
    local = email.split("@", 1)[0]
    return local.split("+", 1)[1] if "+" in local else local


def commit_login(slug, sha, token):
    """The GitHub username linked to commit `sha` (via its verified author
    email), from the API — or None if unlinked or unavailable."""
    data = api("GET", f"/repos/{slug}/commits/{sha}", token)
    if isinstance(data, dict) and isinstance(data.get("author"), dict):
        return data["author"].get("login")
    return None


_REALNAME_CACHE = {}


def user_realname(login, token):
    """The display name on a GitHub user's profile (e.g. `Yipeng Liu` for
    `@berberman`), from the users API — or None if the profile sets no name or
    the lookup is unavailable.  This is how a handle that hides a real identity
    ("Potato Hatsue (@berberman)") gets the actual person's name attached
    automatically.  Cached per login, so someone with several branches is
    fetched once.  Needs a token; without one the users endpoint is rate-limited
    to near-uselessness, so we skip it."""
    if not token or not login:
        return None
    if login not in _REALNAME_CACHE:
        data = api("GET", f"/users/{login}", token)
        _REALNAME_CACHE[login] = data.get("name") if isinstance(data, dict) else None
    return _REALNAME_CACHE[login]


# A reviewer flags a note for this table by writing a line `#Note: …` in a PR
# comment; the text after the marker (to end of line) is surfaced in the table.
_NOTE_RE = re.compile(r"#Note:\s*(.*)", re.IGNORECASE)


# GraphQL is used (rather than the REST `pulls` list) because it returns the
# review decision, unresolved-thread count, auto-merge flag, and merge-queue
# membership in one request per page — the REST API exposes none of these
# directly.
_PR_QUERY = """
query($owner:String!, $name:String!, $cursor:String) {
  repository(owner:$owner, name:$name) {
    pullRequests(states:OPEN, first:50, after:$cursor) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        url
        isDraft
        headRefName
        reviewDecision
        autoMergeRequest { enabledAt }
        mergeQueueEntry { state }
        reviewThreads(first:100) { nodes { isResolved } }
        closingIssuesReferences(first:10) { nodes { number url } }
        comments(first:100) { nodes { body } }
      }
    }
  }
}
"""


def fetch_prs(slug, token):
    """Map branch short-name -> per-PR dict for open PRs.

    Each value carries `num`, `url`, `draft`, `review_decision`
    (`REVIEW_REQUIRED`/`APPROVED`/`CHANGES_REQUESTED`/None), the count of
    `unresolved` review threads, the `auto_merge` / `in_queue` booleans that
    together reveal an auto-merge that is stuck outside the merge queue, and the
    list of `#Note: …` `notes` reviewers left in the PR conversation."""
    owner, _, name = slug.partition("/")
    prs = {}
    cursor = None
    while True:
        data = graphql(_PR_QUERY, {"owner": owner, "name": name, "cursor": cursor}, token)
        repo = (data or {}).get("repository")
        if not repo:
            break
        conn = repo["pullRequests"]
        for pr in conn["nodes"]:
            threads = pr["reviewThreads"]["nodes"]
            unresolved = sum(1 for t in threads if not t["isResolved"])
            # Issues the PR body links with a GitHub closing keyword
            # (fixes/closes/resolves #N); GitHub resolves these for us.
            closes = [{"num": i["number"], "url": i["url"]}
                      for i in pr["closingIssuesReferences"]["nodes"]]
            # `#Note: …` lines a reviewer left in the PR conversation.
            notes = []
            for c in pr["comments"]["nodes"]:
                notes += _NOTE_RE.findall(c["body"] or "")
            notes = [n.strip() for n in notes if n.strip()]
            prs[pr["headRefName"]] = {
                "num": pr["number"],
                "url": pr["url"],
                "draft": pr["isDraft"],
                "review_decision": pr["reviewDecision"],
                "unresolved": unresolved,
                "auto_merge": pr["autoMergeRequest"] is not None,
                "in_queue": pr["mergeQueueEntry"] is not None,
                "closes": closes,
                "notes": notes,
            }
        if conn["pageInfo"]["hasNextPage"]:
            cursor = conn["pageInfo"]["endCursor"]
        else:
            break
    return prs


# --------------------------------------------------------------------------
# markdown rendering
# --------------------------------------------------------------------------
def author_cell(b):
    """Author identity for a branch: the person's real name from their GitHub
    profile when it has one (so `@berberman` reads as `Yipeng Liu`), otherwise
    the last-commit author name, with the GitHub `@handle` appended when known."""
    name = b.get("realname") or b["author"]
    return f"{name} (@{b['login']})" if b.get("login") else name


def status_text(pr):
    """Review / merge readiness of an open PR, as a short string (may be empty
    for a draft with nothing else to report).

    * "(N comments)" — N review threads are still open.
    * "Ready to merge" — approved with nothing unresolved.
    * "🚧 auto-merge held" — auto-merge is enabled but the PR is not in the
      merge queue, so something (failing check, missing approval, conflict) is
      holding it up; "⏳ queued" when it *is* sitting in the queue.
    * "Fixes #N" — issues the PR closes (via a fixes/closes/resolves keyword),
      linked; several are comma-separated.

    Segments are joined with " · "; the readiness word and its "(N comments)"
    count stay together as one segment (e.g. "Approved (1 comment)")."""
    unresolved = pr["unresolved"]
    readiness = []
    if not pr["draft"]:
        dec = pr["review_decision"]
        if dec == "CHANGES_REQUESTED":
            readiness.append("Changes requested")
        elif dec != "REVIEW_REQUIRED":  # APPROVED, or None (no required review configured — rare here)
            readiness.append("Ready to merge" if unresolved == 0 else "Approved")
    if unresolved:
        readiness.append(f"({unresolved} comment{'' if unresolved == 1 else 's'})")
    segments = []
    if readiness:
        segments.append(" ".join(readiness))
    if pr["auto_merge"]:
        segments.append("⏳ queued" if pr["in_queue"] else "🚧 auto-merge held")
    if pr["closes"]:
        links = ", ".join(f"[#{i['num']}]({i['url']})" for i in pr["closes"])
        segments.append(f"Fixes {links}")
    return " · ".join(segments)


def pr_cell(short, prs):
    """The PR link for a branch, followed by its review/merge status (the two
    were merged into one column)."""
    pr = prs.get(short)
    if not pr:
        return "No PR"
    tag = " _(draft)_" if pr["draft"] else ""
    status = status_text(pr)
    sep = f": {status}" if status else ""
    return f"[#{pr['num']}]({pr['url']}){tag}{sep}"


def branch_link(short, slug, maxlen=None, href=None):
    """A Markdown link from a branch's name to a page on GitHub.

    By default points at the branch's tree view (`/tree/<branch>`); pass `href`
    to retarget it — the per-PR table sends the first cell straight to the
    open PR when one exists.  Works without a token, since the tree URL is
    derived purely from the branch name.  The slash in a name like
    `bcp/versification5` is kept (GitHub tree paths use it); other reserved
    characters are percent-encoded.  Falls back to a bare code span if neither
    an `href` nor a repo slug is available.

    When `maxlen` is given and the name is longer, the *visible* text is
    truncated with an ellipsis and the full name is kept as the link's hover
    title, so a wide table stays narrow; the link target is always the full
    branch name."""
    if maxlen and len(short) > maxlen:
        display = short[: maxlen - 1] + "…"
        title = f' "{short}"'
    else:
        display = short
        title = ""
    if href is None:
        if not slug:
            return f"`{display}`"
        quoted = urllib.parse.quote(short, safe="/")
        href = f"https://github.com/{slug}/tree/{quoted}"
    return f"[`{display}`]({href}{title})"


def notes_cell(pr):
    """The `#Note: …` lines reviewers left on a PR, one per line — or an empty
    cell when there are none (or no PR)."""
    notes = pr.get("notes") if pr else None
    if not notes:
        return ""
    return "<br>".join(notes)


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
    # Collapse each file's editor list to independent lines of work: if one
    # branch already contains another's commits, that "shared" edit is a single
    # edit carried downstream, not a concurrent co-edit.
    fmap = {f: independent_branches(rs) for f, rs in fmap.items()}
    hot = {f: rs for f, rs in fmap.items() if len(rs) > 1}

    def file_conflicts(refs):
        return any(a in conf[b] for a, b in itertools.combinations(refs, 2))

    conflicting_files = {f: rs for f, rs in hot.items() if file_conflicts(rs)}
    clean_files = {f: rs for f, rs in hot.items() if not file_conflicts(rs)}
    single_files = {f: rs for f, rs in fmap.items() if len(rs) == 1}

    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    def _blob(path, text=None):
        text = text or path
        return (f"[`{text}`](https://github.com/{slug}/blob/main/{path})"
                if slug else f"`{text}`")

    script_link = _blob("scripts/branch_watch.py")
    workflow_link = _blob(".github/workflows/branch-watch.yml", "branch-watch")
    summary = (f"_Auto-updated {now} by the {workflow_link} workflow running "
               f"{script_link} — run the script with `--update-issue` (and a "
               f"`GITHUB_TOKEN`) to refresh manually._")
    out = [ISSUE_MARKER, "", "## Current Activity", ""]
    if not have_token:
        out.append("> ⚠️ No `GITHUB_TOKEN` available — PRs cannot be read, so "
                   "this report is empty.")
        out.append("")

    # ---- per-PR table (most recently active first) ----
    out.append("### Current PRs")
    out.append("")
    out.append("| Branch / Author | Status | `#Note`s | Activity | Shares files with | Changes |")
    out.append("|---|---|---|---|---|--:|")
    for r, b in sorted(active.items(), key=lambda x: (-x[1]["ts"], x[1]["short"])):
        overlaps = [o for o in active if o != r and active[o]["files"] & b["files"]]
        # A stacked branch — one that fully contains the other's commits — is the
        # same line of work, not a concurrent co-edit (and can never conflict, so
        # never a ⚠️).  Pull those out of the overlap list and label them
        # explicitly, relative to this row's branch: `includes o` when r
        # contains o, `included in o` when r itself sits inside o.
        contains_o = sorted(o for o in overlaps if contains(r, o))
        contained_by = sorted(o for o in overlaps if contains(o, r))
        rest = [o for o in overlaps if o not in contains_o and o not in contained_by]
        # Among the genuinely concurrent overlaps that remain, group a superseded
        # one under the branch that already contains it, so one line of work
        # carried across several branches reads as a single overlap with a single
        # ⚠️, not several.  `A (included in B)` names the superseded
        # branches A first, then the container B whose commits already include
        # them; the ⚠️ (real merge conflict) is shown once, on the container.
        heads = sorted(independent_branches(rest))
        pieces = []
        for h in heads:
            subs = sorted(o for o in rest if o != h and contains(h, o))
            prefix = "⚠️ " if h in conf[r] else ""
            h_link = branch_link(active[h]["short"], slug)
            if subs:
                piece = prefix + ", ".join(
                    branch_link(active[o]["short"], slug) for o in subs) \
                    + " (included in " + h_link + ")"
            else:
                piece = prefix + h_link
            pieces.append(piece)
        pieces += ["includes " + branch_link(active[o]["short"], slug)
                   for o in contains_o]
        pieces += ["included in " + branch_link(active[o]["short"], slug)
                   for o in contained_by]
        ov = ", ".join(pieces) or "—"
        pr = prs.get(b["short"])
        # First cell: the branch (linked to its PR) with its author beneath in
        # small type — the two former columns folded into one.
        branch = branch_link(b["short"], slug, maxlen=25,
                             href=pr["url"] if pr else None)
        first = f"{branch}<br><sub>{author_cell(b)}</sub>"
        # The old "→ main" column is folded in here: flag a branch that no
        # longer merges cleanly right in the Status cell.
        status = pr_cell(b["short"], prs)
        if not b["clean_to_main"]:
            status += " · ⚠️ conflicts with `main`"
        out.append(
            f"| {first} | {status} | {notes_cell(pr)} | "
            f"{b['when']} | {ov} | {files_cell(b['files'])} |"
        )
    out.append("")

    # ---- files: conflicting first, then clean co-edits, then single-branch ----
    out.append("### Active files")
    out.append("")

    def file_table(files):
        rows = ["| File | # | Branches |", "|---|--:|---|"]
        for f, refs in sorted(files.items(), key=lambda x: (-len(x[1]), x[0])):
            labels = []
            for o in sorted(refs):
                clash = any(o in conf[p] for p in refs if p != o)
                labels.append(("⚠️ " if clash else "") + branch_link(active[o]["short"], slug))
            rows.append(f"| `{f}` | {len(refs)} | {', '.join(labels)} |")
        return rows

    if conflicting_files:
        out.append("#### ⚠️ Conflicting")
        out.append("")
        out += file_table(conflicting_files)
        out.append("")
    if clean_files:
        out.append("#### Co-edited (merges clean)")
        out.append("")
        out += file_table(clean_files)
        out.append("")
    if single_files:
        out.append("#### Single-branch")
        out.append("")
        out += file_table(single_files)
        out.append("")
    if not fmap:
        out.append("_No files modified on any PR branch._")
        out.append("")

    # ---- merged / inactive branches (always shown) ----
    out.append("### Merged / inactive branches")
    out.append("")
    if merged:
        out.append("_0 commits ahead of `main` — fully merged or pointing at an ancestor._")
        out.append("")
        for r, b in sorted(merged.items(), key=lambda x: -x[1]["ts"]):
            pr = prs.get(b["short"])
            link = branch_link(b["short"], slug, href=pr["url"] if pr else None)
            out.append(f"- {link} — last activity {b['when']} ({author_cell(b)})")
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


ISSUE_TITLE = "Current Activity"


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
    # Send the title too, so renaming ISSUE_TITLE renames the existing issue in
    # place on the next run (the issue is found by ISSUE_MARKER, not its title).
    res = api("PATCH", f"/repos/{slug}/issues/{number}", token,
              {"title": ISSUE_TITLE, "body": body})
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

    prs = {}
    if token:
        prs = fetch_prs(slug, token)

    # Only branches with an open PR appear anywhere in the report — and only they
    # are weighed when marking shared-file overlaps and conflicts — so drop the
    # rest before the conflict analysis and enrichment below.
    branches = {r: b for r, b in branches.items() if b["short"] in prs}
    conf = pairwise_conflicts(branches)

    # Resolve each branch's author GitHub handle: the commits API (accurate) when
    # a token is available, else parse a noreply commit email. With the handle,
    # look up the person's real name from their GitHub profile for display.
    for b in branches.values():
        b["login"] = (commit_login(slug, b["sha"], token) if token else None) \
            or login_from_email(b["email"])
        b["realname"] = user_realname(b["login"], token)

    body = render(branches, conf, prs, have_token=bool(token), slug=slug)

    if args.update_issue:
        if not token:
            sys.stderr.write("--update-issue needs GITHUB_TOKEN.\n")
            raise SystemExit(1)
        update_issue(slug, token, find_issue(slug, token, args.issue), body)
    else:
        print(body)


if __name__ == "__main__":
    main()
