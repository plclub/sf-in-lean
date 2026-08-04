#!/usr/bin/env python3
# This file is maintained by Claude (AI-generated).
"""
branch_watch.py  —  Report which files are being changed on which branches.

Walks every remote branch, finds the commits not yet in `main`, and builds a
picture of who is touching what:

  * a per-PR table with Ready-to-merge PRs grouped first (then most recently
    active) — five columns: the branch (linked to its PR) over its author and
    last-activity time on a second line in small type; a Status cell of glyph
    badges (✅ ready, 👍 approved with open threads, 🔴 changes requested,
    💬N open threads, ✏️ draft, ⏳ queued / 🚧 auto-merge held, 🔗 fixes issue,
    ⚠️ main = no longer merges cleanly against `main`); an Overlaps cell naming
    which *other* PR branches it shares files with (plain = clean co-edit,
    ⚠️ = a real conflict from an in-memory merge not a filename guess, ⊃/⊂ = one
    branch's commits contain the other's), a Files count (expander), and any
    `#Note: …` lines reviewers left on the PR.  Every icon carries a hover
    tooltip (via `<abbr>`) and is glued to its text with a non-breaking space,
    and a legend below the table spells the glyphs out too.  Only branches with
    an open PR appear in the table, and only they are weighed when marking its
    overlaps and conflicts;
  * a "Branches without PRs:" line just below the table — a compact list of
    every active branch *without* a PR: name (linked to its GitHub page), its author
    (same style as the table), how long since it was created and last active,
    and a ⚠️ when it would conflict with any open PR;
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
        # Rough branch "age": the date of its oldest commit not yet in main —
        # i.e. when this line of work first diverged. A branch with nothing
        # ahead has no divergent commit, so fall back to the tip date.
        if ahead:
            first_sha = git("rev-list", f"{main}..{ref}").splitlines()[-1]
            created = git("log", "-1", "--format=%cr", first_sha)
            if created.endswith(" ago"):
                created = created[:-4]
        else:
            created = when
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
            "created": created,
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
    """Author identity for a branch: the person's name (their GitHub real name
    when known, else the commit-author name) shown as the visible text, linked
    to their profile, with the `@handle` (and the commit alias when it differs
    from the real name) tucked into the link's hover `title` — e.g.
    `[Yipeng Liu](… "@berberman, Potato Hatsue")`. Without a resolved handle
    (no token, or unmatched) we fall back to the bare commit-author name."""
    author = b["author"]
    login = b.get("login")
    real = b.get("realname")
    if login:
        visible = real if (real and real != author) else author
        alias = f", {author}" if real and real != author else ""
        title = f"@{login}{alias}".replace('"', "'")
        return f'[{visible}](https://github.com/{login} "{title}")'
    return author


def tip(glyph, title):
    """A glyph carrying a hover tooltip.  GitHub keeps the `title` attribute on
    `<abbr>`, so the icon renders with an explanatory pop-up (and degrades to a
    bare glyph on any renderer that drops it — the table legend still spells
    every icon out).  Titles are plain text, so no backticks/markdown."""
    return f'<abbr title="{title}">{glyph}</abbr>'


# The "draft" badge is GitHub's transparent-background pencil emoji served as an
# <img> rather than the busier 📝 memo glyph: an image can be sized (a plain
# emoji can't in Markdown), so it sits a touch larger, and `title` gives it the
# same hover tooltip as the <abbr>-wrapped glyphs.  `alt` degrades gracefully.
DRAFT_BADGE = ('<img src="https://github.githubassets.com/images/icons/emoji/'
               'unicode/270f.png" width="20" alt="Draft" title="Draft">')


def status_badges(pr):
    """Review / merge readiness of an open PR as compact glyph badges (each
    carrying a hover tooltip, and spelled out in the table legend).  Badges are
    space-joined and each icon is glued to its own text with a non-breaking
    space, so an icon never wraps away from the word it labels.

    * 📝 draft.
    * 🔴 changes requested · ✅ ready to merge (approved, nothing unresolved) ·
      👍 approved but with open threads.
    * 💬N — N review threads still open.
    * ⏳ in the merge queue · 🚧 auto-merge enabled but held (a failing check,
      missing approval, or conflict is stalling it).
    * 🔗 #N — issues the PR closes (via a fixes/closes/resolves keyword), linked."""
    badges = []
    if pr["draft"]:
        badges.append(DRAFT_BADGE)
    else:
        dec = pr["review_decision"]
        if dec == "CHANGES_REQUESTED":
            badges.append(tip("🔴", "Changes requested"))
        elif dec != "REVIEW_REQUIRED":  # APPROVED, or None (no required review — rare here)
            badges.append(tip("✅", "Ready to merge — approved, nothing unresolved")
                          if pr["unresolved"] == 0
                          else tip("👍", "Approved, but with open review threads"))
    if pr["unresolved"]:
        n = pr["unresolved"]
        badges.append(tip(f"💬{n}", f"{n} open review thread{'' if n == 1 else 's'}"))
    if pr["auto_merge"]:
        badges.append(tip("⏳", "In the merge queue") if pr["in_queue"]
                      else tip("🚧", "Auto-merge enabled but held"))
    if pr["closes"]:
        links = ", ".join(f"[#{i['num']}]({i['url']})" for i in pr["closes"])
        badges.append(tip("🔗", "Issues this PR closes") + "&nbsp;" + links)
    return " ".join(badges)


def pr_ready(pr, clean_to_main):
    """A PR that could merge right now: not a draft, a review actually recorded
    with no changes requested, no unresolved threads, and still clean against
    `main`.  Drives the "Ready to merge" grouping at the top of the table."""
    return bool(pr and not pr["draft"] and pr["unresolved"] == 0
                and pr["review_decision"] not in ("CHANGES_REQUESTED", "REVIEW_REQUIRED")
                and clean_to_main)


def pr_cell(short, prs):
    """The PR link for a branch, followed by its review/merge status badges (the
    two were merged into one column)."""
    pr = prs.get(short)
    if not pr:
        return "No PR"
    badges = status_badges(pr)
    return f"[#{pr['num']}]({pr['url']})" + (f" {badges}" if badges else "")


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
    """The `#Note: …` reviewers left on a PR, separated by a middot and left to
    wrap — or an empty cell when there are none (or no PR).  A middot rather
    than a `<br>` per note: forced line breaks buy no vertical space (the cell's
    block line-height fixes the leading regardless), so flowing them onto shared
    lines keeps the row shorter."""
    notes = pr.get("notes") if pr else None
    if not notes:
        return ""
    return " · ".join(notes)


def files_cell(files):
    """A <details> expander listing files, valid inside a Markdown table cell.
    The names flow middot-separated (not one `<br>` per line) so the expanded
    list stays compact."""
    n = len(files)
    if n == 0:
        return "0"
    inner = " · ".join(f"`{f}`" for f in sorted(files))
    return f"<details><summary>{n}</summary>{inner}</details>"


def render(branches, conf, prs, have_token, slug):
    # The PR table (and the file/overlap analysis beneath it) covers active
    # branches that have an open PR; the "Merged / inactive" section covers PR
    # branches with nothing ahead of main.  Active branches *without* a PR are
    # summarised in the compact "Branches without PRs:" paragraph instead.
    active = {r: b for r, b in branches.items()
              if b["ahead"] > 0 and b["short"] in prs}
    non_pr = {r: b for r, b in branches.items()
              if b["ahead"] > 0 and b["short"] not in prs}
    merged = {r: b for r, b in branches.items()
              if b["ahead"] == 0 and b["short"] in prs}

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

    # ---- per-PR table (Ready-to-merge grouped first, else most recent first) ----
    # No sub-heading here: the table sits directly under "## Current Activity".
    # Five columns: the old "Author" and "Activity" columns are folded into the
    # branch cell's small-type subline, and the wordy Status/overlap text is
    # replaced by glyph badges (spelled out in the legend below the table).
    out.append("| Branch / Author | Status | Overlaps | Files | `#Note`s |")
    out.append("|---|---|---|--:|---|")
    ready_rows, other_rows = [], []
    for r, b in sorted(active.items(), key=lambda x: (-x[1]["ts"], x[1]["short"])):
        overlaps = [o for o in active if o != r and active[o]["files"] & b["files"]]
        # A stacked branch — one that fully contains the other's commits — is the
        # same line of work, not a concurrent co-edit (and can never conflict, so
        # never a ⚠️).  Pull those out of the overlap list and label them
        # explicitly, relative to this row's branch: `⊃ o` when r contains o,
        # `⊂ o` when r itself sits inside o.
        contains_o = sorted(o for o in overlaps if contains(r, o))
        contained_by = sorted(o for o in overlaps if contains(o, r))
        rest = [o for o in overlaps if o not in contains_o and o not in contained_by]
        # Among the genuinely concurrent overlaps that remain, group a superseded
        # one under the branch that already contains it, so one line of work
        # carried across several branches reads as a single overlap with a single
        # ⚠️, not several.  `A ⊂ B` names the superseded branches A first, then
        # the container B whose commits already include them; the ⚠️ (real merge
        # conflict) is shown once, on the container.
        # Each overlap icon carries a tooltip and is glued to its branch link
        # with a non-breaking space, so the symbol never wraps away from the
        # name it qualifies.
        warn = tip("⚠️", "Real merge conflict")
        sup = tip("⊃", "Contains that branch's commits")
        sub = tip("⊂", "Contained in that branch")
        heads = sorted(independent_branches(rest))
        pieces = []
        for h in heads:
            subs = sorted(o for o in rest if o != h and contains(h, o))
            prefix = f"{warn}&nbsp;" if h in conf[r] else ""
            h_link = branch_link(active[h]["short"], slug)
            if subs:
                sub_links = ", ".join(
                    branch_link(active[o]["short"], slug) for o in subs)
                piece = f"{prefix}{sub_links}&nbsp;{sub}&nbsp;{h_link}"
            else:
                piece = prefix + h_link
            pieces.append(piece)
        pieces += [f"{sup}&nbsp;" + branch_link(active[o]["short"], slug)
                   for o in contains_o]
        pieces += [f"{sub}&nbsp;" + branch_link(active[o]["short"], slug)
                   for o in contained_by]
        ov = ", ".join(pieces)
        pr = prs.get(b["short"])
        # First cell: the branch (linked to its PR) with its author and
        # last-activity time on a second line in small type — three former
        # columns folded into one.  A wider branch label keeps it readable.
        branch = branch_link(b["short"], slug, maxlen=40,
                             href=pr["url"] if pr else None)
        first = f"{branch}<br><sub>{author_cell(b)} · {b['when']} ago</sub>"
        # The old "→ main" column is folded into the Status cell: flag a branch
        # that no longer merges cleanly right there, as a ⚠️ main badge.
        status = pr_cell(b["short"], prs)
        if not b["clean_to_main"]:
            status += " " + tip("⚠️&nbsp;main", "No longer merges cleanly with main")
        # `#Note`s flow middot-separated (see notes_cell); `<sub>` is used purely
        # for smaller glyphs — the block line-height fixes the leading regardless.
        notes = notes_cell(pr)
        notes = f"<sub>{notes}</sub>" if notes else ""
        row = (f"| {first} | {status} | {ov} | {files_cell(b['files'])} | "
               f"{notes} |")
        (ready_rows if pr_ready(pr, b["clean_to_main"]) else other_rows).append(row)
    # Ready-to-merge PRs float to the top under a labelled divider so the eye
    # lands on what's actionable; when every row is in one group, skip the labels.
    if ready_rows and other_rows:
        out.append("| **✅ Ready to merge** | | | | |")
        out += ready_rows
        out.append("| **🛠️ In progress** | | | | |")
        out += other_rows
    else:
        out += ready_rows + other_rows
    if active:
        out.append("")
        out.append(
            "<sub>**Status** ✅&nbsp;ready · 👍&nbsp;approved, threads open · "
            "🔴&nbsp;changes requested · 💬&nbsp;open threads · "
            f"{DRAFT_BADGE}&nbsp;draft · ⏳&nbsp;queued · 🚧&nbsp;auto-merge "
            "held · 🔗&nbsp;fixes issue · ⚠️&nbsp;main conflicts with `main`. "
            "&nbsp; **Overlaps** plain = clean co-edit · ⚠️&nbsp;real conflict "
            "· ⊃&nbsp;contains · ⊂&nbsp;contained in.</sub>")
    out.append("")

    # ---- non-PR branches: one compact "Branches without PRs:" line ----
    if non_pr:
        items, any_clash = [], False
        for r, b in sorted(non_pr.items(), key=lambda x: -x[1]["ts"]):
            # ⚠️ if this branch would actually conflict with any open PR branch.
            clash = any(o in active for o in conf[r])
            any_clash = any_clash or clash
            items.append(
                f"{branch_link(b['short'], slug)} {author_cell(b)} "
                f"(created {b['created']}, active {b['when']}"
                f"){' ⚠️' if clash else ''}"
            )
        legend = (" &nbsp;_(⚠️ = conflicts with an open PR)_" if any_clash else "")
        # The whole paragraph is set in small type with `<sub>` (smaller than
        # `<small>` on GitHub, and matching the table's small cells).  Wrapped
        # lines still sit at the surrounding block line-height — that leading is
        # fixed by the block strut and can't be tightened by an inline tag.
        out.append("<sub>**Branches without PRs:** " + ", ".join(items) + "." + legend + "</sub>")
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

    # Conflicts are computed over *all* active branches: PR branches populate the
    # main table's overlap column, and the non-PR "Branches without PRs:"
    # paragraph needs to know whether each such branch clashes with any open PR.
    conf = pairwise_conflicts(branches)

    # Resolve author identity for every branch shown with an author: the PR
    # table, the "Branches without PRs:" line, and the merged/inactive list — all
    # but the non-PR branches with nothing ahead (which appear nowhere).  The
    # commits API (accurate) gives the GitHub handle when a token is available,
    # else a noreply commit email is parsed; with the handle, the person's real
    # name is looked up from their GitHub profile for display.
    for b in branches.values():
        if b["short"] not in prs and b["ahead"] == 0:
            continue
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
