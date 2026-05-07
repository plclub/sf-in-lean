"""
Shared helpers for the Lean formatting / extraction scripts.

Handles the common CLI concerns:
  * Expand arguments into a flat list of .lean files (accepts files and dirs).
  * Validate that at least one file was found.
  * Derive output paths into an explicit --out-dir, preserving filename stems.
  * Skip-with-warning when the output already exists.
"""

from __future__ import annotations

import os
import sys
from typing import Callable, Iterable, List, Optional, Tuple


def collect_lean_files(paths: Iterable[str]) -> Tuple[List[str], List[str]]:
    """
    Expand `paths` (files and/or directories) into (files, errors).

    - Files must have a `.lean` suffix; non-.lean files are reported as errors.
    - Directories are scanned (non-recursively) for `.lean` files. An empty
      directory yields an error.
    - Missing paths yield errors.
    """
    files: List[str] = []
    errors: List[str] = []
    for p in paths:
        if not os.path.exists(p):
            errors.append(f"path not found: {p}")
            continue
        if os.path.isdir(p):
            found = sorted(
                os.path.join(p, entry)
                for entry in os.listdir(p)
                if entry.endswith(".lean")
                and os.path.isfile(os.path.join(p, entry))
            )
            if not found:
                errors.append(f"no .lean files found in directory: {p}")
            files.extend(found)
            continue
        if os.path.isfile(p):
            if not p.endswith(".lean"):
                errors.append(f"not a .lean file: {p}")
                continue
            files.append(p)
            continue
        errors.append(f"unsupported path type: {p}")
    return files, errors


def ensure_out_dir(out_dir: str) -> Optional[str]:
    """Create out_dir if needed. Returns error message or None."""
    try:
        os.makedirs(out_dir, exist_ok=True)
    except OSError as e:
        return f"could not create output directory {out_dir!r}: {e}"
    return None


def output_path(
    input_path: str,
    out_dir: str,
    suffix: str,
    *,
    strip_infix: Optional[str] = None,
) -> str:
    """
    Given input `.../Basics.lean`, out_dir `out/`, suffix `formatted`,
    produce `out/Basics.formatted.lean`.

    If `strip_infix` is given and the stem ends with `.<strip_infix>`,
    that infix is removed before appending the suffix. This makes chained
    pipelines produce clean names (e.g. `Basics.formatted.lean` +
    strip_infix=`formatted`, suffix=`full` -> `Basics.full.lean`).
    """
    base = os.path.basename(input_path)
    stem, _ = os.path.splitext(base)
    if strip_infix and stem.endswith(f".{strip_infix}"):
        stem = stem[: -(len(strip_infix) + 1)]
    return os.path.join(out_dir, f"{stem}.{suffix}.lean")


def process_files(
    paths: List[str],
    out_dir: str,
    suffix: str,
    transform: Callable[[List[str]], List[str]],
    *,
    tool_name: str,
    strip_infix: Optional[str] = None,
    force: bool = False,
) -> int:
    """
    Drive the common flow: collect inputs, ensure out_dir, run `transform`
    on each file's lines, write to `<out_dir>/<stem>.<suffix>.lean`.
    Skip-with-warning if the output already exists. Returns a process
    exit code (0 on any successful work, 1 if no work was done at all).
    """
    if not paths:
        print(
            f"{tool_name}: error: no input files or directories given\n"
            f"  usage: {tool_name} --out-dir DIR FILE_OR_DIR [FILE_OR_DIR ...]",
            file=sys.stderr,
        )
        return 2

    files, errors = collect_lean_files(paths)
    for err in errors:
        print(f"{tool_name}: warning: {err}", file=sys.stderr)

    if not files:
        print(f"{tool_name}: error: no .lean files to process", file=sys.stderr)
        return 1

    dir_err = ensure_out_dir(out_dir)
    if dir_err:
        print(f"{tool_name}: error: {dir_err}", file=sys.stderr)
        return 1

    n_written = 0
    n_skipped = 0
    for in_path in files:
        out_path = output_path(in_path, out_dir, suffix, strip_infix=strip_infix)
        if os.path.exists(out_path) and not force:
            print(
                f"{tool_name}: warning: output already exists, skipping "
                f"(use --force to overwrite): {out_path}",
                file=sys.stderr,
            )
            n_skipped += 1
            continue
        try:
            with open(in_path, "r", encoding="utf-8") as f:
                data = f.read().splitlines()
        except OSError as e:
            print(f"{tool_name}: error reading {in_path}: {e}", file=sys.stderr)
            continue
        result = transform(data)
        try:
            with open(out_path, "w", encoding="utf-8") as f:
                f.write("\n".join(result))
                f.write("\n")
        except OSError as e:
            print(f"{tool_name}: error writing {out_path}: {e}", file=sys.stderr)
            continue
        print(f"{tool_name}: wrote {out_path}", file=sys.stderr)
        n_written += 1

    if n_written == 0 and n_skipped == 0:
        return 1
    return 0
