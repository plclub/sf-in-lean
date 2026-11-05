#!/bin/sh
# Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
# Mostly AI-generated; see CONTRIBUTING.md, "AI policy".
#
# Smoke-test the extension in a throwaway VS Code instance (its own user-data
# and extensions directories; other extensions disabled), so no open VS Code
# window is touched.
#
#   sh vscode-extension/test/vscode-smoke.sh <extracted-project> <vol> <Chapter> <descriptors.json>
#
# e.g. a copy of _out/lf/student/lean, lf, Basics, and the output of
# page-descriptors.js for _out/lf/student/html/Basics/index.html.
set -e
[ $# -eq 4 ] || { echo "usage: $0 <project> <vol> <Chapter> <descriptors.json>" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd -P)
code="${VSCODE_APP:-/Applications/Visual Studio Code.app}/Contents/MacOS/Code"
# The user-data path must be short: VS Code's IPC socket path is limited to 103 bytes.
tmp=$(mktemp -d /tmp/sfl.XXXX)
trap 'rm -rf "$tmp"' EXIT
out="$tmp/report.txt"
SFL_TEST_OUT="$out" SFL_TEST_VOL="$2" SFL_TEST_CHAPTER="$3" \
SFL_TEST_DESCRIPTORS="$(cd "$(dirname "$4")" && pwd -P)/$(basename "$4")" \
  env -u ELECTRON_RUN_AS_NODE "$code" \
  --user-data-dir "$tmp/u" --extensions-dir "$tmp/e" --disable-extensions \
  --extensionDevelopmentPath="$(dirname "$here")" \
  --extensionTestsPath="$here/vscode-test.js" \
  "$1" >/dev/null 2>&1 || true
if [ -f "$out" ]; then cat "$out"; grep -qx PASS "$out"; else echo "no report written" >&2; exit 1; fi
