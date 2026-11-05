#!/bin/sh
# Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
# Mostly AI-generated; see CONTRIBUTING.md, "AI policy".
#
# Install this unpublished extension for local testing by linking this folder
# into ~/.vscode/extensions (VS Code loads any folder there named
# <publisher>.<name>-<version> that holds a package.json, symlink or not).
# Afterwards run "Developer: Reload Window" in each open VS Code window.
#
#   sh vscode-extension/install-dev.sh            # link
#   sh vscode-extension/install-dev.sh --remove   # unlink
set -e
here=$(cd "$(dirname "$0")" && pwd -P)
field() { sed -n "s/^ *\"$1\": *\"\([^\"]*\)\".*/\1/p" "$here/package.json" | head -1; }
link="$HOME/.vscode/extensions/$(field publisher).$(field name)-$(field version)"
if [ "$1" = --remove ]; then
  if [ -L "$link" ]; then rm "$link"; echo "removed  $link"; else echo "no link at $link"; fi
  exit 0
fi
if [ -e "$link" ] && [ ! -L "$link" ]; then
  echo "error: $link exists and is not a symlink; remove it by hand first" >&2
  exit 1
fi
mkdir -p "$HOME/.vscode/extensions"
ln -sfn "$here" "$link"
echo "linked   $link -> $here"
echo "Now run \"Developer: Reload Window\" in each open VS Code window."
