#!/usr/bin/env bash
# Claude-generated helper.
#
# Move the Lake build cache off the slow host bind mount onto the container's
# native filesystem.  In this devcontainer /workspaces/l is a `fakeowner` FUSE
# bind mount from the macOS host (~12x slower for the many small stat/read/write
# calls Lake makes); /home/vscode is on the container-native overlay/ext4.
# Relocating `.lake/build` there and symlinking it back cuts build-time I/O
# without changing anything Lake sees.
#
# Idempotent: safe to re-run after `lake clean`, a container restart, or a
# rebuild.  For durability across full container *rebuilds*, also add the named
# volume described in the project README / devcontainer.json (see the block that
# mounts a volume at $CACHE); this script then just ensures the symlink exists.
#
# Container-only: relocating makes sense (and $CACHE is creatable) only inside
# the devcontainer/CI container.  Outside one — e.g. `make` on the macOS host —
# this is a no-op so builds just use a plain .lake/build.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
CACHE="${SFL_LAKE_BUILD_DIR:-/home/vscode/.cache/sfl-lake-build}"
BUILD="$REPO/.lake/build"

if [ ! -e /.dockerenv ] && [ ! -d /run/.containerenv ] && [ -z "${SFL_LAKE_BUILD_DIR:-}" ]; then
  # A symlink left behind by a container run dangles on the host; drop it so
  # Lake can create a real .lake/build (the container run re-relocates later).
  if [ -L "$BUILD" ] && [ ! -e "$BUILD" ]; then
    rm -f "$BUILD"
    echo "removed dangling container symlink at $BUILD"
  fi
  echo "skip: not running in a container; leaving .lake/build in place"
  exit 0
fi

mkdir -p "$CACHE" "$REPO/.lake"

# Already a symlink to the cache → nothing to do.
if [ -L "$BUILD" ] && [ "$(readlink "$BUILD")" = "$CACHE" ]; then
  echo "ok: $BUILD -> $CACHE (already relocated)"
  exit 0
fi

# A real dir left by Lake (fresh checkout, `lake clean`, or rebuild without the
# volume): move its contents into the cache, then replace it with the symlink.
if [ -d "$BUILD" ] && [ ! -L "$BUILD" ]; then
  echo "moving existing $BUILD contents into $CACHE ..."
  cp -a "$BUILD/." "$CACHE/" 2>/dev/null || true
  rm -rf "$BUILD"
fi

# Dangling symlink (cache target vanished on rebuild) or nothing there yet.
[ -L "$BUILD" ] && rm -f "$BUILD"

ln -s "$CACHE" "$BUILD"
echo "ok: $BUILD -> $CACHE"
