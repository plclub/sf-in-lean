# Makefile for sf-in-lean
#
# Each volume is built in three symmetric variants:
#   student    full prose, solutions elided   → _out/<vol>/student/{html,lean}
#   solutions  full prose, solutions shown    → _out/<vol>/solutions/{html,lean}
#   terse      lecture prose, solutions elided → _out/<vol>/terse/{html,lean}
#   grading    full prose, solutions show (with grading attributes) → _out/<vol>/grading/{html,lean}
#
# To add a new volume (e.g., plf), define its targets with:
#   $(eval $(call VOLUME_template,plf))
# and add it to the `all` target below.

default: all

# ── Volume target template ────────────────────────────────────────────────────
# Usage: $(eval $(call VOLUME_template,slug))
#   slug   lowercase short name used in make targets and CLI args, e.g. lf
#          Each volume has its own executable, called as:
#          lake env .lake/build/bin/sfl-<slug> <mode>
define VOLUME_template

.PHONY: $(1) $(1)-student $(1)-solutions $(1)-terse $(1)-grading

$(1)-student: book-build
	lake env .lake/build/bin/sfl-$(1) student

$(1)-solutions: book-build
	lake env .lake/build/bin/sfl-$(1) solutions

$(1)-terse: book-build
	lake env .lake/build/bin/sfl-$(1) terse

$(1)-grading: book-build
	lake env .lake/build/bin/sfl-$(1) grading

$(1): $(1)-student $(1)-solutions $(1)-terse $(1)-grading

endef

# ── Volume definitions ────────────────────────────────────────────────────────

$(eval $(call VOLUME_template,lf))
$(eval $(call VOLUME_template,hl))
$(eval $(call VOLUME_template,ts))

# ── Top-level targets ─────────────────────────────────────────────────────────

.PHONY: all student solutions terse grading grading-tools grading-check-only grading-check serve clean ensure-build-symlink book-build style style-check style-checklist release

# Compile all volume executables once before any generator starts.  A single
# Lake frontend avoids races on the shared `.lake/build` directory.
book-build: ensure-build-symlink
	lake build sfl-lf sfl-hl sfl-ts

all: lf hl ts

# Build a single variant across every volume.
student: lf-student hl-student ts-student

solutions: lf-solutions hl-solutions ts-solutions

terse: lf-terse hl-terse ts-terse

grading: lf-grading hl-grading ts-grading

grading-tools:
	lake build lean4export comparatorautograder

# Check existing generated roots without generating books or building tools.
grading-check-only:
	python3 scripts/grading_check.py --volumes LF HL TS --variants student solutions --stats --no-make --no-build

# Local convenience target. Run these documented targets separately in CI.
grading-check:
	$(MAKE) all
	$(MAKE) grading-tools
	$(MAKE) grading-check-only

# Mechanical conformance checks for the style guides — STYLE-CODE.md and
# STYLE-WRITING.md (auto checks fail the run; assisted ones are advisory).
# `style-checklist` prints the audit checklist for the judgement-based
# conventions. See scripts/style_check.py.
style:
	python3 scripts/style_check.py

# Kept as the older name for `style`.
style-check: style

style-checklist:
	@python3 scripts/style_check.py --checklist

# In this devcontainer /workspaces/l is a slow host bind mount, so the Lake
# build cache is relocated to the container-native fs and `.lake/build` is a
# symlink to it (see scripts/relocate-lake-build.sh).  `lake clean` deletes that
# symlink and Lake would otherwise recreate a real (slow) dir, so every target
# that invokes `lake` first re-establishes the symlink.  The script is idempotent
# and near-instant when the symlink is already correct.  Outside a container
# (e.g. `make` on the macOS host) it is a no-op.
ensure-build-symlink:
	@scripts/relocate-lake-build.sh

serve: all
	python3 -m http.server 8000 -d _out/

# Package a local release (student html/ + lean/ per volume) for the course
# webpage. scripts/release_chapters.json controls everything: which volumes
# get released (an omitted volume is skipped) and, per volume, which chapters
# are included. Pass extra flags via ARGS to override, e.g.:
#   make release ARGS="--keep-lake"
release:
	python3 scripts/package_release.py $(ARGS)

clean:
	lake clean
	rm -rf _out/
	@scripts/relocate-lake-build.sh
