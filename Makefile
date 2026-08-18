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
#          Each volume has its own executable, called as: lake exe sfl-<slug> <mode>
define VOLUME_template

.PHONY: $(1) $(1)-build $(1)-student $(1)-solutions $(1)-terse

# Build this volume's executable before running any variant.  Lake detects
# nothing changed on subsequent calls and skips quickly.
$(1)-build: ensure-build-symlink
	lake build sfl-$(1)

$(1)-student: $(1)-build
	lake exe sfl-$(1) student

$(1)-solutions: $(1)-build
	lake exe sfl-$(1) solutions

$(1)-terse: $(1)-build
	lake exe sfl-$(1) terse

$(1)-grading: $(1)-build
	lake exe sfl-$(1) grading

$(1): $(1)-student $(1)-solutions $(1)-terse $(1)-grading

endef

# ── Volume definitions ────────────────────────────────────────────────────────

$(eval $(call VOLUME_template,lf))
$(eval $(call VOLUME_template,hl))
$(eval $(call VOLUME_template,ts))

# ── Top-level targets ─────────────────────────────────────────────────────────

.PHONY: all student solutions terse grading serve clean ensure-build-symlink style style-check style-checklist

all: lf hl ts

# Build a single variant across every volume.
student: lf-student hl-student ts-student

solutions: lf-solutions hl-solutions ts-solutions

terse: lf-terse hl-terse ts-terse

grading: lf-grading hl-grading ts-grading

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

clean:
	lake clean
	rm -rf _out/
	@scripts/relocate-lake-build.sh
