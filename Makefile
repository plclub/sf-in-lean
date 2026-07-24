# Makefile for sf-in-lean
#
# Each volume is built in three symmetric variants:
#   student    full prose, solutions elided   → _out/<vol>/student/{html-multi,lean}
#   solutions  full prose, solutions shown    → _out/<vol>/solutions/{html-multi,lean}
#   terse      lecture prose, solutions elided → _out/<vol>/terse/{html-multi,lean}
#
# To add a new volume (e.g., plf), define its targets with:
#   $(eval $(call VOLUME_template,plf))
# and add it to the `all` target below.

default: all

# ── Volume target template ────────────────────────────────────────────────────
# Usage: $(eval $(call VOLUME_template,slug))
#   slug   lowercase short name used in make targets and CLI args, e.g. lf
#          The single `sfl` executable is called as: lake exe sfl <slug> <mode>
define VOLUME_template

.PHONY: $(1) $(1)-build $(1)-student $(1)-solutions $(1)-terse

# Build the sfl executable (shared across all volumes) before running any
# variant.  Lake detects nothing changed on subsequent calls and skips quickly.
$(1)-build: ensure-build-symlink
	lake build sfl

$(1)-student: $(1)-build
	lake exe sfl $(1) student

$(1)-solutions: $(1)-build
	lake exe sfl $(1) solutions

$(1)-terse: $(1)-build
	lake exe sfl $(1) terse

$(1): $(1)-student $(1)-solutions $(1)-terse

endef

# ── Volume definitions ────────────────────────────────────────────────────────

$(eval $(call VOLUME_template,lf))
$(eval $(call VOLUME_template,hl))
$(eval $(call VOLUME_template,ts))

# ── Top-level targets ─────────────────────────────────────────────────────────

.PHONY: all serve clean ensure-build-symlink

all: verso lf hl ts check-bare-lean-chapters check-verso-chapters

# In this devcontainer /workspaces/l is a slow host bind mount, so the Lake
# build cache is relocated to the container-native fs and `.lake/build` is a
# symlink to it (see scripts/relocate-lake-build.sh).  `lake clean` deletes that
# symlink and Lake would otherwise recreate a real (slow) dir, so every target
# that invokes `lake` first re-establishes the symlink.  The script is idempotent
# and near-instant when the symlink is already correct.  Outside a container
# (e.g. `make` on the macOS host) it is a no-op.
ensure-build-symlink:
	@scripts/relocate-lake-build.sh

# Temporary:
# Build bare .lean chapters that compile but are not yet fully versified.
# Remove a module from this list only when it is broken (then fix it), or
# when it has been incorporated into the book via a *Verso.lean include.
.PHONY: check-lean
check-bare-lean-chapters: ensure-build-symlink
	lake build LF.IndProp

# Temporary:
# Build the generated HL/TS Verso chapters that aren't in a book yet, so the
# to_verso round-trip stays compilable.  `verso` (a prerequisite) regenerates
# the sources first.  Drop a module here once it's `{include}`d in its book.
.PHONY: check-verso-chapters
check-verso-chapters: verso ensure-build-symlink
	@if [ -n "$(HL_VERSO_MODULES)" ]; then lake build $(HL_VERSO_MODULES); else echo "no generated Verso chapters to build"; fi

serve: all
	python3 -m http.server 8000 -d _out/

clean:
	lake clean
	rm -rf _out/
	@scripts/relocate-lake-build.sh

# ── Generating Verso chapters from bare Lean (temporary!) ─────────
# Chapters that are not yet authored directly in Verso are generated from their
# code-forward `.lean` source by scripts/to_verso.py:
#     LF/Foo.lean  (bare Lean)  -->  LF/FooVerso.lean  (Verso, .gitignored)
#
# `make verso` (re)generates a LF/XXXVerso.lean for every chapter below.  To put
# a chapter in the book, add its `import`/`{include}` lines to LF.lean by hand
# once it compiles (a freshly generated chapter usually won't build yet:
# cross-chapter `import`s become code blocks, titles need fixing, etc.).

# This will all be ripped out once all chapters are versified.

LF_CHAPTERS :=

LF_VERSO_FILES := $(addprefix LF/,$(addsuffix Verso.lean,$(LF_CHAPTERS)))

# Imp is now versified directly in HL/Imp.lean and {include}d in HL.lean, so it
# is no longer generated here.  Add future not-yet-versified HL chapters below.
HL_CHAPTERS :=

HL_VERSO_FILES := $(addprefix HL/,$(addsuffix Verso.lean,$(HL_CHAPTERS)))

HL_VERSO_MODULES := $(addprefix HL.,$(addsuffix Verso,$(HL_CHAPTERS)))

.PHONY: verso
verso: $(LF_VERSO_FILES) $(HL_VERSO_FILES)

# Regenerate the Verso sources before building the book.
lf-build: verso

LF/%Verso.lean: LF/%.lean scripts/to_verso.py
	python3 scripts/to_verso.py $< $@

HL/%Verso.lean: HL/%.lean scripts/to_verso.py
	python3 scripts/to_verso.py $< $@

# ── Draft solutions for not-yet-versified chapters (temporary!) ───────────────
# Emits solutions .lean for the generated LF/<Ch>Verso.lean chapters listed in
# LFDraft.lean (currently the ones that compile), into
#   _out/lf-draft/solutions/lean/LF/<Ch>.lean
# for diffing against the bare LF/<Ch>.lean sources for completeness.  Add a
# chapter to LFDraft.lean once its Verso source builds.
.PHONY: lf-draft-solutions
lf-draft-solutions: verso ensure-build-symlink
	lake exe sfl-draft solutions
