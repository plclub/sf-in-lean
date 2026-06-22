# Makefile for sf-in-lean
#
# Each volume is built in three symmetric variants:
#   student    full prose, solutions elided   → _out/student/{html-multi,lean}
#   solutions  full prose, solutions shown    → _out/solutions/{html-multi,lean}
#   terse      lecture prose, solutions elided → _out/terse/{html-multi,lean}
#
# To add a new volume (e.g., PLF), define its targets with:
#   $(eval $(call VOLUME_template,plf,PLF))
# and add it to the `all` target below.  (Volume executables are expected to
# be named <slug>_student, <slug>_solutions, <slug>_terse in lakefile.toml.)

default: all

# ── Volume target template ────────────────────────────────────────────────────
# Usage: $(eval $(call VOLUME_template, slug, LibName))
#   slug      short name used in make targets and exe names, e.g. lf
#   LibName   Lake library name, e.g. LF
define VOLUME_template

.PHONY: $(1) $(1)-build $(1)-student $(1)-solutions $(1)-terse

$(1)-build:
	lake build $(2)

$(1)-student: $(1)-build
	lake exe $(1)_student

$(1)-solutions: $(1)-build
	lake exe $(1)_solutions

$(1)-terse: $(1)-build
	lake exe $(1)_terse

$(1): $(1)-student $(1)-solutions $(1)-terse

endef

# ── Volume definitions ────────────────────────────────────────────────────────

$(eval $(call VOLUME_template,lf,LF))

# ── Top-level targets ─────────────────────────────────────────────────────────

.PHONY: all serve clean

all: verso lf

serve: all
	python3 -m http.server 8000 -d _out/

clean:
	lake clean
	rm -rf _out/

# ── Generating Verso chapters from bare Lean ──────────────────────────────────
# Chapters that are not yet authored directly in Verso are generated from their
# code-forward `.lean` source by scripts/to_verso.py:
#     LF/Foo.lean  (bare Lean)  -->  LF/FooVerso.lean  (Verso, .gitignored)
# Basics is authored directly in Verso, so it is not listed here.
#
# `make verso` (re)generates a LF/XXXVerso.lean for every chapter below.  To put
# a chapter in the book, add its `import`/`{include}` lines to LF.lean by hand
# once it compiles (a freshly generated chapter usually won't build yet:
# cross-chapter `import`s become code blocks, titles need fixing, etc.).
LF_CHAPTERS := Induction UsingLean Lists Poly Tactics Logic IndProp IndPropRegexp Maps

LF_VERSO_FILES := $(addprefix LF/,$(addsuffix Verso.lean,$(LF_CHAPTERS)))

.PHONY: verso
verso: $(LF_VERSO_FILES)

# Regenerate the Verso sources before building the book.
lf-build: verso

LF/%Verso.lean: LF/%.lean scripts/to_verso.py
	python3 scripts/to_verso.py $< $@
