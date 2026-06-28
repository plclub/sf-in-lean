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
$(1)-build:
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

.PHONY: all serve clean

all: verso lf hl ts

serve: all
	python3 -m http.server 8000 -d _out/

clean:
	lake clean
	rm -rf _out/

autograder:
	lake build autograder

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

LF_CHAPTERS := Induction UsingLean Lists Poly Tactics Logic IndProp IndPropRegexp Maps

LF_VERSO_FILES := $(addprefix LF/,$(addsuffix Verso.lean,$(LF_CHAPTERS)))

.PHONY: verso
verso: $(LF_VERSO_FILES)

# Regenerate the Verso sources before building the book.
lf-build: verso

LF/%Verso.lean: LF/%.lean scripts/to_verso.py
	python3 scripts/to_verso.py $< $@
