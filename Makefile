# Makefile for sf-in-lean
#
# To add a new volume (e.g., PLF), define its targets with:
#   $(eval $(call VOLUME_template,plf,PLF,plf_verso,plf_verso_terse))
# and add it to the `all` target below.

default: all

# ── Volume target template ────────────────────────────────────────────────────
# Usage: $(eval $(call VOLUME_template, slug, LibName, full-exe, terse-exe))
#   slug      short name used in make targets, e.g. lf
#   LibName   Lake library name, e.g. LF
#   full-exe  lake executable for full HTML + teacher/student .lean
#   terse-exe lake executable for terse HTML + terse .lean
define VOLUME_template

.PHONY: $(1) $(1)-full $(1)-terse $(1)-build

$(1)-build:
	lake build $(2)

$(1)-full: $(1)-build
	lake exe $(3)

$(1)-terse: $(1)-build
	lake exe $(4)

$(1): $(1)-full $(1)-terse

endef

# ── Volume definitions ────────────────────────────────────────────────────────

$(eval $(call VOLUME_template,lf,LF,lf_verso,lf_verso_terse))

# ── Top-level targets ─────────────────────────────────────────────────────────

.PHONY: all serve clean

all: verso lf

serve: all
	python3 -m http.server 8000 -d _out/

clean:
	lake clean
	rm -rf _out/

# Temporary
verso: LF/BasicsVerso.lean

LF/BasicsVerso.lean: LF/Basics.lean scripts/to_verso.py
	 python3 scripts/to_verso.py $< $@
