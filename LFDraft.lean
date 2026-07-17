-- AI-generated (Claude), temporary scaffolding.
--
-- A "draft" LF book that `{include}`s generated `LF/<Ch>Verso.lean` chapters
-- which compile but are not yet part of the real book (LF.lean).  Its only
-- purpose is to let `sfl-draft` emit solutions `.lean` for those chapters
-- (into `_out/lf-draft/…`, never clobbering the real `lf` output) so the
-- round-tripped result can be diffed against the bare `LF/<Ch>.lean` sources
-- for completeness.
--
-- Maintenance: add a chapter's `import` + `{include}` line below once its
-- `LF/<Ch>Verso.lean` builds (see `make verso`); remove it once the chapter
-- graduates into LF.lean.  Keep only currently-building chapters here, or
-- `sfl-draft` won't build.
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save

-- NB LF.MapsVerso builds standalone but cannot join the draft yet: it
-- redefines `PartialMap.update` (etc.) already defined by LF.Lists'
-- partial-maps preview section, and Verso imports share one environment.

import VersoManual

open Verso Genre Manual

#doc (Manual) "Logical Foundations (draft)" =>
