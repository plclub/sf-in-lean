import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save

import LF.Basics
-- Add `import LF.XXXVerso` here for each generated chapter included below.
import LF.InductionVerso
import LF.UsingLeanVerso
import LF.ListsVerso
import LF.PolyVerso
import LF.TacticsVerso
import LF.LogicVerso

import VersoManual

open Verso Genre Manual

-- To add a generated chapter to the book: run `make verso` to (re)generate the
-- LF/XXXVerso.lean sources, add `import LF.XXXVerso` above, and add a matching
-- `{include LF.XXXVerso}` line below in book order.  (The `#doc` body has no
-- comment syntax, so don't put comments after the includes.)
#doc (Manual) "Logical Foundations" =>
{include LF.Basics}
{include LF.InductionVerso}
{include LF.UsingLeanVerso}
{include LF.ListsVerso}
{include LF.PolyVerso}
{include LF.TacticsVerso}
{include LF.LogicVerso}
