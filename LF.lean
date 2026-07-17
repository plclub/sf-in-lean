import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save

import LF.Basics
import LF.Induction
import LF.UsingLean
import LF.Lists
-- NB: bare (not-yet-versified) chapters must NOT be imported here once their
-- Verso version is included below — both declare the same names.  They are
-- built by `make check-bare-lean-chapters` instead.
-- Add `import LF.XXXVerso` here for each generated chapter included below.
import LF.Poly
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
{include LF.Induction}
{include LF.UsingLean}
{include LF.Lists}
{include LF.Poly}
{include LF.TacticsVerso}
{include LF.LogicVerso}
