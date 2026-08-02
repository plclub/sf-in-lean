import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save

import LF.Basics
import LF.Induction
import LF.UsingLean
import LF.Lists
import LF.Poly
import LF.Tactics
import LF.Logic
import LF.IndProp
import LF.Automation
import LF.Typeclasses
import LF.Notations

import VersoManual

open Verso Genre Manual

-- To add a chapter: `import LF.XXX` above and a matching `{include LF.XXX}`
-- line below in book order.  (The `#doc` body has no comment syntax, so don't
-- put comments after the includes.)
#doc (Manual) "Logical Foundations" =>
{include LF.Basics}
{include LF.Induction}
{include LF.UsingLean}
{include LF.Lists}
{include LF.Poly}
{include LF.Tactics}
{include LF.Logic}
{include LF.IndProp}
{include LF.Automation}
{include LF.Typeclasses}
{include LF.Notations}
