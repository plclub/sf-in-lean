import VersoManual
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Exercise
import SFLMeta.Details
import Std.Data.HashMap
import SubVerso.Highlighting

open Lean Elab
open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Std (HashMap)
open SubVerso.Highlighting
open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes)

namespace SFLMeta

block_extension Block.devcomment where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

/-- Shared expander for noop annotation directives.  The directive body is
dropped at elaboration (`#[]`), so the block renders nothing and never reaches
the generated outputs — the original text survives only in the Verso source.
Both `:::dev` and `:::instructor` use this; they differ only in their block
name, so a later build can treat instructor notes differently. -/
def noopDirectiveFor (blockName : Name) : DirectiveExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.other $(mkIdent blockName) #[])

/-- A `:::dev` directive is a noop for author/developer comments. -/
@[directive]
def dev : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.devcomment args contents

/-- Shared expander for noop annotation *code blocks*.  Unlike the `:::`
directives above, a code block receives its body as a raw string that Verso
never parses as markdown, so arbitrary author prose (`:::`, `*`, `#`, `[…]`,
backticks) can't derail the parser and no inner verbatim fence is needed.  The
body is discarded at elaboration, so nothing reaches the generated outputs. -/
def noopCodeBlockFor (blockName : Name) : CodeBlockExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.other $(mkIdent blockName) #[])

/-- A ` ```dev ` code block: the raw-body form of `:::dev` for author/developer
comments.  Registered under the `dev` name (shared with the directive, which
lives in a separate expander table) so the fence reads ` ```dev `.  Prefer this
over the directive so `to_verso` needn't wrap the body in an inner code fence. -/
@[code_block dev]
def devBlock : CodeBlockExpanderOf Unit
  | args, str => noopCodeBlockFor ``Block.devcomment args str
