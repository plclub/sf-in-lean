import VersoManual
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Exercise
import SFLMeta.Details
import Std.Data.HashMap
import SubVerso.Highlighting

open Lean Elab
open Verso
open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Std (HashMap)
open SubVerso.Highlighting
open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes)

namespace SFLMeta

/-- Author-facing configuration for `:::dev`.  Both fields are optional named
arguments: `:::dev`, `:::dev (author := "Benjamin Pierce (bcpierce00)")`,
`:::dev (urgency := SOONER)`, and
`:::dev (author := "Benjamin Pierce (bcpierce00)") (urgency := SOONER)` are
all valid. -/
structure DevConfig where
  /-- Who filed the note, conventionally a full name followed by a GitHub
  handle in parentheses: `"Benjamin Pierce (bcpierce00)"`. -/
  author : Option String
  /-- An urgency keyword, conventionally `SOONER`, `LATER`, `TODO`, or `TOFIX`. -/
  urgency : Option String
deriving Repr

section
variable [Monad m] [MonadError m]

/-- An argument value written either as a bare identifier or as a string
literal (`SOONER` or `"SOONER"`), yielding its text. -/
def ValDesc.identOrStr : ValDesc m String where
  description := doc!"an identifier or string literal"
  signature := CanMatch.Ident ∪ CanMatch.String
  get
    | .name x => Pure.pure x.getId.toString
    | .str s => Pure.pure s.getString
    | other => throwError "Expected identifier or string, got {toMessageData other}"

/-- Argument parser for `DevConfig`: optional named author and urgency. -/
def DevConfig.parse : ArgParse m DevConfig :=
  DevConfig.mk
    <$> ArgParse.named `author ValDesc.identOrStr true
    <*> ArgParse.named `urgency ValDesc.identOrStr true

instance : FromArgs DevConfig m := ⟨DevConfig.parse⟩

end

/-! `Block.devcomment` records its author/urgency metadata in `data` so that a
future dev-facing build can typeset notes in a standard way; the current
builds render nothing. -/
block_extension Block.devcomment (author : Option String) (urgency : Option String) where
  data := Json.arr #[toJson author, toJson urgency]
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

/-- Shared expander for noop annotation directives.  The directive body is
dropped at elaboration (`#[]`), so the block renders nothing and never reaches
the generated outputs — the original text survives only in the Verso source.
`:::instructors` uses this; `:::dev` has its own expander below so it can carry
author/urgency arguments. -/
def noopDirectiveFor (blockName : Name) : DirectiveExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.other $(mkIdent blockName) #[])

/-- A `:::dev` directive is a noop for author/developer comments.  It accepts
optional named author and urgency arguments, e.g.
`:::dev (author := "Benjamin Pierce (bcpierce00)") (urgency := SOONER)`; both
are recorded in the block's data (for a future dev-facing build) while the
body is dropped at elaboration. -/
@[directive]
def dev : DirectiveExpanderOf DevConfig
  | cfg, _contents => do
    let author ← match cfg.author with
      | some a => ``(some $(quote a))
      | none => ``(none)
    let urgency ← match cfg.urgency with
      | some u => ``(some $(quote u))
      | none => ``(none)
    ``(Verso.Doc.Block.other (SFLMeta.Block.devcomment $author $urgency) #[])
