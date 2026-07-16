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

/-- Author-facing configuration for `:::dev`.  All fields are optional; author
and urgency are positional and year is named:  `:::dev`,
`:::dev "Benjamin Pierce (bcpierce00)"`, `:::dev SOONER`, and
`:::dev "Noé De Santo (Ef55)" LATER (year := 2025)` are all valid.  The two
positionals cannot be confused: an author is always a *string literal* (it
contains spaces and parentheses) while an urgency keyword is always a *bare
identifier*, and the parsers accept only their own category. -/
structure DevConfig where
  /-- Who filed the note, conventionally a full name followed by a GitHub
  handle in parentheses: `"Benjamin Pierce (bcpierce00)"`. -/
  author : Option String
  /-- An urgency keyword, conventionally `SOONER`, `LATER`, `TODO`, or `TOFIX`;
  written as a bare identifier. -/
  urgency : Option String
  /-- The year the note was filed (from a `BCP'20`-style tag). -/
  year : Option Nat
deriving Repr

section
variable [Monad m] [MonadError m]

/-- An argument value written as a bare identifier (`SOONER`), yielding its
text. -/
def ValDesc.identText : ValDesc m String where
  description := doc!"an identifier"
  signature := CanMatch.Ident
  get
    | .name x => Pure.pure x.getId.toString
    | other => throwError "Expected identifier, got {toMessageData other}"

/-- Argument parser for `DevConfig`: optional positional author (a string) and
urgency (an identifier), and an optional named year. -/
def DevConfig.parse : ArgParse m DevConfig :=
  DevConfig.mk
    <$> ((some <$> ArgParse.positional `author ValDesc.string) <|> Pure.pure none)
    <*> ((some <$> ArgParse.positional `urgency ValDesc.identText) <|> Pure.pure none)
    <*> ArgParse.named `year .nat true

instance : FromArgs DevConfig m := ⟨DevConfig.parse⟩

end

/-! `Block.devcomment` records its author/urgency metadata in `data` so that a
future dev-facing build can typeset notes in a standard way; the current
builds render nothing. -/
block_extension Block.devcomment (author : Option String)
    (urgency : Option String) (year : Option Nat) where
  data := Json.arr #[toJson author, toJson urgency, toJson year]
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
optional positional author and urgency arguments and an optional named year,
e.g. `:::dev "Benjamin Pierce (bcpierce00)" SOONER (year := 2020)`; all are
recorded in the block's data (for a future dev-facing build) while the body is
dropped at elaboration. -/
@[directive]
def dev : DirectiveExpanderOf DevConfig
  | cfg, _contents => do
    let author ← match cfg.author with
      | some a => ``(some $(quote a))
      | none => ``(none)
    let urgency ← match cfg.urgency with
      | some u => ``(some $(quote u))
      | none => ``(none)
    let year ← match cfg.year with
      | some y => ``(some $(quote y))
      | none => ``(none)
    ``(Verso.Doc.Block.other (SFLMeta.Block.devcomment $author $urgency $year) #[])
