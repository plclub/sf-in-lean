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
  /-- An urgency keyword, conventionally `NOW`, `SOONER`, `LATER`, `TODO`, or
  `TOFIX`; written as a bare identifier. -/
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

/-- Decode a `Block.devcomment` payload `(author, urgency, year)`. -/
def decodeDevData? (data : Json) : Option (Option String × Option String × Option Nat) :=
  match data with
  | .arr #[a, u, y] =>
    let str? : Json → Option String
      | .str s => some s
      | _ => none
    let nat? : Json → Option Nat
      | .num n => some n.toFloat.toUInt32.toNat
      | _ => none
    some (str? a, str? u, nat? y)
  | _ => none

/-- Should a dev note surface in reader-facing outputs (the HTML book and the
generated `.lean` files)?  Only *actionable* notes are shown: those with
urgency `NOW` or `TODO`, or with no urgency at all.  `SOONER`/`LATER`/`TOFIX`
notes remain suppressed. -/
def devNoteShown (urgency : Option String) : Bool :=
  match urgency with
  | none => true
  | some u => u == "NOW" || u == "TODO"

/-- Provenance label for a rendered dev note —
`Dev note (Benjamin Pierce (bcpierce00), NOW, 2020)` — with absent fields
omitted.  `heading` selects the leading phrase: the HTML rendering uses the
default; the generated `.lean` files use `"NOTE FOR DEVELOPERS"`. -/
def devNoteLabel (author urgency : Option String) (year : Option Nat)
    (heading : String := "Dev note") : String :=
  let fields := author.toList ++ urgency.toList ++ (year.map toString).toList
  if fields.isEmpty then heading
  else s!"{heading} ({String.intercalate ", " fields})"

/-! `Block.devcomment` carries the note body as its children and records its
author/urgency metadata in `data`.  A note whose urgency passes `devNoteShown`
(`NOW`, `TODO`, or none) is rendered: brightly highlighted in the HTML book,
and passed through as a comment in the generated `.lean` files (see
`walkBlock` in `SFLMeta.Save`).  All other notes render nothing. -/
block_extension Block.devcomment (author : Option String)
    (urgency : Option String) (year : Option Nat) where
  data := Json.arr #[toJson author, toJson urgency, toJson year]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let some (author, urgency, year) := decodeDevData? data
        | pure .empty
      if devNoteShown urgency then
        let body : Verso.Output.Html ← contents.foldlM (init := .empty) fun acc b =>
          return acc ++ (← goB b)
        return {{
          <div class="sf-dev-note">
            <div class="sf-dev-note-label">{{devNoteLabel author urgency year}}</div>
            {{body}}
          </div>
        }}
      else
        pure .empty
  toTeX := none
  extraCss := [
r##"
div.sf-dev-note {
  margin: 1em 0;
  padding: 0.5em 0.9em;
  border: 1px solid #e6a700;
  border-left: 6px solid #e6a700;
  background: #fff3b0;
  border-radius: 3px;
}
div.sf-dev-note > .sf-dev-note-label {
  font-family: var(--verso-structure-font-family);
  font-weight: 700;
  font-size: 0.85em;
  text-transform: uppercase;
  letter-spacing: 0.03em;
  color: #7a5800;
  margin-bottom: 0.3em;
}
"##
  ]

/-- Shared expander for noop annotation directives.  The directive body is
dropped at elaboration (`#[]`), so the block renders nothing and never reaches
the generated outputs — the original text survives only in the Verso source.
`:::instructors` uses this; `:::dev` has its own expander below so it can carry
author/urgency arguments. -/
def noopDirectiveFor (blockName : Name) : DirectiveExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.other $(mkIdent blockName) #[])

/-- A `:::dev` directive holds an author/developer comment.  It accepts
optional positional author and urgency arguments and an optional named year,
e.g. `:::dev "Benjamin Pierce (bcpierce00)" SOONER (year := 2020)`; all are
recorded in the block's data, and the body is elaborated and kept as the
block's children.  Whether anything is *rendered* is decided per-note by
`devNoteShown` (only `NOW`, `TODO`, or urgency-free notes surface).  NB: since
the body elaborates, a ` ```lean ` fence inside a dev note runs the Lean code —
use a plain ` ``` ` fence for code that must stay inert. -/
@[directive]
def dev : DirectiveExpanderOf DevConfig
  | cfg, contents => do
    let author ← match cfg.author with
      | some a => ``(some $(quote a))
      | none => ``(none)
    let urgency ← match cfg.urgency with
      | some u => ``(some $(quote u))
      | none => ``(none)
    let year ← match cfg.year with
      | some y => ``(some $(quote y))
      | none => ``(none)
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SFLMeta.Block.devcomment $author $urgency $year)
        #[$blocks,*])
