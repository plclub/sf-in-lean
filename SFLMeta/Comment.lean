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

/-- The three urgency keywords a `:::dev` note may carry, in canonical spelling.
Any other urgency is rejected as an error by the directive's argument parser. -/
def devUrgencies : List String := ["NOW", "BeforeNextRelease", "PotentialImprovement"]

/-- Canonicalize a `:::dev` urgency keyword, recognized case-insensitively:
`NOW`, `BeforeNextRelease`, `PotentialImprovement` (in any case) map to their
canonical spelling; every other keyword yields `none` (an error at parse time).
The older source spellings are rewritten upstream by `to_verso.py` (`TODO` →
`NOW`, `SOON`/`SOONER` → `BeforeNextRelease`, `LATER` → `PotentialImprovement`),
so only the canonical three should ever reach a hand-authored `:::dev`. -/
def canonUrgency? (s : String) : Option String :=
  match s.toUpper with
  | "NOW" => some "NOW"
  | "BEFORENEXTRELEASE" => some "BeforeNextRelease"
  | "POTENTIALIMPROVEMENT" => some "PotentialImprovement"
  | _ => none

/-- Author-facing configuration for `:::dev`.  All fields are optional; author
and urgency are positional and year is named:  `:::dev`,
`:::dev "Benjamin Pierce (bcpierce00)"`, `:::dev BeforeNextRelease`, and
`:::dev "Noé De Santo (Ef55)" PotentialImprovement (year := 2025)` are all valid.
The two positionals cannot be confused: an author is always a *string literal*
(it contains spaces and parentheses) while an urgency keyword is always a *bare
identifier*, and the parsers accept only their own category. -/
structure DevConfig where
  /-- Who filed the note, conventionally a full name followed by a GitHub
  handle in parentheses: `"Benjamin Pierce (bcpierce00)"`. -/
  author : Option String
  /-- An urgency keyword — one of `NOW`, `BeforeNextRelease`, or
  `PotentialImprovement` (recognized in any case), written as a bare identifier
  and stored canonicalized. -/
  urgency : Option String
  /-- The year the note was filed (from a `BCP'20`-style tag). -/
  year : Option Nat
deriving Repr

section
variable [Monad m] [MonadError m]

/-- Argument parser for `DevConfig`: optional positional author (a string) and
urgency (an identifier, validated/canonicalized later by the `dev` expander via
`canonUrgency?`), and an optional named year.  Urgency is parsed permissively
here — an `<|>`-guarded positional swallows a `get`-time error, which would turn
an invalid urgency into a confusing leftover-argument message — and validated in
the expander instead, so a bad keyword gets a precise error. -/
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
generated `.lean` files)?  Only *actionable* notes are shown: those with urgency
`NOW` or `BeforeNextRelease`, or with no urgency at all.  `PotentialImprovement`
notes remain suppressed. -/
def devNoteShown (urgency : Option String) : Bool :=
  match urgency with
  | none => true
  | some u => u == "NOW" || u == "BeforeNextRelease"

/-- Render an author for a note label.  The authoring convention puts the GitHub
handle in parentheses (`"Benjamin Pierce (bcpierce00)"`), which would nest inside
the label's own parenthesized field list, so a trailing `(handle)` is rewritten
to an `@handle` suffix.  An author in any other shape is left alone. -/
def devNoteAuthorText (author : String) : String :=
  if author.endsWith ")" then
    match (author.dropRight 1).splitOn " (" with
    | [name, handle] => s!"{name} @{handle}"
    | _ => author
  else author

/-- Render an urgency keyword for a note label: the multi-word canonical
spellings are spelled out with spaces (`BeforeNextRelease` → `before next
release`), `NOW` is left as is. -/
def devUrgencyText (urgency : String) : String :=
  match urgency with
  | "BeforeNextRelease" => "before next release"
  | "PotentialImprovement" => "potential improvement"
  | u => u

/-- Provenance label for a rendered dev note —
`Note to developers (Benjamin Pierce @bcpierce00, before next release, 2020)` —
with absent fields omitted.  `heading` selects the leading phrase; both the HTML
rendering and the generated `.lean` files use the mixed-case default. -/
def devNoteLabel (author urgency : Option String) (year : Option Nat)
    (heading : String := "Note to developers") : String :=
  let fields := (author.map devNoteAuthorText).toList
    ++ (urgency.map devUrgencyText).toList ++ (year.map toString).toList
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
      | some u =>
        match canonUrgency? u with
        | some c => ``(some $(quote c))
        | none =>
          throwError m!"Unknown :::dev urgency '{u}'; expected one of {devUrgencies}"
      | none => ``(none)
    let year ← match cfg.year with
      | some y => ``(some $(quote y))
      | none => ``(none)
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SFLMeta.Block.devcomment $author $urgency $year)
        #[$blocks,*])
