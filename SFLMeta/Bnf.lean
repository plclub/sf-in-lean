import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output Verso.Output.Html
open Verso.Doc.Html

namespace SFLMeta

/-- A token in a BNF production right-hand side. -/
inductive BnfToken where
  /-- A reference to a non-terminal (the same kind of thing the LHS defines), e.g. `T` or `t`.
  Written as a plain identifier in the source. -/
  | nonterm (name : String)
  /-- A schematic variable standing for an arbitrary object-language identifier, e.g. `x` in
  `λ x : T , t`. Written with a leading underscore in the source (`_x` → displayed as `x`). -/
  | «meta» (name : String)
  /-- A literal terminal of the object language, written as a string in the source. -/
  | lit (literal : String)
deriving Repr, Inhabited, BEq, ToJson, FromJson

/-- One alternative of a production: a sequence of tokens, plus an optional gloss
naming the form it describes (SF's right-hand `(application)` column). -/
structure BnfAlt where
  /-- The tokens of the alternative, in source order. -/
  tokens : Array BnfToken
  /-- The gloss, without its surrounding parentheses. -/
  note : Option String := none
deriving Repr, Inhabited, BEq, ToJson, FromJson

/-- A single BNF production: `lhs ::= alts[0] | alts[1] | ...`. -/
structure BnfProduction where
  /-- The non-terminal being defined. -/
  lhs : String
  /-- The right-hand-side alternatives. -/
  alts : Array BnfAlt
deriving Repr, Inhabited, BEq, ToJson, FromJson

/-- A BNF grammar: a sequence of productions in source order. -/
structure BNF where
  /-- The productions. -/
  productions : Array BnfProduction
deriving Repr, Inhabited, BEq, ToJson, FromJson

namespace Bnf

/-! ## Surface syntax

A `bnf%` term and a ` ```bnf ` code block share the same grammar. Productions end
with `;`; alternatives within a production are separated by `|`; a token is either
an identifier (metavariable) or a string literal (terminal). An alternative may
end with a parenthesized string, `("application")`, which becomes a gloss in a
right-hand column rather than part of the grammar. The gloss is written as a
string literal so that it can be arbitrary prose without colliding with the
token syntax. -/

/-- A token of the BNF surface syntax. -/
declare_syntax_cat bnfTok
/-- An identifier is a metavariable token. -/
syntax ident : bnfTok
/-- A string literal is a terminal token. -/
syntax str : bnfTok

/-- One alternative of a BNF production. -/
declare_syntax_cat bnfAlt
/-- An alternative is a non-empty sequence of tokens, optionally followed by a
parenthesized gloss. -/
syntax bnfTok+ ("(" str ")")? : bnfAlt

/-- A single production. -/
declare_syntax_cat bnfProd
/-- A production: `lhs ::= alt | alt | … ;`. The trailing `;` separates productions. -/
syntax ident "::=" bnfAlt ("|" bnfAlt)* ";" : bnfProd

/-- A sequence of productions: the body of a `bnf%` or ` ```bnf ` block. -/
declare_syntax_cat bnfBody
/-- A body is zero or more productions. -/
syntax bnfProd* : bnfBody

/-- A term-level BNF literal: elaborates to a `SFLMeta.BNF` value. -/
syntax (name := bnfTerm) "bnf%" bnfBody "end" : term

/-! ## Macro: parsed syntax → term -/

/-- Translate a parsed `bnfTok` to term syntax producing a `BnfToken`.

An identifier with a leading underscore is a schematic metavariable (the underscore is
stripped); any other identifier is a non-terminal reference. -/
def tokToTerm (stx : TSyntax `bnfTok) : MacroM (TSyntax `term) :=
  match stx with
  | `(bnfTok| $i:ident) =>
    let name := i.getId.toString
    if name.startsWith "_" then
      let s := Syntax.mkStrLit (name.drop 1).toString
      `(SFLMeta.BnfToken.meta $s)
    else
      let s := Syntax.mkStrLit name
      `(SFLMeta.BnfToken.nonterm $s)
  | `(bnfTok| $s:str) =>
    `(SFLMeta.BnfToken.lit $s)
  | _ => Macro.throwUnsupported

/-- Translate a parsed `bnfAlt` to term syntax producing a `BnfAlt`. -/
def altToTerm (stx : TSyntax `bnfAlt) : MacroM (TSyntax `term) := do
  let `(bnfAlt| $toks:bnfTok* $[($note:str)]?) := stx | Macro.throwUnsupported
  let tokTerms ← toks.mapM tokToTerm
  let noteTerm ← match note with
    | some s => `(some $s)
    | none   => `(none)
  `(({ tokens := #[$tokTerms,*], note := $noteTerm } : SFLMeta.BnfAlt))

/-- Translate a parsed `bnfProd` to term syntax producing a `BnfProduction`. -/
def prodToTerm (stx : TSyntax `bnfProd) : MacroM (TSyntax `term) := do
  let `(bnfProd| $lhs:ident ::= $first:bnfAlt $[| $rest:bnfAlt]* ;) := stx
    | Macro.throwUnsupported
  let lhsStr := Syntax.mkStrLit lhs.getId.toString
  let altTerms ← (#[first] ++ rest).mapM altToTerm
  `(({ lhs := $lhsStr, alts := #[$altTerms,*] } : SFLMeta.BnfProduction))

macro_rules
  | `(bnf% $body:bnfBody end) => do
    let `(bnfBody| $[$prods:bnfProd]*) := body | Macro.throwUnsupported
    let prodTerms ← prods.mapM prodToTerm
    `(({ productions := #[$prodTerms,*] } : SFLMeta.BNF))

/-! ## Runtime parser for the code-block body -/

/-- Translate a parsed `bnfTok` syntax to a `BnfToken` value.

Idents starting with `_` are schematic metavariables (the underscore is stripped); other
idents are non-terminal references. -/
def tokOfSyntax (stx : TSyntax `bnfTok) : Except String BnfToken :=
  match stx with
  | `(bnfTok| $i:ident) =>
    let name := i.getId.toString
    if name.startsWith "_" then .ok (.meta (name.drop 1).toString)
    else .ok (.nonterm name)
  | `(bnfTok| $s:str)   => .ok (.lit s.getString)
  | _ => .error s!"unrecognized bnfTok"

/-- Translate a parsed `bnfAlt` to a `BnfAlt`. -/
def altOfSyntax (stx : TSyntax `bnfAlt) : Except String BnfAlt := do
  let `(bnfAlt| $toks:bnfTok* $[($note:str)]?) := stx | .error "expected bnfAlt"
  let tokens ← toks.mapM tokOfSyntax
  pure { tokens, note := note.map (·.getString) }

/-- Translate a parsed `bnfProd` to a `BnfProduction`. -/
def prodOfSyntax (stx : TSyntax `bnfProd) : Except String BnfProduction := do
  let `(bnfProd| $lhs:ident ::= $first:bnfAlt $[| $rest:bnfAlt]* ;) := stx
    | .error "expected bnfProd"
  let alts ← (#[first] ++ rest).mapM altOfSyntax
  pure { lhs := lhs.getId.toString, alts }

/-- Translate a parsed `bnfBody` to a `BNF`. -/
def bnfOfSyntax (stx : TSyntax `bnfBody) : Except String BNF := do
  let `(bnfBody| $[$prods:bnfProd]*) := stx | .error "expected bnfBody"
  let productions ← prods.mapM prodOfSyntax
  pure { productions }

/--
Parse a BNF source string (the body of a ` ```bnf ` block) into a `BNF`.
Surfaces parser and translation errors via `throwError`.
-/
def parseString (src : String) : DocElabM BNF := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `bnfBody src with
  | .error e => throwError "BNF parse error: {e}"
  | .ok stx =>
    match bnfOfSyntax ⟨stx⟩ with
    | .ok bnf => pure bnf
    | .error e => throwError "BNF: {e}"

/-! ## HTML rendering -/

/-- Render a single token as inline HTML. -/
def tokToHtml : BnfToken → Html
  | .nonterm s => {{ <span class="bnf-nt">{{s}}</span> }}
  | .meta    s => {{ <span class="bnf-mv">{{s}}</span> }}
  | .lit     s => {{ <span class="bnf-kw">{{s}}</span> }}

/-- Render a single alternative (sequence of tokens) as inline HTML.  The gloss, if
any, is rendered separately by `toHtmlImpl` into its own column. -/
def altToHtml (alt : BnfAlt) : Html :=
  Html.seq <| alt.tokens.foldl (init := #[]) fun acc t =>
    if acc.isEmpty then #[tokToHtml t]
    else acc.push (Html.text false " ") |>.push (tokToHtml t)

/-- Render a full BNF grammar as a structured HTML table. The LHS of each production is
rendered with the same `.bnf-nt` styling as a non-terminal reference on the RHS so that the
same name looks the same wherever it appears.  A fourth column carries the alternatives'
glosses; it is present but empty for a grammar that has none. -/
def toHtmlImpl (b : BNF) : Html :=
  let rows : Array Html := b.productions.flatMap fun p =>
    p.alts.mapIdx fun i alt =>
      let lhsCell : Html :=
        if i = 0 then {{ <td class="bnf-lhs"><span class="bnf-nt">{{p.lhs}}</span></td> }}
        else {{ <td class="bnf-lhs">{{" "}}</td> }}
      let sep : String := if i = 0 then "::=" else "|"
      let noteCell : Html :=
        match alt.note with
        | some n => {{ <td class="bnf-note">{{"(" ++ n ++ ")"}}</td> }}
        | none   => {{ <td class="bnf-note">{{" "}}</td> }}
      {{ <tr>
           {{lhsCell}}
           <td class="bnf-sep">{{sep}}</td>
           <td class="bnf-alt">{{altToHtml alt}}</td>
           {{noteCell}}
         </tr> }}
  {{ <table class="bnf">{{Html.seq rows}}</table> }}

/-! ## Plain-text rendering

The extracted `.lean` files have no styling to distinguish a terminal from a
non-terminal, so a grammar is rendered there as SF's original aligned display:
tokens separated by spaces, quotes dropped, glosses lined up in a right-hand
column. -/

/-- Render a single token as plain text. -/
def tokToText : BnfToken → String
  | .nonterm s => s
  | .meta    s => s
  | .lit     s => s

/-- Render an alternative as plain text: its tokens, space-separated. -/
def altToText (alt : BnfAlt) : String :=
  String.intercalate " " (alt.tokens.toList.map tokToText)

/-- Render a full BNF grammar as an aligned plain-text display.  The gloss
column is aligned across the whole grammar, not per production. -/
def toTextImpl (b : BNF) : String :=
  let rows : Array (String × Option String) := b.productions.flatMap fun p =>
    p.alts.mapIdx fun i alt =>
      let lhs := if i = 0 then p.lhs else String.ofList (List.replicate p.lhs.length ' ')
      let sep := if i = 0 then "::=" else "  |"
      (lhs ++ " " ++ sep ++ " " ++ altToText alt, alt.note)
  let width := rows.foldl (init := 0) fun w (l, _) => max w l.length
  String.intercalate "\n" (rows.toList.map fun (l, note) =>
    match note with
    | some n => l ++ String.ofList (List.replicate (width + 4 - l.length) ' ') ++ "(" ++ n ++ ")"
    | none   => l)

/-! ## TeX rendering -/

/-- Render a single token as a TeX fragment. -/
def tokToTeX : BnfToken → Verso.Output.TeX
  | .nonterm s => .raw s!"\\mathit\{{s}}"
  | .meta    s => .raw s!"\\mathit\{{s}}"
  | .lit     s => .raw s!"\\textsf\{{s}}"

/-- Render an alternative as a TeX fragment, with `~` separators between tokens.  The
gloss, if any, is rendered separately by `toTeXImpl` into its own column. -/
def altToTeX (alt : BnfAlt) : Verso.Output.TeX :=
  Verso.Output.TeX.seq <| alt.tokens.foldl (init := #[]) fun acc t =>
    if acc.isEmpty then #[tokToTeX t]
    else acc.push (.raw "~") |>.push (tokToTeX t)

/-- Render a full BNF grammar as a LaTeX `tabular` environment.  The fourth column
carries the alternatives' glosses, and stays empty for a grammar that has none. -/
def toTeXImpl (b : BNF) : Verso.Output.TeX :=
  let rows : Array Verso.Output.TeX := b.productions.flatMap fun p =>
    p.alts.mapIdx fun i alt =>
      let lhsCell : Verso.Output.TeX :=
        if i = 0 then .raw s!"\\mathit\{{p.lhs}}" else .empty
      let sep : Verso.Output.TeX :=
        if i = 0 then .raw "::=" else .raw "$\\mid$"
      let noteCell : Verso.Output.TeX :=
        match alt.note with
        | some n => .raw s!"\\textit\{({n})}"
        | none   => .empty
      .seq #[lhsCell, .raw " & ", sep, .raw " & ", altToTeX alt, .raw " & ", noteCell,
             .raw " \\\\\n"]
  .seq #[.raw "\\begin{tabular}{llll}\n", .seq rows, .raw "\\end{tabular}\n"]

end Bnf

/-! ## Block extension and code block -/

block_extension Block.bnf (json : String) (source : String) where
  data := Json.arr #[.str json, .str source]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match data with
      | .arr #[.str jsonStr, .str _] =>
        match Json.parse jsonStr >>= fromJson? with
        | .ok (b : BNF) => pure (Bnf.toHtmlImpl b)
        | .error e =>
          Verso.reportError s!"BNF deserialization failed: {e}"
          pure .empty
      | _ =>
        Verso.reportError "BNF: malformed data"
        pure .empty
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ _ _ data _ => do
      match data with
      | .arr #[.str jsonStr, .str _] =>
        match Json.parse jsonStr >>= fromJson? with
        | .ok (b : BNF) => pure (Bnf.toTeXImpl b)
        | .error e =>
          Verso.reportError s!"BNF deserialization failed: {e}"
          pure .empty
      | _ =>
        Verso.reportError "BNF: malformed data"
        pure .empty
  extraCss := [
r##"
table.bnf {
  margin: 1em auto;
  border-collapse: collapse;
  font-family: var(--verso-code-font-family, monospace);
}
table.bnf td {
  padding: 0.15em 0.5em;
  vertical-align: baseline;
}
table.bnf td.bnf-lhs { text-align: right; }
table.bnf td.bnf-sep { text-align: center; }
table.bnf td.bnf-alt { text-align: left; }
table.bnf .bnf-nt  { font-style: italic; }
table.bnf .bnf-mv  {
  font-style: italic;
  text-decoration: underline;
  text-decoration-thickness: 0.5px;
  text-underline-offset: 0.18em;
}
table.bnf .bnf-kw  { font-weight: 600; font-family: var(--verso-code-font-family, monospace); }
/* The gloss column: set in the body font, muted, and pushed away from the
   grammar so it reads as an annotation rather than as part of the syntax. */
table.bnf td.bnf-note {
  padding-left: 2.5em;
  text-align: left;
  font-family: inherit;
  font-style: italic;
  opacity: 0.65;
}
"##
  ]

/-- A ` ```bnf ` code block: parses its body as a BNF grammar and stores both the
parsed structure (for HTML/TeX rendering) and the original source. -/
@[code_block]
def bnf : CodeBlockExpanderOf Unit
  | (), str => do
    let src := str.getString
    let bnfVal ← Bnf.parseString src
    let json := (toJson bnfVal).compress
    ``(Verso.Doc.Block.other
        (SFLMeta.Block.bnf $(quote json) $(quote src))
        #[Verso.Doc.Block.code $(quote src)])

end SFLMeta
