module

public meta import Lean.Elab.Command

namespace SFLCompat.Recall

open Lean Elab Command
public meta section

/-- All `declId` nodes in a command, in source order. -/
partial def declIds (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.flatMap declIds
  if stx.isOfKind ``Lean.Parser.Command.declId then #[stx] ++ inner else inner

/-- The syntax and written name of the single declaration in a recall command. -/
structure DeclSyntax where
  ident : Syntax
  written : Name

/--
The `declId` node of a declaration command, together with the name written
in it. A command that declares several names (a `mutual` block) or none (an
anonymous `instance`, an `example`) is rejected.
-/
def declaredName (cmd : Syntax) : CommandElabM DeclSyntax := do
  let defined := declIds cmd
  match h : defined.size with
  | 0 => throwErrorAt cmd "the restated command does not declare a name"
  | 1 =>
    let declId := defined[0]
    return { ident := declId[0], written := declId[0].getId }
  | n + 2 =>
    for h : i in 0...(n + 1) do
      logErrorAt defined[i]
        "the restated command declares several names; recall one declaration at a time"
    throwErrorAt defined[n + 1]
      "the restated command declares several names; recall one declaration at a time"

/--
Removes the block indentation of a declaration's source text. The first
line starts at the declaration's first token and has no indentation of its
own; each following line is stripped of the smallest indentation found
among the non-blank ones. Restatements of the same text at different block
depths dedent to identical strings, and every other difference survives
dedenting.
-/
def dedent (s : String) : String :=
  match indentWidth s, s.splitOn "\n" with
  | some n, first :: rest =>
    "\n".intercalate (first :: rest.map (fun l => String.ofList (l.toList.drop n)))
  | _, _ => s
where
  /-- The smallest indentation among the non-blank continuation lines. -/
  indentWidth (s : String) : Option Nat :=
    s.splitOn "\n" |>.drop 1 |>.map (·.toList)
      |>.filter (fun l => !l.all (·.isWhitespace))
      |>.map (fun l => (l.takeWhile (· == ' ')).length)
      |>.min?

/--
Indents the continuation lines of dedented source text by `n` spaces, so
that the text reads correctly at the block depth of a restatement.
-/
def reindent (s : String) (n : Nat) : String :=
  match s.splitOn "\n" with
  | [] => s
  | first :: rest =>
    let pad := String.ofList (List.replicate n ' ')
    "\n".intercalate (first :: rest.map fun l =>
      if l.toList.all (·.isWhitespace) then l else pad ++ l)

/--
Removes the comments from the front of dedented source text, together with
the whitespace around them, so that a suggestion offered for a restatement
that carries no comments does not introduce any. The text of a declaration
or of a constructor begins with its doc comment when it has one, possibly
accompanied by ordinary comments, and a leading block comment ends at its
depth-balanced closing delimiter, so a character scan recognizes the
leading run of comments exactly. A comment elsewhere in the text cannot be
recognized without lexing and is left in place.
-/
def stripLeadingComments (s : String) : String := Id.run do
  let mut cs := s.toList.dropWhile (·.isWhitespace)
  repeat
    if cs.take 2 == ['/', '-'] then
      cs := cs.drop 2
      let mut depth := 1
      while depth > 0 do
        match cs with
        | [] => return s
        | '/' :: '-' :: rest => depth := depth + 1; cs := rest
        | '-' :: '/' :: rest => depth := depth - 1; cs := rest
        | _ :: rest => cs := rest
    else if cs.take 2 == ['-', '-'] then
      cs := cs.dropWhile (· != '\n')
    else
      break
    cs := cs.dropWhile (·.isWhitespace)
  return String.ofList cs

/--
A clickable suggestion that replaces the restated text at `span` with
`original`, which must already be dedented. The original's indentation is
moved to match the restatement's: the restatement's own indentation width
when it has continuation lines, one step past the span's start column when
it does not.
-/
def replaceWithOriginalHint [Monad m] [MonadFileMap m] [MonadLiftT CoreM m]
    (span : Syntax) (original restated : String) : m MessageData := do
  let fileMap ← getFileMap
  let k := match dedent.indentWidth restated, span.getRange? with
    | some k, _ => k
    | none, some r => (fileMap.toPosition r.start).column + 2
    | none, none => 2
  MessageData.hint m!"Replace the restatement with the original:"
    #[{ suggestion := .string (reindent original k), span? := some span }]

/--
The source text of the declaration of `x`, from the file that declared it.

The location comes from the declaration range that Lean records for every
constant. A declaration from the current file is read out of the file map;
one from an imported module is read from its source file, found on the
source search path. In a book build the whole project's sources are on that
path, so definitions can be recalled across chapters.
-/
def sourceOf [Monad m] [MonadEnv m] [MonadError m] [MonadFileMap m]
    [MonadLiftT IO m] [MonadLiftT BaseIO m] (x : Name) : m String := do
  let some ranges ← findDeclarationRanges? x
    | throwError "no declaration range recorded for '{x}'"
  let env ← getEnv
  let text ←
    match env.getModuleIdxFor? x with
    | none => pure (← getFileMap)
    | some idx => do
      let modName := env.allImportedModuleNames[idx.toNat]!
      let sp ← getSrcSearchPath
      let some path ← sp.findModuleWithExt "lean" modName
        | throwError "source for module '{modName}' is not on the search path"
      pure (FileMap.ofString (← IO.FS.readFile path))
  return String.Pos.Raw.extract text.source
    (text.ofPosition ranges.range.pos) (text.ofPosition ranges.range.endPos)

/-- The source text of a piece of syntax in the current file. -/
def sourceOfSyntax [Monad m] [MonadError m] [MonadFileMap m]
    (stx : Syntax) : m String := do
  let some r := stx.getRange?
    | throwErrorAt stx "no source range"
  return String.Pos.Raw.extract (← getFileMap).source r.start r.stop

end

end SFLCompat.Recall
