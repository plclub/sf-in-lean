module

public meta import SFLCompat.Recall.Common

/-!
# Recall, checked byte for byte

`sf_recall_source` lets a chapter restate a definition from earlier in the
development while the build checks that the restatement matches the
original's source text, byte for byte. The restated text is what the
reader already saw, and it can never drift from the original.

```
sf_recall_source
  def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)
```

The restated declaration is parsed but never elaborated; the check is
purely textual: after the block indentation is removed from each side, the
two texts must be equal, byte for byte. The restatement may sit at a
different indentation depth, but it may not be reflowed or respaced.

The comparison covers whole declarations only. Carving a statement out of
the original's source would require parsing it, which is only possible in
the elaboration context of its declaration site; restating only a theorem
statement is therefore the province of `sf_recall statement`, which compares
elaborated types.
-/

namespace SFLCompat.Recall.Source

open Lean Elab Command

/--
`recall_source` restates a definition from earlier in the development and
checks that the restatement matches the original's source text, byte for
byte, modulo block indentation.
-/
syntax (name := recallSrc) "sf_recall_source " command : command

elab_rules : command
  | `(sf_recall_source $cmd:command) => do
    let decl ← declaredName cmd
    let x ← liftCoreM <| withoutExporting <|
      realizeGlobalConstNoOverloadWithInfo decl.ident
    -- The restatement is never elaborated, so it produces no info of its
    -- own. The whole compared region is one big reference to the original:
    -- hovering anywhere in it shows the original, and go-to-definition
    -- jumps to it.
    addConstInfo cmd x
    let restated ← sourceOfSyntax cmd
    let original ← sourceOf x
    unless dedent restated == dedent original do
      throwErrorAt cmd
        (m!"the restatement of '{privateToUserName x}' does not match its source.\n\
            Original:{indentD original}\nRestated:{indentD restated}"
          ++ (← liftCoreM <| replaceWithOriginalHint cmd (dedent original) restated))

namespace Tests

inductive Palette where
  | red | green | blue

def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

theorem twice_id : twice id 3 = 3 := rfl

sf_recall_source
  inductive Palette where
    | red | green | blue

sf_recall_source
  def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

-- Leading comments are removed exactly, including the one-line, nested,
-- and line-comment forms; text without them is untouched.
#guard SFLCompat.Recall.stripLeadingComments
  "/-- d -/ theorem foo : True := trivial" == "theorem foo : True := trivial"
#guard SFLCompat.Recall.stripLeadingComments
  "/-- a /- b -/ c -/\ndef x := 1" == "def x := 1"
#guard SFLCompat.Recall.stripLeadingComments
  "/-- d -/\n-- note\n-- more\ndef x := 1" == "def x := 1"
#guard SFLCompat.Recall.stripLeadingComments "def x := 1" == "def x := 1"

/--
error: the restatement of 'SFLCompat.Recall.Source.Tests.twice' does not match its source.
Original:
  def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)
Restated:
  def twice (f : Nat → Nat) (n : Nat) : Nat := f <| f n

Hint: Replace the restatement with the original:
  def twice (f : Nat → Nat) (n : Nat) : Nat := f <̵|̵ ̵(̲f n)̲
-/
#guard_msgs in
sf_recall_source
  def twice (f : Nat → Nat) (n : Nat) : Nat := f <| f n

-- Reflowing the original is rejected even though the tokens agree.
/--
error: the restatement of 'SFLCompat.Recall.Source.Tests.twice' does not match its source.
Original:
  def twice (f : Nat → Nat) (n : Nat) : Nat := f (f n)
Restated:
  def twice (f : Nat → Nat) (n : Nat) : Nat :=
      f (f n)

Hint: Replace the restatement with the original:
  def twice (f : Nat → Nat) (n : Nat) : Nat :=
  ̵  ̵ ̵ ̵f (f n)
-/
#guard_msgs in
sf_recall_source
  def twice (f : Nat → Nat) (n : Nat) : Nat :=
    f (f n)

/--
error: the restated command declares several names; recall one declaration at a time
---
error: the restated command declares several names; recall one declaration at a time
-/
#guard_msgs in
sf_recall_source
  mutual
    def one : Nat := 1
    def two : Nat := 2
  end

end Tests

end SFLCompat.Recall.Source
