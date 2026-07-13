import VersoManual
import VersoManual.InlineLean
import Illuminate
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse

import LF.IndProp

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Automation: More Automation" =>
%%%
htmlSplit := .never
file := "Automation"
%%%

::::full
Up to now, we've used the manual part of Lean's tactic
facilities.  In this chapter, we'll learn more about some of
Lean's powerful automation features, including
tactic combinators like `try` and `repeat`, decision procedures like `lia`,
and automatic simplification using `simp`.
Using these features together with Lean's metaprogramming facilities will enable us to make
some of our proofs startlingly short!  Used properly, they can
also make proofs more maintainable and robust to changes in
underlying definitions.

Our motivating example will be the following proof, repeated with
just a few small changes from the `IndProp` chapter.  We will
simplify this proof in several stages.
::::

::::terse
Consider the proof below. Notice all the repetition and near-repetition...
::::

```lean
theorem Perm3_In_old (α : Type) (x : α) (l₁ l₂ : List α) :
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  intros hPerm hIn
  induction hPerm
  case perm3_swap12 a b c =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . right; left; assumption
    . left; assumption
    . right; right; left; assumption
    . contradiction
  case perm3_swap23 a b c =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . left; assumption
    . right; right; left; assumption
    . right; left; assumption
    . contradiction
  case perm3_trans _ _ _ _ _ ih₁2 ih₂3 =>
    apply ih₂3; apply ih₁2; apply hIn
```

In this file, we will introduce tactics that will shrink this proof from
around eighteen lines to five.

# The `lia` Tactic

::::full
The `lia` tactic implements a decision procedure for integer linear
arithmetic, a subset of propositional logic and arithmetic. `lia`
is also a decision procedure for first-order logic.
:::dev
RAB: should we explain first-order logic? do they know what this is?
:::

If the goal is a universally quantified formula made out of

  - numeric constants, addition (`+` and `succ`), subtraction (`-` and `pred`)
    and multiplication by constants (this is what makes it Presburger arithmetic),

  - equality (`=` and `≠`) and ordering (`≤` and `<`), and

  - the logical connectives `∧`, `∨`, `¬`, and `→`,

then invoking `lia` will either solve the goal or fail, meaning
that the goal is actually false.  (If the goal is _not_ of this
form, `lia` will fail.)
::::

```lean
example : ∀ (m n o p : Nat),
    m + n ≤ n + o ∧ o + 3 = p + 3 →
    m ≤ p := by
  lia

example : ∀ (m n : Nat),
    m + n = n + m := by
  lia

example : ∀ (m n p : Nat),
    m + (n + p) = m + n + p := by
  lia

example : ∀ (A B C D : Prop),
  (A → B) → (B → C) → (C → D) → (A → D)
     := by
  lia

```

`lia` can many of the cases of our old `Perm3_In` example.
```lean
theorem Perm3_In_better_with_lia : ∀ (α : Type) (x : α) (l₁ l₂ : List α),
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  intros α x l₁ l₂ hPerm hIn
  induction hPerm
  case perm3_swap12 a b c =>
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at *
    obtain h | h | h | h := hIn
    . lia /- was right; left; assumption -/
    . lia
    . lia
    . lia
  case perm3_swap23 a b c =>
  -- Here, we solve _all_ goals- and eschew the `obtain` - with
  -- the <;> tactic combinator, which we saw in the `Induction` chapter.
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
  case perm3_trans _ _ _ _ _ ih₁2 ih₂3 =>
    lia /- was apply ih₂3; apply ih₁2; apply hIn -/
```

# Tactic Combinators

::::full
In `Induction`, we saw how to use the `<;>` combinator in order to apply the same
tactic to every subgoal in a proof. As a reminder, consider this example,
where `cases` on `b` and `c` each leaves two subgoals that are discharged identically:
::::

::::terse
Recall the `<;>` combinator...
::::

```lean
example (b c : Bool) : (b && c) = (c && b) := by
  cases b <;> cases c <;> rfl
```

::::full
This `<;>` is not the only such combinator that Lean has to offer, however.
In general, combinators allow us to build tactics out of smaller ones, letting us
discharge many similar subgoals at once. Getting used to them takes a
little energy, but it lets us scale up to more complex definitions and
more interesting properties without drowning in boring, repetitive detail.
::::

## The `try` combinator

::::full
The first such combinator we'll discuss is `try`. If `t` is a tactic,
then `try t` is a tactic that is just like `t`
except that, if `t` fails, `try t` _successfully_ does nothing at all
(rather than failing).
::::

::::terse
The `try` combinator allows tactics to fail.
::::

```lean
example (P : Prop) (hp : P) : P := by
  try rfl -- `rfl` would fail here, but `try` swallows the failure...
  exact hp -- ...so we can still finish some other way.

example : 1 = 1 := by
  try rfl -- here `try rfl` just does `rfl`
```

::::full
There is not much reason to use `try` in completely manual proofs like
these, but it is very useful together with the `<;>` combinator.
::::

```lean
inductive silly : Nat → Prop where
| silly1 n (h : n > 1) : silly n
| silly2 n (h : 1 ∈ []) : silly n
| silly3 n (h : exists m, n = m + 2) : silly n

example : ∀ n, silly n → n ≠ 1 := by
  intro n h
  cases h
  . lia
  . contradiction
  . lia
```

:::dev
TODO (@dsainati1): replace `cases` with `inversion` when its issue is fixed
:::

::::full
Here, we can use the `lia` tactic to close some of these goals, but not all of them. So,
a more compact way to write this proof would be:
::::

::::terse
The `try` and `<;>` combinators used together allow you to use a tactic to some,
but not all, goals...
::::

```lean
example : ∀ n, silly n → n ≠ 1 := by
  intro n h
  cases h <;> try lia
  -- `lia` doesn't know that `1 ∈ []` is impossible, but we can use `contradiction`
  contradiction
```

We can further simplify our `Perm3_In` example with `try`.

```lean
theorem Perm3_In_better_with_try (α : Type) (x : α) (l₁ l₂ : List α) :
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  intros hPerm hIn
  -- TODO: autoformatter needs to make this look decent
  induction hPerm <;>
  try rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
  case perm3_trans _ _ _ _ _ ih₁2 ih₂3 =>
    lia
```

Note that `try lia <;> try rw [...] <;> lia` _doesn't_ work, because
the first time that `try` catches a failure in a `<;>` sequence, the whole
sequence will stop executing.

:::dev
RAB: Use @berberman's infrastructure for expected failure here.
:::
```lean
/--
error: unsolved goals
case perm3_swap12
α : Type
x : α
l₁ l₂ : List α
a✝ b✝ c✝ : α
hIn : x ∈ [a✝, b✝, c✝]
⊢ x ∈ [b✝, a✝, c✝]

case perm3_swap23
α : Type
x : α
l₁ l₂ : List α
a✝ b✝ c✝ : α
hIn : x ∈ [a✝, b✝, c✝]
⊢ x ∈ [a✝, c✝, b✝]
-/
#guard_msgs(error) in
example (α : Type) (x : α) (l₁ l₂ : List α) :
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  intros hPerm hIn
  induction hPerm <;> try lia <;>
  try rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
```


## The `repeat` combinator

The  `repeat` combinator takes another tactic or parenthesized sequence of tactics
and keeps applying it until it fails.

Here is an example proving that `10` is in a long list using `repeat`:

```lean
example : 10 ∈ [1,2,3,4,5,6,7,8,9,10] := by
  repeat
    rw [List.mem_cons]
    try left; rfl
    -- try makes this optional, which is necessary for the last repetition where left; rfl succeeds
    try right
```

::::full
The tactic `repeat t` never fails: if the tactic `t` doesn't apply
to the original goal, then repeat _succeeds_ without changing the
goal at all (i.e., it repeats zero times).

```lean
example : 10 ∈ [1,2,3,4,5,6,7,8,9,10] := by
  -- This is a no-op
  repeat lia
  repeat
    rw [List.mem_cons]
    try left; rfl
    try right
```
::::

::::full
The tactic `repeat t` does not have any upper bound on the
number of times it applies `t`.  If `t` is a tactic that _always_
succeeds (and makes progress), then `repeat t` will loop
forever.
::::

::::terse
`repeat` can loop forever
::::

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ (m n : Nat),
  m + n = n + m := by
  intros m n
  /- Uncomment the next line to see the infinite loop occur.  You will
     then need to recomment it make Lean listen to you again. -/
  -- repeat rewrite [Nat.add_comm]
  sorry
```

::::full
Wait -- did we just write an infinite loop in Lean?!?!

Sort of.

While evaluation in Lean's term language is guaranteed to
terminate, _tactic_ evaluation is not.  This does not affect Lean's
logical consistency, however, since the job of `repeat` and other
tactics is to guide Lean in constructing proofs; if the
construction process diverges (i.e., it does not terminate), this
simply means that we have failed to construct a proof at all, not
that we have constructed a bad proof.
::::

## The `first` combinator

::::full
The `first` combinator takes a sequence of tactics and tries them in order,
stopping after the first success. As a silly example:
::::

::::terse
The `first` combinator applies the first successful tactic in a list:
::::

```lean
example : ∀ n m, n * (m + 1) = n * m + n := by
  first | rfl | left | lia | induction n
```

::::full
Neither `rfl` nor `left` succeed on this goal, but `lia` does, so `first` stops after `lia`
and never tries `induction`. As with `try`, `first` is most useful in combination with
other combinators. For example, we can rewrite our previous examples that used `repeat` and `try`
like so:
::::

::::terse
We can combine `first` with `repeat`:
::::

```lean
example : 10 ∈ [1,2,3,4,5,6,7,8,9,10] := by
  repeat first
    | exact List.mem_cons_self
    | apply List.mem_cons_of_mem
```

::::full
The `first` tactic here will attempt to close the goal with an application of `List.mem_cons_self`,
if it can, and otherwise `apply List.mem_cons_of_mem` to proceed to checking the next element in the
list. Note that the order here is important! If we had instead written:

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : 10 ∈ [1,2,3,4,5,6,7,8,9,10] := by
  repeat first
    | apply List.mem_cons_of_mem
    | exact List.mem_cons_self
  -- unprovable state!
  sorry
```

Here, when we reach the goal `10 ∈ [10]`, instead of closing the goal with `List.mem_cons_self`
like before, we would instead first try `apply List.mem_cons_of_mem`, which would also succeed.
This leaves us with the goal `10 ∈ []`, which is of course false.
::::

With `first`, we can solve the earlier issue with `try` where it would stop executing
the sequence on the first failure.

```lean
theorem Perm3_In_better_with_first (α : Type) (x : α) (l₁ l₂ : List α) :
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  intros hPerm hIn
  induction hPerm <;>
  -- TODO autoformat
  first
  | rw [List.mem_cons, List.mem_cons, List.mem_cons] at * <;> lia
  | lia
```

Our `Perm3_In` example is getting quite short! But can we do better?

# The `simp` Tactic

:::dev
TODO
:::

```lean
theorem Perm3_In_best (α : Type) (x : α) (l₁ l₂ : List α) :
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  intros hPerm hIn
  induction hPerm <;>
  -- TODO autoformat
  first
  | simp at * <;> lia
  | lia
```

# The `trivial` tactic

:::dev
TODO
:::

# Case Study: Regular Expressions

::::full
As a culminating exercise for this book and as practice using the automation techniques we
discussed above on a real proof,
we examine the theory of regular expressions,
eventually working up to a proof of the pumping lemma.
::::

## Definitions

::::full
Regular expressions are a natural language for describing sets of
strings. Their syntax is defined as follows:
::::

```lean
inductive RegExp (α : Type) : Type where
  | EmptySet
  | EmptyStr
  | Char (c : α)
  | App (r1 r2 : RegExp α)
  | Union (r1 r2 : RegExp α)
  | Star (r : RegExp α)
deriving BEq, DecidableEq, Repr

attribute [pp_nodot] RegExp.Char RegExp.App RegExp.Union RegExp.Star
```

Note that this definition is _polymorphic_: Regular
expressions in `RegExp α` describe strings with characters drawn
from `α` -- which in this exercise we represent as _lists_ with
elements from `α`.

::::full
(Technical aside: We depart slightly from standard practice in
that we do not require the type `α` to be finite.  This results in
a somewhat different theory of regular expressions, but the
difference is not significant for present purposes.)
::::

We connect regular expressions and strings by defining when a
regular expression _matches_ some string.

Informally this looks as follows:

  - The regular expression `EmptySet` does not match any string.

  - `EmptyString` matches the empty string `[]`.

  - `Char x` matches the one-character string `x`.

  - If `re₁` matches `s₁`, and `re₂` matches `s₂`,
    then `App re₁ re₂` matches `s₁ ++ s₂`.

  - If at least one of `re₁` and `re₂` matches `s`,
    then `Union re₁ re₂` matches `s`.

  - Finally, if we can write some string `s` as the concatenation
    of a sequence of strings `s = s_1 ++ ... ++ s_k`, and the
    expression `re` matches each one of the strings `s_i`,
    then `Star re` matches `s`.

    In particular, the sequence of strings may be empty, so
    `Star re` always matches the empty string `[]` no matter what
    `re` is.

We can easily translate this intuition into a set of rules,
where we write `s =~ re` to say that `re` matches `s`:

                        -------------- (MEmpty)
                        `[] =~ EmptyStr`

                        --------------- (MChar)
                        `[x] =~ (Char x)`

                    `s₁ =~ re₁`     `s₂ =~ re₂`
                  --------------------------- (MApp)
                  `(s₁ ++ s₂) =~ (App re₁ re₂)`

                           `s₁ =~ re₁`
                     --------------------- (MUnionL)
                     `s₁ =~ (Union re₁ re₂)`

                           `s₂ =~ re₂`
                     --------------------- (MUnionR)
                     `s₂ =~ (Union re₁ re₂)`

                        --------------- (MStar0)
                        `[] =~ (Star re)`

                           `s₁ =~ re`
                        `s₂ =~ (Star re)`
                    ----------------------- (MStarApp)
                    `(s₁ ++ s₂) =~ (Star re)`


This directly corresponds to the following `inductive` definition:

```lean
namespace RegExp
inductive ExpMatch {α : Type} : List α → RegExp α → Prop where
  | MEmpty : ExpMatch [] EmptyStr
  | MChar (c : α) : ExpMatch [c] (Char c)
  | MApp (s₁ : List α) (re₁ : RegExp α) (s₂ : List α) (re₂ : RegExp α)
         (h₁ : ExpMatch s₁ re₁) (h₂ : ExpMatch s₂ re₂)
       : ExpMatch (s₁ ++ s₂) (App re₁ re₂)
  | MUnionL (s₁ : List α) (re₁ : RegExp α) (re₂ : RegExp α)
            (h₁ : ExpMatch s₁ re₁) : ExpMatch s₁ (Union re₁ re₂)
  | MUnionR (s₂ : List α) (re₁ : RegExp α) (re₂ : RegExp α)
            (h₂ : ExpMatch s₂ re₂) : ExpMatch s₂ (Union re₁ re₂)
  | MStar0 (re : RegExp α) : ExpMatch [] (Star re)
  | MStarApp (s₁ s₂ : List α) (re : RegExp α)
             (h₁ : ExpMatch s₁ re) (h₂ : ExpMatch s₂ (Star re))
           : ExpMatch (s₁ ++ s₂) (Star re)

infix:40 " =~ " => ExpMatch
```

:::dev
TODO (@dsainati1) - replace with quiz directive
:::
::::full
Notice that this clause in our informal definition...

  - "The expression `EmptySet` does not match any string."

... is not explicitly reflected in the above definition.  Do we
need to add something?

   (A) Yes, we should add a rule for this.

   (B) No, one of the other rules already covers this case.

   (C) No, the _lack_ of a rule actually gives us the behavior we
       want.
::::

```lean
theorem quiz : ∀ α (s: List α), ¬(s =~ EmptySet) := by
  intro α s contra; inversion contra
```

::::full
Notice that these rules are not _quite_ the same as the
intuition that we gave at the beginning of the section. First, we
don't need to include a rule explicitly stating that no string is
matched by `EmptySet`; indeed, the syntax of inductive definitions
doesn't even _allow_ us to give such a "negative rule." We just
don't happen to include any rule that would have the effect of
`EmptySet` matching some string.

Second, the intuition we gave for `Union` and `Star` correspond
to two constructors each: `MUnionL` / `MUnionR`, and `MStar0` /
`MStarApp`.  The result is logically equivalent to the original
intuition but more convenient to use in Lean, since the recursive
occurrences of `ExpMatch` are given as direct arguments to the
constructors, making it easier to perform induction on evidence.
(The exercises below ask you
to prove that the constructors given in the inductive declaration
and the ones that would arise from a more literal transcription of
the intuition is indeed equivalent.)

Let's illustrate these rules with a few examples.
::::

## Examples

```lean
example : [1] =~ Char 1 := by
  apply ExpMatch.MChar

example : [1, 2] =~ App (Char 1) (Char 2):= by
  apply ExpMatch.MApp [1] <;> constructor
```

::::full
Notice how the last example applies `MApp` to the string
`[1]` directly.  Since the goal mentions `[1, 2]` instead of
`[1] ++ [2]`, Lean wouldn't be able to figure out how to split
the string on its own.)

Using `inversion`, we can also show that certain strings do _not_
match a regular expression:
::::

```lean
example : ¬([1, 2] =~ Char 1) := by
  intro contra; inversion contra
```

We can define helper functions for writing down regular
expressions. The `reg_exp_of_list` function constructs a regular
expression that matches exactly the string that it receives as an
argument:

```lean
def reg_exp_of_list {α} (l : List α) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')

example : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] := by
  apply ExpMatch.MApp [1]; constructor
  apply ExpMatch.MApp [2]; constructor
  apply ExpMatch.MApp [3]; constructor
  constructor
```

::::exercise (rating := 1) (name := "regexp_match_of_list")
As a quick exercise, prove that every list matches `reg_exp_of_list` of itself:

```lean
theorem regexp_match_of_list α (l : List α) : l =~ reg_exp_of_list l := by
  solution!
    induction l with
    | nil => constructor
    | cons hd tl ih =>
        simp [reg_exp_of_list]
        have h : hd :: tl = [hd] ++ tl := by simp
        rw [h]
        constructor; constructor; assumption
```
:::grade
```
GRADE_THEOREM 2: regexp_match_of_list
```
:::
::::

::::full
We can also prove general facts about `ExpMatch`. For instance,
the following lemma shows that every string `s` matched by `re`
is also matched by `Star re`.
::::

::::terse
Something more interesting:
::::


:::dev
TODO: (@dsainati1) - how to make this a WORKINCLASS in verso?
:::
```lean
theorem MStar1 α s (re : RegExp α) :
    s =~ re →
    s =~ Star re := by
    intro h
    rw [←List.append_nil s]
    constructor
    . assumption
    . constructor
```

::::full
(Note the use of `app_nil_r` to change the goal of the theorem to
exactly the shape expected by `MStarApp`.)
::::

The following lemmas show that the intuition about matching given
at the beginning of the section can be obtained from the formal
inductive definition.

::::exercise (rating := 1) (name := "EmptySet_is_empty")

```lean
theorem EmptySet_is_empty α (s : List α) : ¬(s =~ EmptySet) := by
  solution!
    intros h
    inversion h
```
:::grade
```
GRADE_THEOREM 0.5: EmptySet_is_empty
```
:::
::::

::::exercise (rating := 1) (name := "MUnion'")

```lean
theorem MUnion' : ∀ α (s : List α) (re₁ re₂ : RegExp α),
  s =~ re₁ ∨ s =~ re₂ →
  s =~ Union re₁ re₂ := by
  solution!
    rintro α s re₁ re₂ (h | h)
    . apply ExpMatch.MUnionL; assumption
    . apply ExpMatch.MUnionR; assumption
```
:::grade
```
GRADE_THEOREM 0.5: MUnion'
```
:::
::::

The next lemma is stated in terms of the `fold` function on Lists:
If `ss : List (List α)` represents a sequence of
strings `s₁, ..., sn`, then `List.foldr (· ++ ·) ss []` is the result of
concatenating them all together.

::::exercise (rating := 2) (name := "MUnion'")

```lean
theorem MStar' α (ss : List (List α)) (re : RegExp α)
  (h : ∀ s, s ∈ ss → s =~ re) :
  ss.foldr (· ++ ·) [] =~ RegExp.Star re := by
  -- ADMITTED
  induction ss with
  | nil => constructor
  | cons s ss' ih =>
    simp
    constructor
    · apply h; simp
    · apply ih; intro s' hs'
      apply h; simp; right; assumption
```
:::grade
```
GRADE_THEOREM 2: MUnion'
```
:::
::::

::::exercise (rating := 1) (name := "EmptyStr_not_needed")
It turns out that the `EmptyStr` constructor is actually not
   needed, since the regular expression matching the empty string can
   also be defined from `Star` and `EmptySet`:

```lean
def EmptyStr' {α:Type} := @Star α (EmptySet)
```

State and prove that this `EmptyStr'` definition matches exactly
the same strings as the `EmptyStr` constructor.

:::solution
```lean
theorem empty_equiv {α:Type} (s:List α) :
  s =~ EmptyStr ↔ s =~ EmptyStr' := by

  constructor <;> intro h
  . inversion h; constructor
  . inversion h with
    | MStar0 => constructor
    | MStarApp _ _ h₁ _ => inversion h₁
```
:::
::::

::::full
Since the definition of `ExpMatch]`has a recursive
structure, we might expect that proofs involving regular
expressions will often require induction on evidence.
::::

::::terse
Naturally, proofs about `ExpMatch` often require induction (on evidence!).
::::

For example, suppose we want to prove the following intuitive
fact: If a string `s` is matched by a regular expression `re`,
then all elements of `s` must occur as character literals
somewhere in `re`.

To state this as a theorem, we first define a function `re_chars`
that lists all characters that occur in a regular expression:

```lean
def reChars {α : Type} (re : RegExp α) : List α :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re₁ re₂ => reChars re₁ ++ reChars re₂
  | Union re₁ re₂ => reChars re₁ ++ reChars re₂
  | Star re => reChars re
```

Now, the main theorem:

:::dev
TODO (@dsainati1) : This should be a workinclass
:::

```lean
theorem in_re_match {α : Type} {s : List α} {re : RegExp α} {x : α}
    (hmatch : s =~ re) (hin : x ∈ s) : x ∈ reChars re := by
  induction hmatch with
  | MEmpty => simp at hin
  | MChar c => simp [reChars]; simp at hin; exact hin
  | MApp _ _ _ _ _ _ ih₁ ih₂ =>

  /- Something interesting happens in the `MApp` case.  We obtain
    _two_ induction hypotheses: One that applies when `x` occurs in
    `s₁` (which is matched by `re₁`), and a second one that applies when `x`
    occurs in `s₂` (matched by `re₂`). -/
    simp [reChars] at *
    rcases hin with hin₁ | hin₂
    · left; exact ih₁ hin₁
    · right; exact ih₂ hin₂
  | MUnionL _ _ _ _ ih =>
    simp [reChars]; left; exact ih hin
  | MUnionR _ _ _ h₂ ih =>
    simp [reChars]; right; exact ih hin
  | MStar0 => simp at hin
  | MStarApp _ _ _ _ _ ih₁ ih₂ =>

  /- Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for `ExpMatch`, rather than
    induction on the regular expression `re`: The latter would only
    provide an induction hypothesis for strings that match `re`, which
    would not allow us to reason about the case `In x ∈ s₂`. -/
    simp at hin
    rcases hin with hin₁ | hin₂
    · exact ih₁ hin₁
    · exact ih₂ hin₂
```


::::exercise (rating := 1) (name := "re_not_empty")
Write a recursive function `re_not_empty` that tests whether a
regular expression matches some string. Prove that your function
is correct.

:::solution
```lean
def re_not_empty {α : Type} (re : RegExp α) : Bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re₁ re₂ => re_not_empty re₁ && re_not_empty re₂
  | Union re₁ re₂ => re_not_empty re₁ || re_not_empty re₂
  | Star _ => true

theorem re_not_empty_correct {α : Type} (re : RegExp α) :
    (∃ s, s =~ re) ↔ re_not_empty re = true := by
  induction re with
  | EmptySet =>
    simp [re_not_empty]; intro s h; inversion h
  | EmptyStr =>
    simp [re_not_empty]; exists []; constructor
  | Char x =>
    simp [re_not_empty]; exists [x]; constructor
  | App re₁ re₂ ih₁ ih₂ =>
    simp [re_not_empty]
    constructor
    · rintro ⟨s, h⟩
      inversion h with
      | App s₁ s₂ h₁ h₂ =>
        constructor
        . apply ih₁.mp; exists s₁
        . apply ih₂.mp; exists s₂
    · rintro ⟨h₁, h₂⟩
      obtain ⟨s₁, hs₁⟩ := ih₁.mpr h₁
      obtain ⟨s₂, hs₂⟩ := ih₂.mpr h₂
      exists (s₁ ++ s₂); constructor <;> assumption
  | Union re₁ re₂ ih₁ ih₂ =>
    simp [re_not_empty]
    constructor
    · rintro ⟨s, h⟩
      inversion h with
      | MUnionL h₁ => left; apply ih₁.mp; exists s
      | MUnionR h₂ => right; apply ih₂.mp; exists s
    · rintro (h₁ | h₂)
      · obtain ⟨s, hs⟩ := ih₁.mpr h₁; exists s; constructor; assumption
      · obtain ⟨s, hs⟩ := ih₂.mpr h₂; exists s; apply ExpMatch.MUnionR; assumption
  | Star re _ =>
      simp [re_not_empty]; exists []; constructor
```
:::
::::


## The `generalize` Tactic

One potentially confusing feature of the `induction` tactic is
that it won't let you perform an induction over a term that
isn't sufficiently general. Here's an example:

```lean
/--
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  Star re
-/
#guard_msgs in
example α (s₁ s₂ : List α) (re : RegExp α) :
  s₁ =~ Star re →
  s₂ =~ Star re →
  s₁ ++ s₂ =~ Star re := by
  intro h₁

  /- Now, just doing an `inversion` on `h₁` won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence). We might try this, but Lean won't let us: -/
  induction h₁
```

The problem here is that `induction` over a Prop hypothesis only
works properly with hypotheses that are "fully general," i.e.,
ones in which all the arguments are just variables, as opposed to more
specific expressions like `Star re`.

A possible, but awkward, way to solve this problem is "manually
generalizing" over the problematic expressions by adding
explicit equality hypotheses to the lemma:

```lean
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example α (s₁ s₂ : List α) (re re' : RegExp α) :
  re' = Star re →
  s₁ =~ re' →
  s₂ =~ Star re →
  s₁ ++ s₂ =~ Star re := by

  intro h₁ h₂ h₃
/- We can now proceed by performing induction over evidence
  directly, because the argument to the first hypothesis is
  sufficiently general, which means that we can discharge most cases
  by inverting the `re' = Star re` equality in the context. *)
  This works, but it makes the statement of the lemma a bit ugly.
  Fortunately, there is a better way... -/
  sorry
```

The tactic `generalize h : e = x` causes Lean to (1) replace all
occurrences of the expression `e` by the variable `x`, and (2) add
an equation `h : x = e` to the context.  Here's how we can use it
to show the above result:

```lean
theorem star_app α (s₁ s₂ : List α) (re : RegExp α) :
  s₁ =~ Star re →
  s₂ =~ Star re →
  s₁ ++ s₂ =~ Star re := by

  intros h₁
  generalize heq : Star re = re' at h₁
  -- We now have `heq : Star re = re'`
  -- `heq` is contradictory in most cases, allowing us to conclude immediately via `contradiction`
  induction h₁ <;> try contradiction
  -- The interesting cases are those that correspond to `Star`
  case MStar0 _ => intro h₂; simp; exact h₂
  case MStarApp _ _ _ _ _ _ ih₂ =>
    injections heq; subst heq
    intro h₂; simp
    apply ExpMatch.MStarApp
    . assumption
    . apply ih₂ <;> trivial
  /- Note that the induction hypothesis `ih₂` on the `MStarApp` case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by `generalize`. -/
```

::::exercise (rating := 1) (name := "exp_match_ex2")
The `MStar''` lemma below (combined with its converse, the
`MStar'` exercise above), shows that our definition of `ExpMatch`
for `Star` is equivalent to the informal one given previously.

```lean
theorem MStar'' α (s : List α) (re : RegExp α) :
  s =~ Star re →
  exists ss : List (List α),
    s = List.foldr (· ++ ·) [] ss
    ∧ ∀ s', s' ∈ ss → s' =~ re := by
  solution!
    intro h
    generalize heq : Star re = re' at h
    induction h <;> try trivial
    case MStar0 ih =>
      exists []; simp
    case MStarApp s₁ s₂ re h₁ h₂ ih₁ ih₂ =>
      injections heq; subst heq
      obtain ⟨ss, hfold, hall⟩ := ih₂ rfl
      exists (s₁ :: ss); simp; rw [←hfold]
      repeat
        constructor
        trivial
      intro s h; apply hall; trivial
```
::::

## The "Weak" Pumping Lemma

One of the first really interesting theorems in the theory of
regular expressions is the so-called _pumping lemma_, which
states, informally, that any sufficiently long string `s` matching
a regular expression `re` can be "pumped" by repeating some middle
section of `s` an arbitrary number of times to produce a new
string also matching `re`.  For the sake of simplicity, this
exercise considers a slightly weaker theorem than is usually
stated in courses on automata theory -- hence the name
`weak_pumping`.  The stronger one can be found below.

To get started, we need to define "sufficiently long."  Since we
are working in a constructive logic, we actually need to be able
to _calculate_, for each regular expression `re`, a minimum length
for strings `s` to guarantee "pumpability."

```lean
namespace Pumping

def pumpingConstant {α : Type} (re : RegExp α) : Nat :=
  match re with
  | RegExp.EmptySet => 1
  | RegExp.EmptyStr => 1
  | RegExp.Char _ => 2
  | RegExp.App re₁ re₂ => pumpingConstant re₁ + pumpingConstant re₂
  | RegExp.Union re₁ re₂ => pumpingConstant re₁ + pumpingConstant re₂
  | RegExp.Star r => pumpingConstant r
```

You may find these lemmas about the pumping constant useful when
proving the pumping lemma below.

```lean
theorem pumping_constant_ge_1 {α : Type} (re : RegExp α) :
    pumpingConstant re ≥ 1 := by
  induction re with
  | EmptySet => simp [pumpingConstant]
  | EmptyStr => simp [pumpingConstant]
  | Char _ => simp [pumpingConstant]
  | App re₁ _ ih1 _ => simp [pumpingConstant]; lia
  | Union re₁ _ ih1 _ => simp [pumpingConstant]; lia
  | Star _ ih => simp [pumpingConstant]; exact ih

theorem pumping_constant_0_false {α : Type} (re : RegExp α)
    (h : pumpingConstant re = 0) : False := by
  have := pumping_constant_ge_1 re; lia
```

Next, it is useful to define an auxiliary function that repeats a
string (appends it to itself) some number of times.

```lean
def napp {α : Type} (n : Nat) (l : List α) : List α :=
  match n with
  | 0 => []
  | n' + 1 => l ++ napp n' l
```

These auxiliary lemmas might also be useful in your proof of the
pumping lemma.

```lean
theorem napp_plus {α : Type} (n m : Nat) (l : List α) :
    napp (n + m) l = napp n l ++ napp m l := by
  induction n with
  | zero => simp [napp]
  | succ n ih => simp [Nat.succ_add, napp, ih]

theorem napp_star {α : Type} (m : Nat) (s₁ s₂ : List α) (re : RegExp α)
    (hs1 : s₁ =~ re) (hs₂ : s₂ =~ RegExp.Star re) :
    napp m s₁ ++ s₂ =~ RegExp.Star re := by
  induction m with
  | zero => simp [napp]; exact hs₂
  | succ m ih =>
    simp only [napp]
    rw [List.append_assoc]
    apply ExpMatch.MStarApp <;> trivial
```

The (weak) pumping lemma itself says that, if `s =~ re` and if the
length of `s` is at least the pumping constant of `re`, then `s`
can be split into three substrings `s₁ ++ s₂ ++ s₃` in such a way
that `s₂` can be repeated any number of times and the result, when
combined with `s₁` and `s₃`, will still match `re`.  Since `s₂` is
also guaranteed not to be the empty string, this gives us
a (constructive!) way to generate strings matching `re` that are
as long as we like.

This proof is quite long, so to make it more tractable we've
broken it up into a number of sub-proofs, which we then assemble
to prove the main lemma.

Your job is to complete the proofs of the helper lemmas; the main
lemma relies on these. Several of the lemmas about `Nat.ble` that were
in an optional exercise earlier in the `IndProp` chapter may be useful here
-- in particular, `lt_ge_cases` and `plus_le`

::::exercise (rating := 2) (name := "weak_pumping_char")
```lean
theorem weak_pumping_char {α : Type} (x : α) :
  pumpingConstant (Char x) <= [x].length →
  ∃ s₁ s₂ s₃ : List α,
    [x] = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [ ] ∧
    (∀ m : Nat, s₁ ++ napp m s₂ ++ s₃ =~ Char x) := by
  solution!
    intro contra
    simp [pumpingConstant] at contra
```
::::

::::exercise (rating := 4) (name := "weak_pumping_app")
```lean
theorem weak_pumping_app {α : Type}
                         (s₁ s₂ : List α) (re₁ re₂ : RegExp α) :
  s₁ =~ re₁ →
  s₂ =~ re₂ →
  (pumpingConstant re₁ <= s₁.length →
  ∃ s₂ s₃ s₄ : List α,
    s₁ = s₂ ++ s₃ ++ s₄ ∧
    s₃ ≠ [ ] ∧
    (∀ m : Nat, s₂ ++ napp m s₃ ++ s₄ =~ re₁)) →
  (pumpingConstant re₂ <= s₂.length →
    ∃ s₁ s₃ s₄ : List α,
      s₂ = s₁ ++ s₃ ++ s₄ ∧
      s₃ ≠ [ ] ∧
      (∀ m : Nat, s₁ ++ napp m s₃ ++ s₄ =~ re₂)) →
  pumpingConstant (App re₁ re₂) <= (s₁ ++ s₂).length →
  ∃ s₀ s₃ s₄ : List α,
    s₁ ++ s₂ = s₀ ++ s₃ ++ s₄ ∧
    s₃ ≠ [ ] ∧
    (∀ m : Nat, s₀ ++ napp m s₃ ++ s₄ =~ App re₁ re₂) := by
  intro hmatch₁ Hmatch2 ih₁ ih₂ Hlen
  obtain H | H :
    pumpingConstant re₁ <= s₁.length ∨ pumpingConstant re₂ <= s₂.length := by
    solution!
      rw [app_length] at Hlen
      apply add_le_cases
      apply Hlen
  . solution!
      specialize ih₁ H
      let ⟨s₁₂, s₁₃, s₁₄, h₁, h₂, h₃⟩ := ih₁
      rw [h₁]
      exists s₁₂; exists s₁₃; exists (s₁₄ ++ s₂)
      constructor
      . simp
      constructor
      . assumption
      . intro m; specialize h₃ m
        rw [←List.append_assoc]
        constructor <;> trivial
  . solution!
      specialize ih₂ H
      let ⟨s₂₁, s₂₂, s₂₃, h₁, h₂, h₃⟩ := ih₂
      rw [h₁]
      exists (s₁ ++ s₂₁); exists s₂₂; exists s₂₃
      constructor
      . rw [←List.append_assoc, ←List.append_assoc]
      constructor
      . assumption
      . intro m; specialize h₃ m
        rw [List.append_assoc, List.append_assoc]
        constructor
        assumption
        rw [←List.append_assoc]
        assumption
```
::::

::::exercise (rating := 3) (name := "weak_pumping_union_l")
```lean
theorem weak_pumping_union_l :  ∀ {α : Type} (s₁ : List α) (re₁ re₂ : RegExp α),
  s₁ =~ re₁ →
  (pumpingConstant re₁ <= s₁.length →
    ∃ s₂ s₃ s₄ : List α,
      s₁ = s₂ ++ s₃ ++ s₄ ∧
      s₃ ≠ [ ] ∧
      (∀ m : Nat, s₂ ++ napp m s₃ ++ s₄ =~ re₁)) →
  pumpingConstant (Union re₁ re₂) <= s₁.length →
  ∃ s₀ s₂ s₃ : List α,
    s₁ = s₀ ++ s₂ ++ s₃ ∧
    s₂ ≠ [ ] ∧
    (∀ m : Nat, s₀ ++ napp m s₂ ++ s₃ =~ Union re₁ re₂) := by
  intro α s₁ re₁ re₂ Hmatch IH Hlen
  have H : pumpingConstant re₁ <= s₁.length := by
    solution!
      simp [pumpingConstant] at Hlen
      lia
  solution!
    specialize IH H
    let ⟨s₁₁, s₁₂, s₁₃, h₁, h₂, h₃⟩ := IH
    exists s₁₁; exists s₁₂; exists s₁₃
    constructor
    . assumption
    constructor
    . assumption
    . intro m; specialize h₃ m
      apply ExpMatch.MUnionL
      assumption
```
::::

::::exercise (rating := 3) (name := "weak_pumping_union_r")
```lean
theorem weak_pumping_union_r {α : Type} (s₂ : List α) (re₁ re₂ : RegExp α) :
  s₂ =~ re₂ →
  (pumpingConstant re₂ <= s₂.length →
    ∃ s₁ s₃ s₄ : List α,
      s₂ = s₁ ++ s₃ ++ s₄ ∧
      s₃ ≠ [ ] ∧
      (∀ m : Nat, s₁ ++ napp m s₃ ++ s₄ =~ re₂)) →
  pumpingConstant (Union re₁ re₂) <= s₂.length →
  ∃ s₁ s₀ s₃ : List α,
    s₂ = s₁ ++ s₀ ++ s₃ ∧
    s₀ ≠ [ ] ∧
    (∀ m : Nat, s₁ ++ napp m s₀ ++ s₃ =~ Union re₁ re₂) := by
  -- symmetric to the previous
  intro Hmatch IH Hlen
  have H : pumpingConstant re₂ <= s₂.length := by
   solution!
      simp [pumpingConstant] at Hlen
      lia
  solution!
    specialize IH H
    let ⟨s₂₁, s₂₂, s₂₃, h₁, h₂, h₃⟩ := IH
    exists s₂₁; exists s₂₂; exists s₂₃
    constructor
    . assumption
    constructor
    . assumption
    . intro m; specialize h₃ m
      apply ExpMatch.MUnionR
      assumption
```
::::

::::exercise (rating := 2) (name := "weak_pumping_star_zero")
```lean
theorem weak_pumping_star_zero {α : Type} (re : RegExp α) :
  pumpingConstant (Star re) <= @List.length α [] →
  ∃ s₁ s₂ s₃ : List α,
    [ ] = s₁ ++ s₂ ++ s₃ ∧
    s₂ ≠ [ ] ∧
    (∀ m : Nat, s₁ ++ napp m s₂ ++ s₃ =~ Star re) := by
  solution!
    intro Hp
    simp only [List.length_nil] at Hp
    inversion Hp with
    | refl h h₁ =>
      have h2 := pumping_constant_ge_1 re
      rw [←h₁] at h2; inversion h2
```
::::

::::exercise (rating := 5) (name := "weak_pumping_star_app")
```lean
theorem weak_pumping_star_app : ∀ {α : Type}  (s₁ s₂ : List α) (re : RegExp α),
  s₁ =~ re →
  s₂ =~ .Star re →
  (pumpingConstant re <= List.length s₁ →
    ∃ s₂ s₃ s₄ : List α,
      s₁ = s₂ ++ s₃ ++ s₄
      ∧ s₃  ≠ [ ] ∧
      (∀ m : Nat, s₂ ++ napp m s₃ ++ s₄ =~ re)) →
  (pumpingConstant (Star re) <= s₂.length →
    ∃ s₁ s₃ s₄ : List α,
      s₂ = s₁ ++ s₃ ++ s₄ ∧
      s₃  ≠ [ ] ∧
      (∀ m : Nat, s₁ ++ napp m s₃ ++ s₄ =~ Star re)) →
  pumpingConstant (Star re) <= (s₁ ++ s₂).length →
  ∃ s₀ s₃ s₄ : List α,
    s₁ ++ s₂ = s₀ ++ s₃ ++ s₄ ∧
    s₃  ≠ [ ] ∧
    (∀ m : Nat, s₀ ++ napp m s₃ ++ s₄ =~ .Star re)  := by
  intro T s₁ s₂ re hmatch₁ hmatch₂ ih₁ ih₂ Hlen
  rw [app_length] at *
  obtain Hs1len0 | ⟨s1len, Hs1re1⟩ | Hs1re1 :
    (s₁.length = 0
      ∨ (s₁.length ≠ 0 ∧ s₁.length < pumpingConstant re)
      ∨ pumpingConstant re <= s₁.length) := by
    cases s₁
    . solution!
        left; rfl
    . case cons h s1' =>
      solution!
        right
        have Hcases : (List.length (h :: s1') < pumpingConstant re
                      ∨ pumpingConstant re <= List.length (h :: s1')) := by
          apply lt_ge_cases
        cases Hcases
        . left; constructor
          . intro contra
            contradiction
          . assumption
        . right; assumption
  . solution!
      have Hs1nil : s₁ = [] := by
        cases s₁; rfl; contradiction
      subst Hs1nil
      simp at Hlen
      apply ih₂; apply Hlen
  . solution!
      exists []; exists s₁; exists s₂
      constructor; rfl
      constructor
      . intro contra; subst contra; contradiction
      . intro m; apply napp_star
        assumption
        assumption
  . solution!
      specialize ih₁ Hs1re1
      let ⟨s₁₁, s₁₂, s₁₃, h₁, h₂, h₃⟩ := ih₁
      exists s₁₁; exists s₁₂; exists (s₁₃ ++ s₂)
      rw [h₁]
      constructor
      . simp
      constructor
      . assumption
      . intro m; specialize h₃ m
        rw [←List.append_assoc]
        apply ExpMatch.MStarApp
        . assumption
        . assumption
```
::::

::::exercise (rating := 3) (name := "weak_pumping")
```lean
theorem weak_pumping {α : Type} {re : RegExp α} {s : List α}
    (hmatch : s =~ re) (hlen : pumpingConstant re ≤ s.length) :
    ∃ s₁ s₂ s₃ : List α,
      s = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [] ∧
      ∀ m, s₁ ++ napp m s₂ ++ s₃ =~ re := by
  solution!
    induction hmatch
    . simp [pumpingConstant] at hlen
    . apply weak_pumping_char; assumption
    . apply weak_pumping_app <;> assumption
    . apply weak_pumping_union_l <;> assumption
    . apply weak_pumping_union_r <;> assumption
    . apply weak_pumping_star_zero <;> assumption
    . apply weak_pumping_star_app <;> assumption
```
::::


## The (Strong) Pumping Lemma

:::dev
TODO (DHS): If this exercise is going to be optional we should still fill in the
solution but it's lower priority.
:::

::::exercise (rating := 10) (name := "weak_pumping")
Now here is the usual version of the pumping lemma. In addition to
requiring that `s₂ <> []`, it also strengthens the result to
include the claim that `length s₁ + length s₂ <= pumping_constant re`.

```lean
theorem pumping {α : Type} {re : RegExp α} {s : List α}
    (_hmatch : s =~ re) (_hlen : pumpingConstant re ≤ s.length) :
    ∃ s₁ s₂ s₃ : List α,
      s = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [] ∧
      s₁.length + s₂.length ≤ pumpingConstant re ∧
      ∀ m, s₁ ++ napp m s₂ ++ s₃ =~ re := by
  sorry
```
::::

```lean
end Pumping
end RegExp
```
