import SFLMeta
import LF.IndProp

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "ProofObjects: The Curry-Howard Correspondence" =>
%%%
tag := "ProofObjects"
htmlSplit := .never
file := some "ProofObjects"
%%%

```lean -show
-- This setting is enabled to make some tricky mistakes harder to make.
set_option autoImplicit false
```

:::epigraph
"Algorithms are the computational content of proofs."
(Robert Harper)
:::

::::terse
Programming and proving in Lean are two sides of the same coin.
Proofs manipulate evidence much as programs manipulate data.
::::

::::full
We have seen that Lean has mechanisms both for _programming_,
using inductive data types like {name}`Nat` or {name}`List` and functions over
these types, and for _proving_ properties of these programs, using
inductive propositions (like {name}`Even`), implication, universal
quantification, and the like.  So far, we have mostly treated
these mechanisms as if they were quite separate, and for many
purposes this is a good way to think.  But we have also seen hints
that Lean's programming and proving facilities are closely related.
For example, the keyword `inductive` is used to declare both data
types and propositions, and `→` is used both to describe the type
of functions on data and logical implication.  This is not just a
syntactic accident!  In fact, programs and proofs in Lean are
almost the same thing.  In this chapter we will study this connection
in more detail.

We have already seen the fundamental idea: provability in Lean is
always witnessed by _evidence_.  When we construct the proof of a
basic proposition, we are actually building a tree of evidence,
which can be thought of as a concrete data structure.

If the proposition is an implication like `A → B`, then its proof
is an evidence _transformer_: a recipe for converting evidence for
A into evidence for B.  So at a fundamental level, proofs are
simply programs that manipulate evidence.
::::

Question: If evidence is data, what are propositions themselves?

Answer: They are types!

:::slidebreak
:::

Look again at the formal definition of the {name}`Even` property.
For illustrative purposes, we've made the implicit argument `{n : Nat}` to {name}`Even.succ_succ`
explicit.

```lean
namespace EvenProp
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ (n : Nat) (h : Even n) : Even (n + 2)
```

We can pronounce the ":" here as either "has type" or "is a proof of."
For example, the second line in the definition of {name}`Even`
declares that {lean}`(Even.zero : Even 0)`.  Instead of
"{name}`Even.zero` has type {lean}`Even 0`," we can say that
"{name}`Even.zero` is a proof of {lean}`Even 0`."

:::slidebreak
:::

This pun between types and propositions — between `:` as "has type"
and `:` as "is a proof of" or "is evidence for" — is called the
_Curry-Howard correspondence_.  It proposes a deep connection
between the world of logic and the world of computation:

```display +centered
propositions  ~  types
proofs        ~  programs
```

See {citet Bib.wadler2015}[] for a brief history and modern exposition.

:::slidebreak
:::

Many useful insights follow from this connection. To begin with,
it gives us a natural interpretation of the type of the {name}`Even.succ_succ`
constructor.

The type of {name}`Even.succ_succ`
says that it is a _function_ (better: a data _constructor_) taking two arguments (one number
`n` plus evidence for `Even n`) and returning evidence that `n + 2` is even.

```lean (name := check_succ_succ)
#check @Even.succ_succ
```

```leanOutput check_succ_succ
Even.succ_succ : ∀ (n : Nat), Even n → Even (n + 2)
```

This can be read "{name}`Even.succ_succ` is a constructor that takes two
arguments — a number `n` and evidence for the proposition `Even n` — and yields evidence for the proposition `Even (n + 2)`."

:::slidebreak
:::

Now let's look again at an earlier proof involving {name}`Even`.

```lean
theorem even_4 : Even 4 := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply Even.zero
```

Just as with ordinary data values and functions, we can use the
`#print` command to see the _proof object_ that results from this
proof script.

```lean (name := print_even_4)
#print even_4
```

```leanOutput print_even_4
theorem EvenProp.even_4 : Even 4 :=
Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

:::slidebreak
:::

Indeed, we can also write down this proof object directly,
with no need for a proof script at all:

```lean (name := check_even_4_term)
#check (Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
  : Even (2 + 2))
```

```leanOutput check_even_4_term
Even.succ_succ 2 (Even.succ_succ 0 Even.zero) : Even (2 + 2)
```

::::full
The expression {lean}`Even.succ_succ 2 (Even.succ_succ 0 Even.zero)` instantiates the
parameterized constructor {name}`Even.succ_succ` with the specific arguments {lean}`2`
and {lean}`0` plus the corresponding proof objects for its premises {lean}`Even 2` and {lean}`Even 0`.  Alternatively, we can think of {name}`Even.succ_succ` as a
primitive "evidence constructor" that, when applied to a
particular number, wants to be further applied to evidence that
this number is even; its type,

```display +centered
∀ (n : Nat), Even n → Even (n + 2)
```

expresses this functionality, in the same way that the polymorphic
type {lean}`{α : Type} → List α` expresses the fact that the constructor
{name}`List.nil` can be thought of as a function from types to empty lists
with elements of that type.

The fact that some arguments are implicit, like `{α}` of {lean}`List`
and `{n}` of the real {name}`Even.succ_succ`, actually doesn't make a difference at all:
{name}`List` is still taking one argument, and {name}`Even.succ_succ` is still taking two.
Implicit arguments are just a usability feature that tells Lean to figure some arguments
out when we apply a definition (like {name}`Even.succ_succ`) to an explicit argument
(like a proof of `Even n`). In this case, since `Even n` contains `n`, we don't need to pass `n` in to
begin with, and can mark it as implicit with the curly braces as `{n}`.

We saw in the {ref "Logic"}[Logic] chapter that we can use function
application syntax to instantiate universally quantified variables
in lemmas, as well as to supply evidence for assumptions that
these lemmas impose.  For instance:
::::

::::terse
Similarly, as we've seen, we can directly apply theorems to
arguments in proof scripts:
::::

```lean
theorem even_4' : Even 4 := by
  apply Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

# Proof Scripts

::::full
The _proof objects_ we've been discussing lie at the core of how
Lean operates.  When Lean is following a proof script, what is
happening internally is that it is gradually constructing a proof
object — a term whose type is the proposition being proved. All the
tactics following `by` tell it how to build up a term
of the required type.  To see this process in action, we provide
a `show_proof` tactic to display the current state of the proof
tree at various points in the following tactic proof.

`show_proof` wraps a tactic script and prints the partial proof term —
a term with _holes_ where the remaining proof obligations are —
before and after each step. A term's holes are shown as `?_`.

::::

::::terse
When we write a proof using tactics, what we are doing is
instructing Lean to build a proof object under the hood.  We can
see this using the custom tactic `show_proof`:
::::

::::details "Tactic: show_proof"
```lean
section ShowProof
open Lean Elab Tactic Meta

/-- Like `instantiateMVars`, but also substitutes holes
whose assignment Lean delays until they are complete
(e.g., the body under an `intro`). -/
partial def instantiatePartial (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  transform e (pre := fun e => do
    let .mvar m := e.getAppFn | return .continue
    let some d ← getDelayedMVarAssignment? m
      | return .continue
    let v ← instantiatePartial (mkMVar d.mvarIdPending)
    let args := e.getAppArgs
    let n := d.fvars.size
    let v :=
      (v.abstract d.fvars).instantiateRevRange 0 n args
    return .done (mkAppN v args[n:]))

/-- `show_proof tac₁ … tacₙ` runs the tactics in order,
printing the partial proof term (with `?_` for unfilled
holes) before the first tactic and after each one. -/
elab "show_proof" seq:tacticSeq : tactic => do
  let root ← getMainGoal
  let s := seq.raw[0]
  let tacs :=
    if s.getKind == ``Parser.Tactic.tacticSeqBracketed then
      s[1].getSepArgs
    else s[0].getSepArgs
  let render : TacticM Format := do
    let e ← instantiatePartial (mkMVar root)
    withOptions
      (fun o => (o.setBool `pp.mvars false).setBool
        `pp.fieldNotation false)
      (ppExpr e)
  let mut out ← render
  for t in tacs do
    evalTactic t
    let tac ← PrettyPrinter.ppTactic ⟨t⟩
    out := out ++ .line ++ .line ++ f!"after {tac}:" ++
      .nest 2 (.line ++ (← render))
  logInfo m!"{out}"

end ShowProof
```
::::

```lean (name := even_4_show_proof)
theorem even_4'' : Even 4 := by
  show_proof
    apply Even.succ_succ
    apply Even.succ_succ
    apply Even.zero
```

```leanOutput even_4_show_proof
?_

after apply Even.succ_succ:
  Even.succ_succ 2 ?_

after apply Even.succ_succ:
  Even.succ_succ 2 (Even.succ_succ 0 ?_)

after apply Even.zero:
  Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

::::full
At any given moment, Lean has constructed a term with a
"hole" (indicated by `?_` here, and so on), and it knows what
type of evidence is needed to fill this hole.

Each hole corresponds to a subgoal, and the proof is
finished when there are no more subgoals.  At this point, the
evidence we've built is stored in the global context (i.e. Lean's
environment that it uses for type-checking) under the name
given in the `theorem` command.
::::

:::slidebreak
:::

Tactic proofs are convenient, but they are not essential in Lean:
in principle, we can always just construct the required evidence
by hand. Then we can write a proof term directly following a `:=`
(instead of writing `by` and then tactics)
to introduce a global name for this evidence.

```lean
theorem even_4''' : Even 4 :=
  Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

::::::full
All these different ways of building the proof lead to exactly the
same evidence being saved in the global environment.

```lean (name := print_all_even_4)
#print even_4
#print even_4'
#print even_4''
#print even_4'''
```

```leanOutput print_all_even_4
theorem EvenProp.even_4 : Even 4 :=
Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

```leanOutput print_all_even_4
theorem EvenProp.even_4' : Even 4 :=
Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

```leanOutput print_all_even_4
theorem EvenProp.even_4'' : Even 4 :=
Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

```leanOutput print_all_even_4
theorem EvenProp.even_4''' : Even 4 :=
Even.succ_succ 2 (Even.succ_succ 0 Even.zero)
```

:::::exercise (rating := 2) (name := "eight_is_even")
Give a tactic proof and a proof object showing that {lean}`Even 8`.

```lean
theorem even_8_tactics : Even 8 := by
  solution!
    apply Even.succ_succ
    apply Even.succ_succ
    apply even_4

theorem even_8_term : Even 8 :=
  solution!(Even.succ_succ 6 (Even.succ_succ 4 even_4))
```

:::gradeTheorem 1 even_8_tactics
:::

:::gradeTheorem 1 even_8_term
:::
:::::

::::::

# Quantifiers, Implications, Functions

In Lean's computational universe (where data structures and
programs live), there are two sorts of values that have arrows in
their types: _constructors_ introduced by `inductive`ly defined
data types, and _functions_.

Similarly, in Lean's logical universe (where we carry out proofs),
there are two ways of giving evidence for an implication:
constructors introduced by `inductive`ly defined propositions,
and... functions!

:::slidebreak
:::

For example, consider this statement:

```lean
theorem even_plus4 (n : Nat) (h : Even n) :
    Even (n + 4) := by
  apply Even.succ_succ
  apply Even.succ_succ
  apply h
```

What is the proof object corresponding to {name}`even_plus4`?

:::slidebreak
:::

We're looking for an expression whose _type_ is {lean}`∀ (n : Nat), Even n → Even (n + 4)` — that is, a _function_ that takes two arguments (one
number and a piece of evidence) and returns a piece of evidence!

Here it is:

```lean
theorem even_plus4' : ∀ (n : Nat), Even n → Even (n + 4) :=
  fun (n : Nat) => fun (h : Even n) =>
    Even.succ_succ (n + 2) (Even.succ_succ n h)
```

::::full
Recall that `fun n => blah` means "the function that, given `n`,
yields `blah`," and that Lean treats `n + 4` and `n + 2 + 2`
as synonyms. Another equivalent way to write this definition is:
::::

::::terse
Or equivalently:
::::

```lean
theorem even_plus4'' (n : Nat) (h : Even n) :
    Even (n + 4) :=
  Even.succ_succ (n + 2) (Even.succ_succ n h)

#check (even_plus4'' : ∀ (n : Nat), Even n → Even (n + 4))
```

:::slidebreak
:::

## Dependency, Equivalence, and Proof Irrelevance
%%%
tag := "proof-irrelevance"
%%%

When we view the proposition being proved by {name}`even_plus4` as a
function type, one interesting point becomes apparent: The second
argument's type, `Even n`, mentions the _value_ of the first
argument, `n`.

While such _dependent types_ are not found in most mainstream
programming languages, they can be quite useful in programming
too, as the flurry of activity in the functional programming
community over the past couple of decades
(and recently, most notably Lean!) demonstrates.
Dependent types sit at the "highest corner" of the Lambda Cube
(see the `Stlc` chapter of _Type Systems_): types can depend on _values_
in addition to other types.

:::slidebreak
:::

Notice that both implication (`→`) and quantification (`∀`)
correspond to functions on evidence.  In fact, they are really the
same thing: `→` is just a shorthand for a degenerate use of
`∀` where there is no dependency, i.e., no need to give a
name to the type on the left-hand side of the arrow:

```display +centered
   ∀ (x : Nat), Nat
=  ∀ (_ : Nat), Nat
=  Nat        → Nat
```

::::full

For example, consider this proposition:

```lean
def even_plus2 : Prop :=
  ∀ (n : Nat), ∀ (E : Even n), Even (n + 2)
```

A proof term inhabiting this proposition would be a function
with two arguments: a number `n` and some evidence `E` that `n` is
even.  But the name `E` for this evidence is not used in the rest
of the statement of {name}`even_plus2`, so it's a bit silly to bother
making up a name for it.  We could write it like this instead,
using the dummy identifier `_` in place of a real name:

```lean
def even_plus2' : Prop :=
  ∀ (n : Nat), ∀ (_ : Even n), Even (n + 2)
```

Or, equivalently, we can write it in a different, familiar way:

```lean
def even_plus2'' : Prop :=
  ∀ (n : Nat), Even n → Even (n + 2)
```

In general, "`P → Q`" is just syntactic sugar for
"`∀ (_ : P), Q`".

When we write theorem statements in Lean, we often _will_
name the quantified evidence with a name often beginning with `h`:

```lean
theorem even_plus2_thm :
  ∀ (n : Nat) (heven : Even n), Even (n + 2) := by
    intro n h; constructor; assumption
```

And we will also put the names before the `:`, which saves needing to
use {tactic}`intro`:
```lean
theorem even_plus2_thm' (n : Nat) (heven : Even n) :
    Even (n + 2) := by
    constructor; assumption
```

_All_ of these theorem statements are equivalent! When we write `def`,
we are just writing down the statement — the type. When we write
`theorem`, we are stating the type and then providing a witness after
the `:=` (either with `by` and tactics or directly with a term). We
can even show the two definitions are equivalent in Lean itself:

```lean
theorem even_plus2_defs_same :
    even_plus2 = even_plus2'' := by rfl
```
Remember that theorem statements are just types, so {name}`rfl` here is just
comparing two types.

What about the two theorems? Here, we are asking if two _proofs_ — which we now know
are both _functions_ — are equal. Then, do we need to use {tactic}`funext`?

```lean
theorem even_plus2_theorems_same :
    even_plus2_thm = even_plus2_thm' := by rfl
```

Surprisingly, we don't. This is because Lean has a special feature
called _definitional proof irrelevance_. It says that any two proofs
of the same proposition are definitionally equal. So we could write
the same proof again however we wanted — with different tactics, using
terms instead of tactics, etc. — and we would still have "the same
theorem."

```lean
theorem even_plus2_thm'' (n : Nat) (heven : Even n) :
    Even (n + 2) := by
    exact Even.succ_succ n heven

theorem even_plus2_theorems_still_same :
  even_plus2_thm = even_plus2_thm'' := by rfl
```

::::

:::::quiz
Recall the definition of {name}`Even`:

```display +centered
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ (n : Nat) (h : Even n) : Even (n + 2)
```

What is the type of this expression?

```display +centered
fun (n : Nat) =>
  fun (h : Even n) =>
     Even.succ_succ (n + 2) (Even.succ_succ n h)
```

(A) {lean}`∀ (n : Nat), Even n`

(B) {lean}`∀ (n : Nat), Even (n + 2)`

(C) {lean}`∀ (n : Nat), Even n → Even n`

(D) {lean}`∀ (n : Nat), Even n → Even (n + 2)`

(E) {lean}`∀ (n : Nat), Even n → Even (n + 4)`

(F) Not typeable

:::quizSolution
(E)
```lean
#check (fun (n : Nat) =>
          fun (h : Even n) =>
            Even.succ_succ (n + 2) (Even.succ_succ n h)
        : ∀ (n : Nat), Even n → Even (n + 4))
```
:::
:::::

# Programming with Tactics

:::suppressPreviousHeaderWhenTerse
:::

::::full
If we can build proofs by giving explicit terms rather than
executing tactic scripts, you may wonder whether we can build
_programs_ using tactics rather than by writing down explicit
terms.

Naturally, the answer is yes!

```lean (name := add2_show_proof)
def add2 : Nat → Nat := by
  show_proof
    intro n
    apply Nat.succ
    apply Nat.succ
    exact n
```

```leanOutput add2_show_proof
?_

after intro n:
  fun n => ?_

after apply Nat.succ:
  fun n => Nat.succ ?_

after apply Nat.succ:
  fun n => Nat.succ (Nat.succ ?_)

after exact n:
  fun n => Nat.succ (Nat.succ n)
```

```lean (name := print_add2)
#print add2
```

```leanOutput print_add2
def EvenProp.add2 : Nat → Nat :=
fun n => n.succ.succ
```

```lean (name := eval_add2)
#eval add2 2
```

```leanOutput eval_add2
4
```

Notice that we followed `def … :=` with `by` rather than
with a term.  This tells Lean to enter _proof
scripting mode_ to build an object of type {lean}`Nat → Nat`.

This feature is mainly useful for writing functions with dependent
types, which we won't explore much further in this book.  But it
does illustrate the uniformity and orthogonality of the basic
ideas in Lean.

:::dev "Michael Hicks (mwhicks1)"
This statement is a bit mysterious. Why are dependent types special?
I think the answer is that they allow for more explicit specifications --
normal types are just not strong enough to say much about a function you might
ask tactics to synthesize. There are lots of Nat -> Nat functions,
but far fewer that ... insert dependent type here.
:::

Since `def` and `theorem` can both use terms or `by`, is there any difference between the two?
There is one: a `theorem` must have a {lean}`Prop` type.

```lean +error -keep (name := add2_theorem_wrong)
theorem add2_with_theorem_wrong : Nat → Nat := by
    apply Nat.succ
```

```leanOutput add2_theorem_wrong
type of theorem `EvenProp.add2_with_theorem_wrong` is not a proposition
  Nat → Nat
```
::::

# Building Proof Objects Incrementally (Optional)

:::suppressPreviousHeaderWhenTerse
:::

```lean -show
section IncrementalProofObjects
set_option warn.sorry false
```

::::full
As you probably noticed while solving the exercises earlier in the
chapter, constructing proof objects is more involved than
constructing the corresponding tactic proofs. Fortunately, there's
a simple trick to help in the construction: we can use the _term_
{lean}`sorry` as a placeholder of any type we like.

As an example, let's walk through the process of constructing a
proof object demonstrating the evenness of {lean}`8`.

```lean
theorem even_8_atmpt_1 : Even 8 := sorry
```

Maybe we can use {name}`Even.succ_succ` to construct a term of type {lean}`Even 8`?
Recall that {name}`Even.succ_succ` is of type

```display +centered
∀ (n : Nat), Even n → Even (n + 2)
```

If we can demonstrate that {lean}`6` is even, we should be done.

```lean
theorem even_8_atmpt_2 : Even 8 := Even.succ_succ 6 sorry
```

In the attempt above, we've omitted the proof that {lean}`6` is even,
but it can easily be constructed following the same procedure:

```lean
theorem even_8_atmpt_3 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4 sorry)

theorem even_8_atmpt_4 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4
    (Even.succ_succ 2 sorry))

theorem even_8_atmpt_5 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4
    (Even.succ_succ 2 (Even.succ_succ 0 Even.zero)))
```

To recap, we've been guided by an informal proof that we have in
our minds, and we check the high-level details before completing
the intricacies of the proof. The {lean}`sorry` term allows us to do
this.
::::

```lean -show
end IncrementalProofObjects
```

# Practical Uses of Terms in Proofs

In the {name}`Even` examples, we show how to build proofs using terms to
illustrate that they are one and the same. But in the most recent
example, doing so is impractical: the proof terms are
verbose and arguably harder to write and follow than a tactic proof.
So the question naturally arises — would we
ever use terms in _real_ Lean proofs? The answer is yes, and we show
some examples where such use is helpful, and indeed actively encouraged
in real Lean developments.

Here are some of the places where terms most often appear in Lean proofs:

1. {lean}`rfl`: The _term_ {lean}`rfl` is used very often as a full proof instead of
`by rfl` (which references the _tactic_ {tactic}`rfl` of the same name)
and is even preferred in Lean's Mathlib, which writes its
`@[simp]` definitional lemmas this way.
```lean
theorem two_add_two : 2 + 2 = 4 := rfl

@[simp]
theorem length_cons {α : Type} (x : α) (xs : List α) :
    (x :: xs).length = xs.length + 1 := rfl
```

2. To succinctly apply an existing lemma, possibly via dot notation on proofs
```lean
theorem add_comm_flip (a b : Nat) : b + a = a + b := Nat.add_comm b a
theorem le_chain {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂
```

3. Within anonymous constructors and projections for
   {name}`And` (`∧`), {name}`Iff` (`↔`), and {name}`Exists` (`∃`)

```lean
theorem and_swap {P Q : Prop} (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
theorem iff_swap {P Q : Prop} (h : P ↔ Q) : Q ↔ P := ⟨h.2, h.1⟩
theorem exists_double : ∃ n, n + n = 4 := ⟨2, rfl⟩
```

4. `fun` for implications (as in {lean}`even_plus4'`)
```lean
theorem imp_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) :
    P → R :=
  fun hp => hqr (hpq hp)
```

5. Proof fields of structures/instances (as in {ref "Typeclasses"}[Typeclasses]' Monoid laws)
```lean
structure PosNat where
  val : Nat
  pos : 0 < val
def three : PosNat where
  val := 3
  pos := Nat.succ_pos 2
```

Using terms in proofs can be
more succinct and more useful than writing out tactics.
Try out using terms like {name}`rfl` directly in your proofs in this book and see what you discover!

# Logical Connectives as Inductive Types

:::suppressPreviousHeaderWhenTerse
:::

::::full
We have now seen that tactics are not "special" in Lean: they are just
manipulators of terms.
Recall that Lean's logical connectives are also not "special": only universal
quantification (with implication as a special case) is built into
Lean; all the other connectives are defined inductively.
Now that we know more about the relationship between terms and tactics,
we can delve into advanced ways to work with logical connectives.
::::

```lean -show
namespace Props
```

## Conjunction

:::suppressPreviousHeaderWhenTerse
:::

::::::full
To prove that `P ∧ Q` holds, we must present evidence for both
`P` and `Q`.  Thus, it makes sense to define a proof object for
`P ∧ Q` to consist of a pair of proofs: one for `P` and
another for `Q`. This leads to the following definition.

```lean -show
namespace AndPlayground
```

```lean
structure And (P Q : Prop) : Prop where
  intro ::
  left : P
  right : Q
```

Now that we have pulled back the covers a bit further, we can
reveal another fact: a `structure` is just an inductive type with
one constructor whose parameters are named. By default,
the constructor is called `mk`, which we can rename to `<name>`
using `<name> ::`, as in the example.

We can also see that this definition of {name}`And` matches core
{lean}`And` exactly: a `structure` with constructor {name _root_.And.intro}`intro`
and fields {name _root_.And.left}`left`/{name _root_.And.right}`right`
(except that core uses `a` and `b` instead of `P` and `Q`).
```lean (name := print_core_and)
#print _root_.And
```

```leanOutput print_core_and
structure _root_.And (a b : Prop) : Prop
number of parameters: 2
fields:
  _root_.And.left : a
  _root_.And.right : b
constructor:
  _root_.And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
```

Notice the similarity with the definition of the {name}`MyProd` type,
given in chapter {ref "Poly"}[Poly]; the only difference is that {name}`MyProd` takes
{lean}`Type` arguments, whereas {name}`And` takes {lean}`Prop` arguments.

```lean (name := print_myprod)
#print MyProd
```

```leanOutput print_myprod
structure MyProd (α β : Type) : Type
number of parameters: 2
fields:
  MyProd.fst : α
  MyProd.snd : β
constructor:
  MyProd.mk {α β : Type} (fst : α) (snd : β) : MyProd α β
```

:::slidebreak
:::

This similarity should clarify why {tactic}`cases`, {tactic}`obtain` `⟨hp, hq⟩`,
and {tactic}`intro` `⟨hp, hq⟩`
patterns can be used on a conjunctive hypothesis.  Case analysis
allows us to consider all possible ways in which `P ∧ Q` was
proved. For {name}`And` there is just one — the {name}`And.intro` constructor:

```lean (name := proj1'_cases)
theorem proj1' (P Q : Prop) (hpq : And P Q) : P := by
  cases hpq with
  | intro hp _ => exact hp
```

Here is a use of {tactic}`obtain`:

```lean
theorem and_comm (P Q : Prop) : And P Q ↔ And Q P := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := h
    constructor
    · exact hq
    · exact hp
  · intro h
    obtain ⟨hq, hp⟩ := h
    constructor
    · exact hp
    · exact hq
```

```lean -show
end AndPlayground
```

:::slidebreak
:::

Just as the `inductive` (`structure`) definition of {name}`And` can be
manipulated by tactics, we can also use it to build proofs directly.

```lean
theorem proj1'' (P Q : Prop) (hpq : P ∧ Q) : P :=
  match hpq with
  | And.intro hp _ => hp

theorem and_comm'_aux (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  match h with
  | And.intro hp hq => And.intro hq hp

theorem and_comm' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
  Iff.intro (and_comm'_aux P Q) (and_comm'_aux Q P)
```

Here, {lean}`Iff.intro` is doing the same thing as {name}`And.intro`:
it builds the {name}`Iff` `structure` with its two arguments.

:::::exercise (rating := 2) (name := "conj_fact")
Construct a proof object for the following proposition.

```lean
theorem conj_fact : ∀ (P Q R : Prop),
    P ∧ Q → Q ∧ R → P ∧ R :=
  solution!(fun _ _ _ hpq hqr =>
    match hpq, hqr with
    | And.intro hp _, And.intro _ hr => And.intro hp hr)
```

:::gradeTheorem 2 conj_fact
:::
:::::

::::::

:::::quiz
::::full
What is the type of this expression?

```display +centered
fun P Q R (h1 : And P Q) (h2 : And Q R) =>
  match h1, h2 with
  | And.intro hp _, And.intro _ hr => And.intro hp hr
```

(A) {lean}`∀ (P Q R : Prop), P ∧ Q → Q ∧ R → P ∧ R`

(B) {lean}`∀ (P Q R : Prop), Q ∧ P → R ∧ Q → P ∧ R`

(C) {lean}`∀ (P Q R : Prop), P ∧ R`

(D) {lean}`∀ (P Q R : Prop), P ∨ Q → Q ∨ R → P ∨ R`

(E) Not typeable

:::quizSolution
(A)
```lean
#check (fun P Q R (h1 : And P Q) (h2 : And Q R) =>
          match h1, h2 with
          | And.intro hp _, And.intro _ hr =>
            And.intro hp hr
        : ∀ (P Q R : Prop), P ∧ Q → Q ∧ R → P ∧ R)
```
:::
::::

:::::

## Disjunction

:::suppressPreviousHeaderWhenTerse
:::

::::::full
The inductive definition of disjunction uses two constructors, one
for each side of the disjunction:

```lean -show
namespace OrPlayground
```

```lean
inductive Or (P Q : Prop) : Prop where
  | inl : P → Or P Q
  | inr : Q → Or P Q
```

This declaration explains the behavior of the {tactic}`cases` tactic on
a disjunctive hypothesis, since the generated subgoals match the
shape of the {name}`Or.inl` and {name}`Or.inr` constructors.

:::slidebreak
:::

Once again, we can also directly write proof objects for theorems
involving {name}`Or`, without resorting to tactics.

```lean (name := inj_l'_show_proof)
theorem inj_l : ∀ (P Q : Prop), P → Or P Q :=
  fun _ _ hp => Or.inl hp

theorem inj_l' (P Q : Prop) (hp : P) : Or P Q := by
  show_proof
    left
    exact hp
```

```leanOutput inj_l'_show_proof
?_

after left:
  Or.inl ?_

after exact hp:
  Or.inl hp
```

:::slidebreak
:::

```lean
theorem or_elim : ∀ (P Q R : Prop),
    Or P Q → (P → R) → (Q → R) → R :=
  fun _ _ _ hpq hpr hqr =>
    match hpq with
    | Or.inl hp => hpr hp
    | Or.inr hq => hqr hq

theorem or_elim' (P Q R : Prop) (hpq : Or P Q)
    (hpr : P → R) (hqr : Q → R) : R := by
  cases hpq with
  | inl hp =>
    apply hpr
    exact hp
  | inr hq =>
    apply hqr
    exact hq
```

:::dev "Mike Hicks (mwhicks1)"
It is confusing that we don't use {tactic}`show_proof` here, but if we did, it doesn't show the
proof in the first example; it looks more like the second example directly. Should we
change the example? Maybe use the non-sameness to explain how proofs can differ?
:::

```lean -show
end OrPlayground
```

:::::exercise (rating := 2) (name := "or_commut'")
Construct a proof object for the following proposition.

```lean
theorem or_commut' : ∀ (P Q : Prop), P ∨ Q → Q ∨ P :=
  solution!(fun (P Q : Prop) (h : P ∨ Q) =>
    match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq)
```

:::gradeTheorem 2 or_commut'
:::
:::::

::::::

:::::quiz
::::full
What is the type of this expression?

```display +centered
fun P Q h =>
  match h with
  | Or.inl hp => @Or.inr Q P hp
  | Or.inr hq => @Or.inl Q P hq
```

(A) {lean}`∀ P Q H, Q ∨ P ∨ H`

(B) {lean}`∀ (P Q : Prop), P ∨ Q → Q ∨ P`

(C) {lean}`∀ P Q H, P ∨ Q → Q ∨ P → H`

(D) {lean}`∀ (P Q : Prop), P ∨ Q → P ∨ Q`

(E) Not typeable

:::quizSolution
(B)
```lean
#check (fun P Q h =>
          match h with
          | Or.inl hp => @Or.inr Q P hp
          | Or.inr hq => @Or.inl Q P hq
        : ∀ (P Q : Prop), P ∨ Q → Q ∨ P)
```
:::
::::

:::::

## Existential Quantification

:::suppressPreviousHeaderWhenTerse
:::

::::full
To give evidence for an existentially quantified proposition `P`, we package a
witness `x` together with a proof of `P x`, i.e., that `x` satisfies `P`:

```lean -show
namespace ExistsPlayground
```

```lean
inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀ (w : α), P w → Exists P
```
```lean -show
end ExistsPlayground
```

This definition may need a little unpacking.  {name}`Exists` can be used to
build propositions of the form `Exists P`, where `P` is a predicate, i.e.,
a _function_ from witness values of type `α` to {lean}`Prop`. The {name}`Exists.intro`
constructor then offers a way of constructing evidence for `Exists P`,
given a witness `w` and a proof of `P w`.

:::slidebreak
:::

The more familiar form {lean}`∃ x, Even x` desugars to an expression
involving {name}`Exists`:

```lean (name := check_exists)
#check (Exists (fun n => Even n) : Prop)
```

```leanOutput check_exists
∃ n, Even n : Prop
```

Here's how to define an explicit proof object involving {name}`Exists`:

```lean
theorem some_nat_is_even : ∃ n, Even n :=
  Exists.intro 4
    (Even.succ_succ 2 (Even.succ_succ 0 Even.zero))
```
::::

::::hide
```
/- APT: Move to IndPrinciples ? -/
/- FULL: Here's the induction principle that Lean generates: -/

    Check ex_ind
      : forall (α: Type) (P: α->Prop) (Q: Prop),
        (forall witness:α, P witness -> Q) ->
        (exists y, P y) ->
        Q.

/- FULL: This induction principle can be understood as follows: If we have
a function [f] that can construct evidence for [Q] given _any_
witness of type [α] together with evidence that this witness has
property [P], then from a proof of [ex α P] we can extract the
witness and evidence that must have been supplied to the
constructor, give these to [f], and thus obtain a proof of [Q]. -/
```
:::dev "Claude" PotentialImprovement
AI-TODO: About the hidden block above. Lean generates no `Exists.ind`; its
eliminators are `Exists.rec` and the derived `Exists.elim`.

Proposed fix: if un-hidden, port the block as `#check @Exists.elim` (or `@Exists.rec`) with a `leanOutput`, and adjust "the induction principle that Lean generates". Otherwise leave it.
:::
::::

The notation in the standard library is a slight extension of
the above, enabling syntactic forms such as `∃ x y, P x y`.
The standard library's {lean}`Exists` also takes `P` implicitly.

::::::quiz
::::full
Which of the following propositions is proved by
providing an explicit witness `w` using {tactic}`exists` `w`?

(A) {lean}`∀ (x : Nat), (∃ n, x = n + 1) → x ≠ 0`

(B) {lean}`∀ (x : Nat), x ≠ 0 → (∃ n, x = n + 1)`

(C) {lean}`∀ (x : Nat), x = 0 → ¬(∃ n, x = n + 1)`

(D) {lean}`∀ (x : Nat), x = 4 → x ≠ 0`

(E) none of the above

:::quizSolution
(B)
```lean
example : ∀ (x : Nat), x ≠ 0 → (∃ n, x = n + 1) := by
  intro x h
  cases x with
  | zero =>
    exfalso
    apply h
    rfl
  | succ x' => exists x'
```
:::
::::
::::::

::::::full
:::::exercise (rating := 2) (name := "ex_even_Sn")
Construct a proof object for the following proposition.

```lean
theorem ex_even_Sn : Exists (fun n => Even (n + 1)) :=
  solution!(Exists.intro 1 (Even.succ_succ 0 Even.zero))
```

:::gradeTheorem 2 ex_even_Sn
:::
:::::
::::::

:::slidebreak
:::

To destruct existentials in a proof term, we simply use {tactic}`match`:

```lean
theorem dist_exists_or_term (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) :=
  fun h => match h with
           | Exists.intro x hx =>
               match hx with
               | Or.inl hpx => Or.inl (Exists.intro x hpx)
               | Or.inr hqx => Or.inr (Exists.intro x hqx)
```

::::::full
:::::exercise (rating := 2) (name := "ex_match")
Construct a proof object for the following proposition:

```lean
theorem ex_match : ∀ (A : Type) (P Q : A → Prop),
    (∀ (x : A), P x → Q x) →
    (∃ x, P x) → (∃ x, Q x) :=
  solution!(fun _ _ _ hpq hp =>
    match hp with
    | Exists.intro x hpx => Exists.intro x (hpq x hpx))
```

:::gradeTheorem 2 ex_match
:::
:::::
::::::

## {lean}`True` and {lean}`False`

:::suppressPreviousHeaderWhenTerse
:::

::::::full
The inductive definition of the {lean}`True` proposition is simple:

```lean
inductive True : Prop where
  | intro : True
```

It has one constructor: there is one definitional way to build {lean}`True`.
(But there are lots of ways to state and prove true things!)

:::::exercise (rating := 1) (name := "p_implies_true")
Construct a proof object for the following proposition.

```lean
theorem p_implies_true : ∀ (P : Prop), P → True :=
  solution!(fun _ _ => True.intro)
```

:::gradeTheorem 1 p_implies_true
:::
:::::

:::slidebreak
:::

{lean}`False` is equally simple — indeed, so simple it may look
syntactically wrong at first glance!

```lean
inductive False : Prop
```

That is, {lean}`False` is an inductive type with _no_ constructors,
i.e., no way to build evidence for it. Thus, there is
no way to complete the following definition (replacing {lean}`sorry`) such
that it succeeds.

```lean
theorem contra : False := sorry
```

:::slidebreak
:::

But it _is_ possible to destruct {lean}`False` by pattern matching. There can
be no patterns that match it, since it has no constructors. To
handle this, Lean uses the {tactic}`nomatch` construct.

```lean
theorem false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra
```

Since there are no branches to evaluate, the {tactic}`nomatch` expression
can be given any type we want, including {lean}`0 = 1`.
Fortunately, it's impossible to ever cause the {tactic}`nomatch` to be
evaluated, because we can never construct a value of type {lean}`False`
to pass to the function.

:::::exercise (rating := 1) (name := "ex_falso_quodlibet'")
Construct a proof object for the following proposition.

```lean
theorem ex_falso_quodlibet' : ∀ (P : Prop), False → P :=
  solution!(fun _ contra => nomatch contra)
```

:::gradeTheorem 1 ex_falso_quodlibet'
:::
:::::
::::::

```lean -show
end Props
```

# Equality

:::suppressPreviousHeaderWhenTerse
:::

```lean -show
namespace EqualityPlayground
```

::::::full
Even Lean's equality relation is not built in.  We can define
it ourselves:

```lean
inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀ (x : α), Eq x x

scoped infix:50 " =' " => Eq
```

The {name}`Eq` definition relates pairs of elements of type `α`. The only way to
prove `Eq a b` for a pair of elements `a` and `b` is via the {name}`Eq.refl` constructor,
which by requiring `Eq x x` for all `x` forces `a` and `b` to be _the same_.

:::slidebreak
:::

This means we can use {name}`Eq.refl` to construct evidence that, for example, {lean}`2 = 2`.
Can we also use it to construct evidence that {lean}`1 + 1 = 2`?
Perhaps surprisingly: Yes, we can!

The reason is that Lean treats as "the same" any two terms that are
_convertible_ according to a simple set of computation rules.
These rules, which are similar to those used by `#eval`, include
evaluation of function application, inlining of definitions, and
simplification of {tactic}`match` expressions.

```lean
theorem four : 2 + 2 =' 1 + 3 := by
  apply Eq.refl
```

:::slidebreak
:::

The {tactic}`rfl` tactic that we have used to prove
equalities of the form `x = y` up to now is
essentially just shorthand for {tactic}`apply` {name}`Eq.refl`.

In tactic-based proofs of equality, the conversion rules operate
invisibly: whenever Lean checks two terms for definitional equality
— as {tactic}`rfl` does when closing a goal `x = y`, or as {tactic}`exact`
and {tactic}`apply` do when unifying a term against an expected type — it
reduces both sides by these computation rules before comparing them.
You can see what's going on by enabling the Lean option {InlineLean.option}`trace.Meta.isDefEq`:

```lean
set_option trace.Meta.isDefEq true in
example : 1 + 1 = 2 := rfl
```

In explicit proofs of equality, the conversion rules still operate
invisibly, but their _result_ is made manifest as an argument to
{name}`Eq.refl` in the proof term.

```lean
theorem four' : 2 + 2 =' 1 + 3 :=
  Eq.refl 4

theorem singleton : ∀ (α : Type) (x : α),
    [] ++ [x] =' x :: [] :=
  fun (α : Type) (x : α) => Eq.refl [x]
```

:::slidebreak
:::

We can also pattern-match on an equality proof:

```lean
theorem eq_add : ∀ (n1 n2 : Nat),
    n1 =' n2 → (n1 + 1) =' (n2 + 1) :=
  fun n1 n2 heq =>
    match heq with
    | Eq.refl _ => Eq.refl (n1 + 1)
```

By pattern-matching against `n1 =' n2`, we replace `n2` with `n1`
in the type we have to produce, so
instead of `(n1 + 1) =' (n2 + 1)`, we now have to produce something
of type `(n1 + 1) =' (n1 + 1)`, which we establish by `Eq.refl (n1 + 1)`.

:::slidebreak
:::

A tactic-based proof runs into some difficulties if we try to use
our usual repertoire of tactics, such as {tactic}`rw` and
{tactic}`rfl`. Those work with relations that Lean knows about,
such as `=`, but not with our `='`. We could teach Lean about `='`
(by registering a reflexivity lemma for {tactic}`rfl`, or by working
in a _quotient type_ where `='` becomes `=`, for {tactic}`rw`),
but a simpler way is to use {tactic}`cases` and {tactic}`apply` instead.

```lean +error -keep
example (n1 n2 : Nat) (heq : n1 =' n2) :
    (n1 + 1) =' (n2 + 1) := by
  rw [heq] -- doesn't work for _our_ =' relation
```

```lean +error -keep
example (n1 : Nat) : (n1 + 1) =' (n1 + 1) := by
  rfl -- doesn't work for _our_ =' relation
```

```lean
theorem eq_add' (n1 n2 : Nat) (heq : n1 =' n2) :
    (n1 + 1) =' (n2 + 1) := by
  cases heq -- n2 replaced by n1 in the goal!
  apply Eq.refl
```

:::::exercise (rating := 2) (name := "eq_cons")
Construct the proof object for the following theorem. Use pattern
matching on the equality hypotheses.

```lean
theorem eq_cons : ∀ (α : Type) (h1 h2 : α) (t1 t2 : List α),
    h1 =' h2 → t1 =' t2 → h1 :: t1 =' h2 :: t2 :=
  solution!(fun _ h1 _ t1 _ heq teq =>
    match heq, teq with
    | Eq.refl _, Eq.refl _ => Eq.refl (h1 :: t1))
```

:::gradeTheorem 2 eq_cons
:::
:::::

:::dev PotentialImprovement
```
(PR) The leibniz_equality exercise may confuse students
because of the reuse of = for local equality. In the solution, the
inversion cannot be replaced with a rewrite, as it can outside this
module, because rewrite does not understand local equality. A quick
fix is to use notation such as "x == y" locally.  Then it is clear
that the inversion replaces local equality with library
equality. But to really clarify, perhaps the exercise should be
moved to IndPrinciples.v, where the text can show the actual
definition of library equality (after the discussion of the simpler
principle for le to motivate the use of a parameter) and the
resulting eq_ind, and the exercise can ask for an explicit proof
term instead of a tactics-based proof.

(BCP) At least one reader did get confused by the rewrite failure.
And the harder exercise is also confusing for the same reason (have
to use apply instead of reflexivity).  Would be good to do
something about this.  I agree with moving it elsewhere, I think.

(PR) I have put the == quick fix in.

MRC 3/22: I have added [eq_add'] above to explain why [rewrite] and
[reflexivity] fail, and to show that [destruct] and [apply] will
work.  I've also added a second exercise to give the proof object,
which does not actually require [eq_ind]. I think the exercise
stands on its own here, now.
```
:::

:::::exercise (rating := 2) (name := "equality__leibniz_equality")
The inductive definition of equality implies _Leibniz equality_:
what we mean when we say "`x` and `y` are equal" is that every
property `P` that is true of `x` is also true of `y`. Prove
that.

```lean
theorem equality__leibniz_equality : ∀ (α : Type) (x y : α),
    x =' y → ∀ (P : α → Prop), P x → P y := by
  solution!
    intro α x y heq P hpx
    cases heq
    exact hpx
```

:::gradeTheorem 2 equality__leibniz_equality
:::
:::::

:::::exercise (rating := 2) (name := "equality__leibniz_equality_term")
Construct the proof object for the previous exercise.  All it
requires is anonymous functions and pattern-matching; the large
proof term constructed by tactics in the previous exercise is
needessly complicated. Hint: pattern-match as soon as possible.

```lean
theorem equality__leibniz_equality_term :
    ∀ (α : Type) (x y : α),
    x =' y → ∀ (P : α → Prop), P x → P y :=
  solution!(fun _ _ _ heq =>
    match heq with
    | Eq.refl _ => fun _ hp => hp)
```

:::gradeTheorem 2 equality__leibniz_equality_term
:::
:::::

:::::exercise (rating := 2) (name := "leibniz_equality__equality") (optional := true)
Show that, in fact, the inductive definition of equality is
_equivalent_ to Leibniz equality.  Hint: the proof is quite short.
You can write it by inventing a clever property `P` to
instantiate the antecedent, or you can let Lean figure it out...

```lean
theorem leibniz_equality__equality : ∀ (α : Type) (x y : α),
    (∀ (P : α → Prop), P x → P y) → x =' y := by
  solution!
    intro α x y h
    apply h (fun z => x =' z) -- `apply h` also works; Lean will provide `P`.
    apply Eq.refl
```
:::::
::::::

:::::quiz
::::full
Which of the following is a correct proof object for the proposition

```display +centered
∃ x, x + 3 =' 4
```

?

(A) `Eq.refl 4`

(B) `@Exists.intro Nat (z + 3 =' 4) 1 (Eq.refl 4)`

(C) `@Exists.intro Nat (fun z => z + 3 =' 4) 1 (Eq.refl 4)`

(D) `@Exists.intro Nat (fun z => z + 3 =' 4) 1 (Eq.refl 1)`

(E) none of the above

:::quizSolution
```lean +error -keep
theorem quiz1 : ∃ x, x + 3 =' 4 :=
  Eq.refl 4
```

```lean +error -keep
theorem quiz2 : ∃ x, x + 3 =' 4 :=
  @Exists.intro Nat (z + 3 =' 4) 1 (Eq.refl 4)
```

```lean
theorem quiz3 : ∃ x, x + 3 =' 4 :=
  @Exists.intro Nat (fun z => z + 3 =' 4) 1 (Eq.refl 4)
```

```lean +error -keep
theorem quiz4 : ∃ x, x + 3 =' 4 :=
  @Exists.intro Nat (fun z => z + 3 =' 4) 1 (Eq.refl 1)
```
:::
::::
:::::

```lean -show
end EqualityPlayground
```

:::dev
-- ## Inversion, Again

-- :::suppressPreviousHeaderWhenTerse
-- :::

HIDE: PR: This section may be repetitive given the increased
attention paid to {tactic}`inversion`, and it may be ineffective since
this chapter is no longer on the recommended path. We need to
think about whether this kind of reinforcement of the tactic is
needed, and if so, where to place it for best impact.

BCP 11/18: I agree — this material is a bit redundant.  On the
other hand, the examples at the end may be helpful, so maybe it's
fine to leave it.
:::

# Lean's Trusted Computing Base

:::suppressPreviousHeaderWhenTerse
:::

:::dev "Mike Hicks (mwhicks1)"
There is some overlap here and with the discussion of the TCB in Logic.lean.
For that matter, much of the discussion of logical connective proofs here
overlaps with the presentation in Logic.lean. This split feels non-optimal
to me. I wonder if we can consider some sort of merge of these two chapters.
:::

::::full
One question that arises with any automated proof assistant
is "why should we trust it?" — i.e., what if there is a bug in
the implementation that renders all its reasoning suspect?

While it is impossible to allay such concerns completely, the fact
that Lean is based on the Curry-Howard correspondence gives it a
strong foundation. Because propositions are just types and proofs
are just terms, checking that an alleged proof of a proposition is
valid just amounts to _type-checking_ the term.  Type checkers are
relatively small and straightforward programs, so the "trusted
computing base" for Lean — the part of the code that we have to
believe is operating correctly — is small too.

How, then, does Lean relegate its large set of complex behaviors to a small codebase?

Lean is organized in two layers. The _elaborator_ is large and
complicated: it handles notation, implicit arguments, {tactic}`match`,
recursion, and tactics. Its output is a plain term in Lean's core
type theory, which it hands to the _kernel_. Only the kernel is
trusted. It is small, and its job is just to type-check that term,
computing as needed to decide whether two types are the same.

This division means that a bug in the elaborator, or in a tactic,
cannot lead Lean to accept a false theorem: at worst, it produces a
term that the kernel then rejects. Every declaration, whether written
as a term or built by tactics, is checked by the kernel when it is
added to the environment.

Two checks you might expect a typechecker to perform, exhaustiveness
of {tactic}`match` and termination of recursive functions, happen in the
elaborator, because the kernel's language actually has no {tactic}`match` and no
recursion at all. The kernel's language for destructuring values only has the notion of a
_recursor_: a primitive function that is exhaustive and
terminating by construction. If the elaborator cannot express a definition
in terms of the recursors generated by the kernel, it rejects the definition.

There are some mild exceptions to this, like `partial def`, but those exceptions
have strict rules imposed upon them to prevent a proof of {name}`False`,
and in general it is the translation to recursors that catches such bugs.

We can see the elaborator refuse
definitions that would otherwise let us prove {name}`False`:

```lean +error -keep
theorem or_bogus : ∀ (P Q : Prop), P ∨ Q → P :=
  fun (P Q : Prop) (A : P ∨ Q) =>
    match A with
    | Or.inl h => h
```

All the types here match correctly, but the {tactic}`match` only
considers one of the possible constructors for {name}`Or`.  Lean's
exhaustiveness check will reject this definition.

```lean +error -keep
def infinite_loop {α : Type} (n : Nat) : α :=
  infinite_loop n
termination_by structural n

theorem falso : False := infinite_loop 0
```

Recursive function `infinite_loop` purports to return a
value of any type `α` that you would like.  (The
`termination_by structural n` annotation tells Lean that it recurses
on argument `n`, not `α`.)  Were Lean to allow `infinite_loop`, then `falso`
would be definable, thus giving evidence for {lean}`False`.  So Lean rejects
`infinite_loop`.

Besides the kernel, we also trust the handful of _axioms_ Lean
assumes, such as {name}`propext`. The command `#print axioms` shows
which axioms a theorem depends on. The tactic {tactic}`native_decide` goes
further, trusting Lean's compiler too, which is why careful
developments avoid it.
::::

# More Exercises

:::suppressPreviousHeaderWhenTerse
:::

::::::full
Most of the following theorems were already proved with tactics in
{ref "Logic"}[Logic].  Now construct the proof objects for them
directly.

:::::exercise (rating := 2) (name := "and_assoc")
```lean
theorem and_assoc : ∀ (P Q R : Prop),
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  solution!(fun _ _ _ h =>
    match h with
    | And.intro hp (And.intro hq hr) =>
      And.intro (And.intro hp hq) hr)
```

:::gradeTheorem 2 and_assoc
:::
:::::

:::::exercise (rating := 3) (name := "or_distributes_over_and")
```lean
theorem or_distributes_over_and : ∀ (P Q R : Prop),
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  solution!(fun _ _ _ =>
    Iff.intro
      (fun h =>
        match h with
        | Or.inl hp => And.intro (Or.inl hp) (Or.inl hp)
        | Or.inr (And.intro hq hr) =>
          And.intro (Or.inr hq) (Or.inr hr))
      (fun h =>
        match h with
        | And.intro hpq hpr =>
          match hpq, hpr with
          | Or.inl hp, _ | _, Or.inl hp => Or.inl hp
          | Or.inr hq, Or.inr hr =>
            Or.inr (And.intro hq hr)))
```

:::gradeTheorem 3 or_distributes_over_and
:::
:::::

:::::exercise (rating := 3) (name := "negations")
```lean
theorem double_neg : ∀ (P : Prop),
    P → ¬¬P :=
  solution!(fun _ hp hnp => hnp hp)
```

:::gradeTheorem 1 double_neg
:::

```lean
theorem contradiction_implies_anything : ∀ (P Q : Prop),
    (P ∧ ¬P) → Q :=
  solution!(fun _ _ h =>
    match h with
    | And.intro hp hnp => nomatch hnp hp)
```

:::gradeTheorem 1 contradiction_implies_anything
:::

```lean
theorem de_morgan_not_or : ∀ (P Q : Prop),
    ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  solution!(fun _ _ h =>
    And.intro (fun hp => h (Or.inl hp))
      (fun hq => h (Or.inr hq)))
```

:::gradeTheorem 1 de_morgan_not_or
:::
:::::

:::::exercise (rating := 2) (name := "currying")
```lean
theorem curry : ∀ (P Q R : Prop),
    ((P ∧ Q) → R) → (P → (Q → R)) :=
  solution!(fun _ _ _ h hp hq =>
    h (And.intro hp hq))
```

:::gradeTheorem 1 curry
:::

```lean
theorem uncurry : ∀ (P Q R : Prop),
    (P → (Q → R)) → ((P ∧ Q) → R) :=
  solution!(fun _ _ _ h hpq =>
    match hpq with
    | And.intro hp hq => h hp hq)
```

:::gradeTheorem 1 uncurry
:::
:::::

::::::

# Working with Proof Irrelevance

:::suppressPreviousHeaderWhenTerse
:::

::::::full
In {ref "Logic"}[Logic] we saw that functional extensionality ({tactic}`funext`)
is a core property of Lean. A similar notion about propositions also exists
in Lean, this time as a core axiom of _propositional extensionality_:

```lean (name := check_propext)
-- Written out, propositional extensionality looks like this:
def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

-- Lean calls it `propext`:
#check propext
```

```leanOutput check_propext
propext {a b : Prop} : (a ↔ b) → a = b
```

Propositional extensionality asserts that if two propositions are
equivalent — i.e., each implies the other — then they are in
fact equal. The _proof objects_ for the propositions might be
syntactically different terms. But propositional extensionality
overlooks that, just as functional extensionality overlooks the
syntactic differences between functions.

:::::exercise (rating := 1) (name := "pe_implies_or_eq") (level := Advanced)
Prove the following consequence of propositional extensionality.

```lean
theorem pe_implies_or_eq :
    propositional_extensionality →
    ∀ (P Q : Prop), (P ∨ Q) = (Q ∨ P) := by
  solution!
    unfold propositional_extensionality
    intro PE P Q
    apply PE (P ∨ Q) (Q ∨ P)
    apply Or.comm
```

:::gradeTheorem 1 pe_implies_or_eq
:::
:::::

:::::exercise (rating := 1) (name := "pe_implies_true_eq") (level := Advanced)
Prove that if a proposition `P` is provable, then it is equal to
{lean}`True` — as a consequence of propositional extensionality.

```lean
theorem pe_implies_true_eq :
    propositional_extensionality →
    ∀ (P : Prop), P → True = P := by
  solution!
    unfold propositional_extensionality
    intro PE P p
    apply PE
    constructor
    · intro _
      exact p
    · intro _
      apply True.intro
```

:::gradeTheorem 1 pe_implies_true_eq
:::
:::::

Propositional extensionality is about equating two different
_propositions_ that happen to be equivalent. A related but distinct
notion, _proof irrelevance_, is instead about equating two different
_proofs_ of the _same_ proposition:

```lean
def proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2
```

In many proof assistants, proving this fact outright requires an
assumption like propositional extensionality: without some axiom to
fall back on, two proofs of the same proposition are just two terms,
and nothing forces them to be equal. But recall the
{ref "proof-irrelevance"}[Dependency, Equivalence, and Proof
Irrelevance] section earlier in this chapter: Lean's {lean}`Prop` already
builds proof irrelevance into its type theory, so that any two
proofs of the same proposition are automatically
_definitionally_ equal. So {name}`proof_irrelevance` holds outright here,
with no axioms needed at all:

```lean (name := check_pi)
theorem proof_irrelevance_lean : proof_irrelevance :=
  fun _ _ _ => rfl

#print axioms proof_irrelevance_lean
```

```leanOutput check_pi
'EvenProp.proof_irrelevance_lean' does not depend on any axioms
```

This is one of the ways Lean's type theory is unusual: most other
proof assistants either don't have this property by default, or
offer it only for a separate, special-purpose kind of proposition
that you have to opt into.

::::::

```lean -show
end EvenProp
```
