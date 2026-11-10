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

This setting is enabled to make some tricky mistakes harder to make.
```lean
set_option autoImplicit false
```

:::dev "Claude" BeforeNextRelease
AI-TODO: Chapter-wide items before a final version.

- Review the code conventions chosen during the port: lowercase hypothesis
  names (`hpq`, `h`), `theorem … := term` for proof objects, the
  `AndPlayground`/`OrPlayground`/`ExistsPlayground` namespaces, and `='`.
- Replace the remaining `--` dashes in prose with em dashes (STYLE-WRITING).
- Register the chapter in `LF.lean` (after IndProp) and the lakefile, then
  run `lake build` plus the student/solutions/terse variant builds (they
  catch `{ref}` and variant errors that `lake build` misses).
- Mark AI-written material per the CONTRIBUTING AI policy (this file was
  ported with Claude's help; the `show_proof` tactic is Claude-written), and
  run `/proofread ProofObjects`.

Proposed fix: work through the list; delete this note when done.
:::

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

```display
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
parameterized constructor {name}`Even.succ_succ` with the specific arguments `2`
and `0` plus the corresponding proof objects for its premises {lean}`Even 2` and {lean}`Even 0`.  Alternatively, we can think of {name}`Even.succ_succ` as a
primitive "evidence constructor" that, when applied to a
particular number, wants to be further applied to evidence that
this number is even; its type,

```display
∀ (n : Nat), Even n → Even (n + 2)
```

expresses this functionality, in the same way that the polymorphic
type {lean}`{α : Type} → List α` expresses the fact that the constructor
{name}`List.nil` can be thought of as a function from types to empty lists
with elements of that type.

The fact that the some arguments are implicit, like `{α}` of {lean}`List`
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
the `show_proof` command to display the current state of the proof
tree at various points in the following tactic proof.

`show_proof` wraps a tactic script and prints the partial proof term—
a term with _holes_ where the remaining proof obligations are—
before and after each step. A term's holes are shown as `?_`.

The implementation of `show_proof` need not be understood. Its details are
tucked away in the block below.
::::

::::terse
When we write a proof using tactics, what we are doing is
instructing Lean to build a proof object under the hood.  We can
see this using the custom command `show_proof`:
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
evidence we've built is stored in the global context under the name
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

What is the proof object corresponding to `even_plus4`?

:::slidebreak
:::

We're looking for an expression whose _type_ is `∀ (n : Nat), Even n → Even (n + 4)` — that is, a _function_ that takes two arguments (one
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

When we view the proposition being proved by `even_plus4` as a
function type, one interesting point becomes apparent: The second
argument's type, `Even n`, mentions the _value_ of the first
argument, `n`.

While such _dependent types_ are not found in most mainstream
programming languages, they can be quite useful in programming
too, as the flurry of activity in the functional programming
community over the past couple of decades
(and recently, most notably Lean!) demonstrates.

:::slidebreak
:::

Notice that both implication (`→`) and quantification (`∀`)
correspond to functions on evidence.  In fact, they are really the
same thing: `→` is just a shorthand for a degenerate use of
`∀` where there is no dependency, i.e., no need to give a
name to the type on the left-hand side of the arrow:

```display
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
of the statement of `even_plus2`, so it's a bit silly to bother
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
use `intro`:
```lean
theorem even_plus2_thm' (n : Nat) (heven : Even n) :
    Even (n + 2) := by
    constructor; assumption
```

_All_ of these theorem statements are equivalent! When we write `def`,
we are just writing down the statement— the type. When we write
`theorem`, we are stating the type and then providing a witness after
the `:=` (either with `by` and tactics or directly with a term). We
can even show the two definitions are equivalent in Lean itself:

```lean
theorem even_plus2_defs_same :
    even_plus2 = even_plus2'' := by rfl
```
Remember that theorem statements are just types, so `rfl` here is just
comparing two types.

What about the two theorems? Here, we are asking if two _proofs_— AKA,
two _functions_— are equal. Then, do we need to use {tactic}`funext`?

```lean
theorem even_plus2_theorems_same :
    even_plus2_thm = even_plus2_thm' := by rfl
```

Surprisingly, we don't. This is because Lean has a special feature
called _definitional proof irrelevance_. It says that any two proofs
of the same proposition are definitionally equal. So we could write
the same proof again however we wanted— with different tactics, using
terms instead of tactics, etc.— and we would still have "the same
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

```display
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ (n : Nat) (h : Even n) : Even (n + 2)
```

What is the type of this expression?

```display
fun (n : Nat) =>
  fun (h : Even n) =>
     Even.succ_succ (n + 2) (Even.succ_succ n h)
```

(A) `∀ (n : Nat), Even n`

(B) `∀ (n : Nat), Even (n + 2)`

(C) `∀ (n : Nat), Even n → Even n`

(D) `∀ (n : Nat), Even n → Even (n + 2)`

(E) `∀ (n : Nat), Even n → Even (n + 4)`

(F) Not typeable

:::quizSolution
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

Notice that we terminated the `Definition` with a `.` rather than
with `:=` followed by a term.  This tells Rocq to enter _proof
scripting mode_ to build an object of type `Nat → Nat`.  Also, we
terminate the proof with `Defined` rather than `Qed`; this makes
the definition _transparent_ so that it can be used in computation
like a normally-defined function.  (`Qed`-defined objects are
opaque during computation.)

This feature is mainly useful for writing functions with dependent
types, which we won't explore much further in this book.  But it
does illustrate the uniformity and orthogonality of the basic
ideas in Rocq.
::::

:::dev "Claude" BeforeNextRelease
AI-TODO: The paragraph about terminating with `.` and `Defined` vs. `Qed` is wrong
in Lean:

- You write `def add2 : Nat → Nat := by …`. There is no separate
  "proof scripting mode" entered by a period.
- There is no `Defined` vs. `Qed`. A `def` built with tactics is transparent
  and computable (`#eval add2 2` works).
- The closest Lean distinction is `def` vs. `theorem`. A `theorem` must have a
  `Prop` type: `theorem add2 : Nat → Nat := by …` is rejected with "type of
  theorem `add2` is not a proposition" (verified). `theorem` bodies are also
  treated as irreducible and are not compiled.

`Compute` becomes `#eval` (or `#reduce`).

Proposed fix: rewrite the paragraph: `:= by` enters tactic mode to build a term of type `Nat → Nat`; a `def` built this way stays computable (`#eval add2 2`); the contrast with Rocq's `Defined`/`Qed` becomes `def` vs. `theorem` (a `theorem` must have a `Prop` type).
:::

::::::hide
Building Proof Objects Incrementally (Optional)

:::dev PotentialImprovement
Is the following helpful / necessary? I (Mukund) find myself
doing exactly this when constructing proof objects...
:::

As you probably noticed while solving the exercises earlier in the
chapter, constructing proof objects is more involved than
constructing the corresponding tactic proofs. Fortunately, there's
a simple trick to help in the construction: we can start with a
little bit of magic defining a term `admit` that can be used as a
placeholder of any type we like.

As an example, let's walk through the process of constructing a
proof object demonstrating the beauty of `16`.

```lean
theorem even_8_atmpt_1 : Even 8 := sorry
```

Maybe we can use {name}`Even.succ_succ` to construct a term of type {lean}`Even 8`?
Recall that {name}`Even.succ_succ` is of type

```display
∀ (n : Nat), Even n → Even (n + 2)
```

If we can demonstrate that `6` is even, we should be done.

```lean
theorem even_8_atmpt_2 : Even 8 := Even.succ_succ 6 sorry
```

In the attempt above, we've omitted the proofs that `6` is even,
but it can easily be constructed following the same procedure:

```lean
theorem even_8_atmpt_3 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4 sorry)

theorem even_8_atmpt_4 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4 (Even.succ_succ 2 sorry))

theorem even_8_atmpt_5 : Even 8 :=
  Even.succ_succ 6 (Even.succ_succ 4
    (Even.succ_succ 2 (Even.succ_succ 0 Even.zero)))
```

To recap, we've been guided by an informal proof that we have in
our minds, and we check the high level details before completing
the intricacies of the proof. The `admit` term allows us to do
this.
::::::

:::dev "Claude" BeforeNextRelease
AI-TODO: Please review the hidden "Building Proof Objects Incrementally" section
above, which I (Claude) ported. Rocq's `Definition admit {T: Type} : T.
Admitted.` is dropped, and the attempts use Lean's built-in `sorry` instead
(checked in a scratch file: each attempt typechecks, with "declaration uses
`sorry`" warnings). The prose still says we _define_ a term `admit`; in Lean
nothing needs defining. Lean code inside `::::hide` is never elaborated, so
if this section is un-hidden, its blocks become live and will need the
`sorry` warnings accepted or shown. Source slip: "the beauty of `16`" should
be `8`. The heading is plain text because headings can't sit inside a
directive.

Proposed fix: review the port. If the section stays hidden, nothing else is needed; if it is un-hidden, reword "defining a term `admit`" to refer to Lean's built-in `sorry`, fix "16" to "8", and accept or show the `sorry` warnings.
:::

# Logical Connectives as Inductive Types

:::suppressPreviousHeaderWhenTerse
:::

::::full
Inductive definitions are powerful enough to express most of the
logical connectives we have seen so far.  Indeed, only universal
quantification (with implication as a special case) is built into
Rocq; all the others are defined inductively.

Let's see how.
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
`P ∧ Q` to consist of a pair of two proofs: one for `P` and
another one for `Q`. This leads to the following definition.

```lean -show
namespace AndPlayground
```

```lean
inductive And (P Q : Prop) : Prop where
  | intro : P → Q → And P Q
```

:::dev "Claude" BeforeNextRelease
AI: Lean differences for this definition:

- `∧` is fixed core syntax for core `And`, so inside `AndPlayground` our copy
  is written prefix-style, `And P Q`. (Rocq redefined `/\`.)
- Rocq's `Arguments conj [P] [Q]` is dropped: Lean makes inductive parameters
  implicit in constructors automatically.
- Core `And` and `Prod` are both `structure`s (see the `#print` below), so the
  parallel is even closer in Lean than the prose says.
:::

Notice the similarity with the definition of the {name}`Prod` type,
given in chapter {ref "Poly"}[Poly]; the only difference is that {name}`Prod` takes
`Type` arguments, whereas {name}`And` takes `Prop` arguments.

```lean (name := print_prod)
#print Prod
```

```leanOutput print_prod
structure Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
number of parameters: 2
fields:
  Prod.fst : α
  Prod.snd : β
constructor:
  Prod.mk.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) : α × β
```

:::slidebreak
:::

This similarity should clarify why `destruct` and `intro`
patterns can be used on a conjunctive hypothesis.  Case analysis
allows us to consider all possible ways in which `P ∧ Q` was
proved — here just one (the {name}`And.intro` constructor).

```lean (name := proj1'_show_proof)
theorem proj1' (P Q : Prop) (hpq : And P Q) : P := by
  show_proof
    cases hpq with
    | intro hp _ => exact hp
```

```leanOutput proj1'_show_proof
?_

after cases hpq with
| intro hp _ => exact hp:
  And.casesOn (motive := fun t => hpq = t → P) hpq (fun hp a h => hp) (Eq.refl hpq)
```

:::dev
HIDE: CH: Proof term in Show Proof above is not the simplest one,
so I would only return to it after showing proj1'' below
:::

Similarly, the `split` tactic actually works for any inductively
defined proposition with exactly one constructor.  In particular,
it works for {name}`And`:

:::dev "Claude" BeforeNextRelease
AI-TODO: Misleading in Lean, together with the "`destruct` and `intro` patterns"
sentence above.

- Lean's `split` is an unrelated tactic: it splits `if` and `match` in the
  goal. Rocq's `split` corresponds to Lean's `constructor`.
- `constructor` is _not_ limited to one-constructor types. It applies the
  first constructor that unifies with the goal. On an `Or` goal it silently
  picks `Or.inl` (verified).
- `destruct` and `intro [ … ]` become `cases`, `obtain ⟨hp, hq⟩`, and
  `intro ⟨hp, hq⟩`.

Proposed fix: change "`destruct` and `intro` patterns" to "`cases` and `obtain` patterns", and the `split` sentence to say that the `constructor` tactic works for any inductively defined proposition, applying the (here, only) constructor.
:::

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

This shows why the inductive definition of {name}`And` can be
manipulated by tactics as we've been doing.  We can also use it to
build proofs directly, using pattern-matching.  For instance:

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

:::dev "Claude" BeforeNextRelease
AI-TODO: Rocq-vs-Lean difference in `and_comm'`. Rocq's `iff` is _defined_ as a
conjunction of two implications, which is why the Rocq term builds it with
`conj`. Lean's `Iff` is its own structure, with constructor `Iff.intro` and
fields `mp`/`mpr`, so the term uses `Iff.intro`. Readers who make the Rocq
connection ("an iff is a pair of implications") need the prose to say this
explicitly; the same applies to `or_distributes_over_and` below.

Proposed fix: after the `and_comm'` block, add a sentence that `↔` is a structure whose constructor `Iff.intro` takes the two directions, so `Iff.intro` plays the role `conj` plays in Rocq.
:::

:::::exercise (rating := 2) (name := "conj_fact")
Construct a proof object for the following proposition.

```lean
theorem conj_fact : ∀ (P Q R : Prop),
    P ∧ Q → Q ∧ R → P ∧ R :=
  solution!(fun _ _ _ hpq hqr =>
    match hpq, hqr with
    | And.intro hp _, And.intro _ hr => And.intro hp hr)
```
:::::

::::::

:::::quiz
::::full
What is the type of this expression?

```display
fun P Q R (h1 : And P Q) (h2 : And Q R) =>
  match h1, h2 with
  | And.intro hp _, And.intro _ hr => And.intro hp hr
```

(A) `∀ (P Q R : Prop), P ∧ Q → Q ∧ R → P ∧ R`

(B) `∀ (P Q R : Prop), Q ∧ P → R ∧ Q → P ∧ R`

(C) `∀ (P Q R : Prop), P ∧ R`

(D) `∀ (P Q R : Prop), P ∨ Q → Q ∨ R → P ∨ R`

(E) Not typeable

:::quizSolution
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

This declaration explains the behavior of the `destruct` tactic on
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
:::::

::::::

:::::quiz
::::full
What is the type of this expression?

```display
fun P Q h =>
  match h with
  | Or.inl hp => @Or.inr Q P hp
  | Or.inr hq => @Or.inl Q P hq
```

(A) `∀ P Q H, Q ∨ P ∨ H`

(B) `∀ (P Q : Prop), P ∨ Q → P ∨ Q`

(C) `∀ P Q H, P ∨ Q → Q ∨ P → H`

(D) `∀ (P Q : Prop), P ∨ Q → Q ∨ P`

(E) Not typeable

:::quizSolution
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
To give evidence for an existential quantifier, we package a
witness `x` together with a proof that `x` satisfies the property
`P`:

```lean -show
namespace ExistsPlayground
```

```lean
inductive Exists {A : Type} (P : A → Prop) : Prop where
  | intro : ∀ (x : A), P x → Exists P
```

```lean -show
end ExistsPlayground
```

This probably needs a little unpacking.  The core definition is
for a type former {name}`Exists` that can be used to build propositions of
the form `Exists P`, where `P` itself is a _function_ from witness
values in the type `A` to propositions.  The {name}`Exists.intro`
constructor then offers a way of constructing evidence for `Exists P`,
given a witness `x` and a proof of `P x`.

The notation in the standard library is a slight extension of
the above, enabling syntactic forms such as `∃ x y, P x y`.

:::dev "Claude" BeforeNextRelease
AI-TODO: Lean differences for this section:

- Our copy is named `Exists` to mirror core (Rocq: `ex`/`ex_intro`).
- Core `Exists.intro : ∀ {α} {p : α → Prop} (w : α), p w → Exists p` takes the
  predicate _implicitly_, so Rocq's `ex_intro ev 4 (…)` becomes
  `Exists.intro 4 (…)` below.
- Rocq's `Notation "'exists' x , p"` is dropped: `∃` is core syntax, and
  `exists` is a Lean tactic keyword.

Proposed fix: after the `Exists` definition, add a sentence that core `Exists.intro` takes the predicate implicitly, so we write `Exists.intro 4 (…)`, and that `@Exists.intro Nat (fun n => Even n) 4 (…)` gives the fully explicit form (needed for the equality quiz).
:::

:::slidebreak
:::

The more familiar form `∃ x, Even x` desugars to an expression
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
/- FULL: Here's the induction principle that Rocq generates: -/

    Check ex_ind
      : forall (X: Type) (P: X->Prop) (Q: Prop),
        (forall witness:X, P witness -> Q) ->
        (exists y, P y) ->
        Q.

/- FULL: This induction principle can be understood as follows: If we have
a function [f] that can construct evidence for [Q] given _any_
witness of type [X] together with evidence that this witness has
property [P], then from a proof of [ex X P] we can extract the
witness and evidence that must have been supplied to the
constructor, give these to [f], and thus obtain a proof of [Q]. -/
```
::::

:::dev "Claude" PotentialImprovement
AI-TODO: About the hidden block above. Lean generates no `Exists.ind`; its
eliminators are `Exists.rec` and the derived `Exists.elim`.

Proposed fix: if un-hidden, port the block as `#check @Exists.elim` (or `@Exists.rec`) with a `leanOutput`, and adjust "the induction principle that Rocq generates". Otherwise leave it.
:::

:::dev
HIDE: APT21: Moved this here because it seemed misplaced further below.
:::

::::::quiz
::::full
Which of the following propositions is proved by
providing an explicit witness `w` using `exists w`?

(A) `∀ (x : Nat), (∃ n, x = n + 1) → x ≠ 0`

(B) `∀ (x : Nat), x ≠ 0 → (∃ n, x = n + 1)`

(C) `∀ (x : Nat), x = 0 → ¬(∃ n, x = n + 1)`

(D) `∀ (x : Nat), x = 4 → x ≠ 0`

(E) none of the above

:::quizSolution
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
:::::
::::::

:::slidebreak
:::

To destruct existentials in a proof term we simply use match:

```lean
theorem dist_exists_or_term (X : Type) (P Q : X → Prop) :
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
:::::
::::::

## `True` and `False`

:::suppressPreviousHeaderWhenTerse
:::

::::::full
The inductive definition of the `True` proposition is simple:

```lean
inductive True : Prop where
  | intro : True
```

It has one constructor (so every proof of `True` is the same, so
being given a proof of `True` is not informative.)

:::dev "Claude" BeforeNextRelease
AI-TODO: Lean differences for the `True`/`False` subsection:

- In Lean, _every_ proposition's proofs are all the same (definitional proof
  irrelevance; see the last section). The parenthetical above is true but
  could suggest this is special to `True`.
- `match contra with end` became `nomatch contra`. `nomatch` is not in
  STYLE-CODE's notation table yet.
- The `Fail … contra : False := 42` demo misleads in Lean. The error is
  "numerals are data in Lean, but the expected type is a proposition"
  (verified), which is about numerals, not about `False` having no
  constructors. A would-be inhabitant such as `True.intro` would give a plain
  type mismatch.

Proposed fix: replace `42` with `True.intro` in `contra`, so the error is a plain type mismatch; add `nomatch` to STYLE-CODE's notation table under ProofObjects; optionally tie the `True` parenthetical to the Proof Irrelevance section.
:::

:::::exercise (rating := 1) (name := "p_implies_true")
Construct a proof object for the following proposition.

```lean
theorem p_implies_true : ∀ (P : Prop), P → True :=
  solution!(fun _ _ => True.intro)
```
:::::

:::slidebreak
:::

`False` is equally simple — indeed, so simple it may look
syntactically wrong at first glance!

```lean
inductive False : Prop
```

That is, `False` is an inductive type with _no_ constructors —
i.e., no way to build evidence for it. For example, there is
no way to complete the following definition such that it
succeeds.

```lean +error -keep
theorem contra : False :=
  42
```

:::slidebreak
:::

But it is possible to destruct `False` by pattern matching. There can
be no patterns that match it, since it has no constructors.  So
the pattern match also is so simple it may look syntactically
wrong at first glance.

```lean
theorem false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra
```

Since there are no branches to evaluate, the `match` expression
can be considered to have any type we want, including `0 = 1`.
Fortunately, it's impossible to ever cause the `match` to be
evaluated, because we can never construct a value of type `False`
to pass to the function.

:::::exercise (rating := 1) (name := "ex_falso_quodlibet'")
Construct a proof object for the following proposition.

```lean
theorem ex_falso_quodlibet' : ∀ (P : Prop), False → P :=
  solution!(fun _ contra => nomatch contra)
```
:::::
::::::

```lean -show
end Props
```

# Equality

:::suppressPreviousHeaderWhenTerse
:::

::::::full
Even Rocq's equality relation is not built in.  We can define
it ourselves:

```lean -show
namespace EqualityPlayground
```

:::dev
```
HIDE: APT: (This) isn't exactly the library definition, which treats the
first argument as a fixed parameter, in order to give a better
induction principle. [CH: This difference is mentioned below. Is
this difference the reason we use "==" notation instead of that
from the standard library (=)? Reading on this may also have
to do with setoids?]
```
:::

```lean
inductive Eq {X : Type} : X → X → Prop where
  | refl : ∀ (x : X), Eq x x

scoped infix:50 " =' " => Eq
```

The way to think about this definition (which is just a slight
variant of the standard library's) is that, given a set `X`, it
defines a _family_ of propositions "`x` is equal to `y`," indexed
by pairs of values (`x` and `y`) from `X`.  There is just one way
of constructing evidence for members of this family: applying the
constructor {name}`Eq.refl` to a type `X` and a single value `x : X`,
which yields evidence that `x` is equal to `x`.

Other types of the form `Eq x y` where `x` and `y` are not the
same are thus uninhabited.

:::dev "Claude" BeforeNextRelease
AI-TODO: Wrong in Lean, together with the APT/CH HIDE note above. Lean
automatically promotes a fixed leading index to a parameter, so our `Eq` gets
"number of parameters: 2", exactly like core `Eq` (verified with `#print`).
Consequences:

- The Rocq "slight variant of the standard library's" (both arguments as
  indices) cannot be reproduced with this definition. Ours _is_ the library
  shape, so the APT note and the "slight variant" remark describe no
  difference in Lean.
- "Indexed by pairs of values" is inaccurate: the family is parameterized by
  `x` and indexed by `y`.
- Notation is `='` (scoped), since `==` is Lean's boolean `BEq`.

Proposed fix: delete the APT/CH HIDE note; rewrite "(which is just a slight variant of the standard library's)" as "(which mirrors the standard library's)", and "indexed by pairs of values (`x` and `y`)" as "parameterized by `x` and indexed by `y`".
:::

:::slidebreak
:::

We can use {name}`Eq.refl` to construct evidence that, for example, `2 = 2`.  Can we also use it to construct evidence that `1 + 1 = 2`?
Yes, we can.  Indeed, it is the very same piece of evidence!

The reason is that Rocq treats as "the same" any two terms that are
_convertible_ according to a simple set of computation rules.

These rules, which are similar to those used by `Compute`, include
evaluation of function application, inlining of definitions, and
simplification of `match`es.

Rocq terms are "the same" if they are _convertible_
according to a simple set of computation rules: evaluation of
function applications, inlining of definitions, and simplification
of `match`es.

```lean
theorem four : 2 + 2 =' 1 + 3 := by
  apply Eq.refl
```

:::slidebreak
:::

`reflexivity` is essentially just `apply Eq.refl`.

The `reflexivity` tactic that we have used to prove
equalities up to now is essentially just shorthand for `apply Eq.refl`.

In tactic-based proofs of equality, the conversion rules are
normally hidden in uses of `simpl` (either explicit or implicit in
other tactics such as `reflexivity`).

But you can see them directly at work in the following explicit
proof objects:

:::dev "Claude" BeforeNextRelease
AI-TODO: Misleading in Lean, for this and the convertibility paragraphs above:

- `reflexivity` becomes the `rfl` tactic, and `rfl` is _not_ just
  `apply Eq.refl`. It tries `Eq.refl`, `Iff.refl`, `HEq.refl`, and any lemma
  tagged `@[refl]`. On our `Eq` it fails ("No `[refl]` lemma registered for
  relation"; verified) unless such a lemma is added.
- `simpl` becomes `dsimp`/`rfl`.
- "Similar to those used by `Compute`" fits `#reduce` (definitional
  unfolding) better than `#eval` (compiled evaluation).
- Nuance: on `Nat` literals, `2 + 2` vs. `1 + 3` is decided by the kernel's
  built-in (GMP-accelerated) literal arithmetic, not by step-by-step
  unfolding of `Nat.add`. The "computation rules" story is idealized for
  numerals.

Proposed fix: `reflexivity` → `rfl` throughout; "essentially just `apply Eq.refl`" → true for core `=`, but note that `rfl` fails on our `='` unless a lemma is tagged `@[refl]`; `simpl` → `dsimp`; "used by `Compute`" → "used by `#reduce`".
:::

```lean
theorem four' : 2 + 2 =' 1 + 3 :=
  Eq.refl 4

theorem singleton : ∀ (X : Type) (x : X),
    [] ++ [x] =' x :: [] :=
  fun (X : Type) (x : X) => Eq.refl [x]
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

By pattern-matching against `n1 =' n2`, we obtain a term `n`
that replaces `n1` and `n2` in the type we have to produce, so
instead of `(n1 + 1) =' (n2 + 1)`, we now have to produce something
of type `(n + 1) =' (n + 1)`, which we establish by `Eq.refl (n + 1)`.

:::dev
```
HIDE: CH: Old text for reference:
"By pattern-matching against [n1 == n2], we obtain a term [n]
that is known to be convertible to both [n1] and [n2]. The term
[eq_refl (S n)] establishes [(S n) == (S n)]. The first [n] can be
converted to [n1], and the second to [n2], which yields [(S n1) ==
(S n2)]. Rocq handles all that conversion for us."

CH: This explanation seems to imply that conversion in Rocq
is symmetric. Then [eq_refl (S n1)] should work above too, but it
doesn't. I may be wrong, but to me the replacement of [n1] and
[n2] by [n] done by the destruct below seems like better intuition
for what's going on, and why one can't [eq_refl (S n1)] to prove a
goal where [n1] was already substituted away.
```
:::

:::dev "Claude" BeforeNextRelease
AI-TODO: Wrong in Lean, both the prose above and CH's note. Because the first
argument of our `Eq` is a parameter, the pattern cannot bind a fresh `n`:
`| Eq.refl n => Eq.refl (n + 1)` is rejected (`n` unknown; verified). Matching
on `heq : n1 =' n2` instead substitutes `n2 := n1`, so the code writes
`| Eq.refl _ => Eq.refl (n1 + 1)`; `eq_cons` likewise. The prose's "we obtain a
term `n`" needs rewriting, and CH's observation is reversed: `Eq.refl (n1 + 1)`
is exactly what works.

Proposed fix: rewrite the paragraph: matching on `n1 =' n2` replaces `n2` by `n1` in the type we have to produce, so we must produce `(n1 + 1) =' (n1 + 1)`, which `Eq.refl (n1 + 1)` establishes. Delete CH's HIDE note.
:::

:::slidebreak
:::

A tactic-based proof runs into some difficulties if we try to use
our usual repertoire of tactics, such as `rewrite` and
`reflexivity`. Those work with *setoid* relations that Rocq knows
about, such as `=`, but not our `='`. We could prove to Rocq that
`='` is a setoid, but a simpler way is to use `destruct` and
`apply` instead.

:::dev "Claude" BeforeNextRelease
AI-TODO: Partly wrong in Lean.

- `rw` works only with `Eq` and `Iff` ("Expected an equality or iff proof",
  verified), and core Lean has no setoid rewriting to extend it. So "we could
  prove that `==` is a setoid" has no Lean analog.
- `rfl` _can_ be extended, by tagging a reflexivity lemma `@[refl]`.
- The workaround carries over: `cases heq`, then `apply Eq.refl`.

Proposed fix: replace the setoid sentence with: `rw` only works with `=` and `↔`, and `rfl` only with relations that have a `@[refl]` lemma, so we use `cases` and `apply` instead.
:::

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

:::dev "Claude" BeforeNextRelease
AI: The Rocq proof ran `Fail rewrite` and `Fail reflexivity` _inside_ the proof
of `eq_add'`. A Verso block either succeeds or is `+error`, so they are split
out into two `+error` examples before the real proof. (The in-proof form would
need `fail_if_success`, which is not in the tactic table.) The comment "`n1` and
`n2` replaced by `n`" became "`n2` replaced by `n1`", which is what Lean does;
see the note on `eq_add`.
:::

:::::exercise (rating := 2) (name := "eq_cons")
Construct the proof object for the following theorem. Use pattern
matching on the equality hypotheses.

```lean
theorem eq_cons : ∀ (X : Type) (h1 h2 : X) (t1 t2 : List X),
    h1 =' h2 → t1 =' t2 → h1 :: t1 =' h2 :: t2 :=
  solution!(fun _ h1 _ t1 _ heq teq =>
    match heq, teq with
    | Eq.refl _, Eq.refl _ => Eq.refl (h1 :: t1))
```
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
property on `P` that is true of `x` is also true of `y`. Prove
that.

```lean
theorem equality__leibniz_equality : ∀ (X : Type) (x y : X),
    x =' y → ∀ (P : X → Prop), P x → P y := by
  solution!
    intro X x y heq P hpx
    cases heq
    exact hpx
```
:::::

:::::exercise (rating := 2) (name := "equality__leibniz_equality_term")
Construct the proof object for the previous exercise.  All it
requires is anonymous functions and pattern-matching; the large
proof term constructed by tactics in the previous exercise is
needessly complicated. Hint: pattern-match as soon as possible.

```lean
theorem equality__leibniz_equality_term :
    ∀ (X : Type) (x y : X),
    x =' y → ∀ (P : X → Prop), P x → P y :=
  solution!(fun _ _ _ heq =>
    match heq with
    | Eq.refl _ => fun _ hp => hp)
```
:::::

:::::exercise (rating := 3) (name := "leibniz_equality__equality") (optional := true)
Show that, in fact, the inductive definition of equality is
_equivalent_ to Leibniz equality.  Hint: the proof is quite short;
about all you need to do is to invent a clever property `P` to
instantiate the antecedent.

```lean
theorem leibniz_equality__equality : ∀ (X : Type) (x y : X),
    (∀ (P : X → Prop), P x → P y) → x =' y := by
  solution!
    intro X x y h
    apply h (fun z => x =' z)
    apply Eq.refl
```
:::::

:::dev
HIDE: CH: The hint here is not necessarily helpful. No "clever"
instantiation of H is needed, since Rocq can just figure it out with
a backwards proof:
:::
::::::

::::hide
```
Lemma leibniz_equality__equality_simpler : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intro X x y H. apply H. apply eq_refl.
Qed.
```
::::

:::dev "Claude" PotentialImprovement
AI-TODO: The hidden `leibniz_equality__equality_simpler` block above is still Rocq.
Proposed fix: port it as `theorem leibniz_equality__equality_simpler :
∀ (X : Type) (x y : X), (∀ (P : X → Prop), P x → P y) → x =' y := by
intro X x y h; apply h; apply Eq.refl` (checked: Lean's `apply h`
solves the higher-order unification, so CH's point still holds in
Lean).
:::

:::::quiz
::::full
Which of the following is a correct proof object for the proposition

```display
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

:::dev "Claude" BeforeNextRelease
AI-TODO: In the quiz above, the options use `@Exists.intro Nat (…)`, because core
`Exists.intro` takes the predicate implicitly. The quiz turns on the explicit
predicate argument, so `@` is needed to state options (B)–(D) at all. This
`@` form hasn't been introduced in the prose yet.

Proposed fix: introduce the `@Exists.intro` explicit form in the
Existential Quantification section (see the AI-TODO there) before this
quiz.
:::

## Inversion, Again

:::suppressPreviousHeaderWhenTerse
:::

:::dev
HIDE: PR: This section may be repetitive given the increased
attention paid to `inversion`, and it may be ineffective since
this chapter is no longer on the recommended path. We need to
think about whether this kind of reinforcement of the tactic is
needed, and if so, where to place it for best impact.

BCP 11/18: I agree — this material is a bit redundant.  On the
other hand, the examples at the end may be helpful, so maybe it's
fine to leave it.
:::

::::full
We've seen `inversion` used with both equality hypotheses and
hypotheses about inductively defined propositions.  Now that we've
seen that these are actually the same thing, we're in a position
to take a closer look at how `inversion` behaves.

:::dev "Claude" BeforeNextRelease
AI-TODO: This section is wrong for Lean as a whole. Lean has no `inversion`
tactic; IndProp uses `cases` and hand-proved inversion lemmas
(`Even.inversion`). `cases` also behaves differently from what the bullets
below describe. It unifies the constructor's indices with the hypothesis and
_substitutes_ the results, so no equations are left in the context.
Impossible cases (such as `n + 1 = 0`) are closed automatically by
no-confusion. The section needs recasting around `cases`, or cutting (the
PR/BCP note above already questions it).

Proposed fix: either cut the section (as PR/BCP already suggest), or
recast it around `cases`: for each constructor, `cases` makes a
subgoal, adds the constructor's arguments, unifies its indices with
the hypothesis and substitutes them, and closes impossible cases by
no-confusion. The three examples (`Or`, `And`, `Eq`) carry over with
`cases`.
:::

In general, the `inversion` tactic...

- takes a hypothesis `H` whose type `P` is inductively defined,
  and

- for each constructor `C` in `P`'s definition,

  - generates a new subgoal in which we assume `H` was
    built with `C`,

  - adds the arguments (premises) of `C` to the context of
    the subgoal as extra hypotheses,

  - matches the conclusion (result type) of `C` against the
    current goal and calculates a set of equalities that must
    hold in order for `C` to be applicable,

  - adds these equalities to the context (and, for convenience,
    rewrites them in the goal), and

  - if the equalities are not satisfiable (e.g., they involve
    things like `n + 1 = 0`), immediately solves the subgoal.

:::slidebreak
:::

_Example_: If we invert a hypothesis built with {name}`Or`, there are
two constructors, so two subgoals get generated.  The
conclusion (result type) of the constructor (`P ∨ Q`) doesn't
place any restrictions on the form of `P` or `Q`, so we don't get
any extra equalities in the context of the subgoal.

:::slidebreak
:::

_Example_: If we invert a hypothesis built with {name}`And`, there is
only one constructor, so only one subgoal gets generated.  Again,
the conclusion (result type) of the constructor (`P ∧ Q`) doesn't
place any restrictions on the form of `P` or `Q`, so we don't get
any extra equalities in the context of the subgoal.  The
constructor does have two arguments, though, and these can be seen
in the context in the subgoal.

:::slidebreak
:::

_Example_: If we invert a hypothesis built with {name}`Eq`, there is
again only one constructor, so only one subgoal gets generated.
Now, though, the form of the {name}`Eq.refl` constructor does give us
some extra information: it tells us that the two arguments to {name}`Eq`
must be the same!  The `inversion` tactic adds this fact to the
context.
::::

# Rocq's Trusted Computing Base

:::suppressPreviousHeaderWhenTerse
:::

::::full
One question that arises with any automated proof assistant
is "why should we trust it?" — i.e., what if there is a bug in
the implementation that renders all its reasoning suspect?

While it is impossible to allay such concerns completely, the fact
that Rocq is based on the Curry-Howard correspondence gives it a
strong foundation. Because propositions are just types and proofs
are just terms, checking that an alleged proof of a proposition is
valid just amounts to _type-checking_ the term.  Type checkers are
relatively small and straightforward programs, so the "trusted
computing base" for Rocq — the part of the code that we have to
believe is operating correctly — is small too.

What must a typechecker do?  Its primary job is to make sure that
in each function application the expected and actual argument
types match, that the arms of a `match` expression are constructor
patterns belonging to the inductive type being matched over and
all arms of the `match` return the same type, and so on.

The Coq typechecker is what actually checks our proofs.  We
have to trust it, but it's relatively small and
straightforward.

:::dev "Claude" BeforeNextRelease
AI-TODO: The rest of this section misdescribes Lean's TCB.

- *Who checks what.* Lean's elaborator compiles `match` and recursion into
  recursors (`casesOn`, `rec`, `WellFounded.fix`) _before_ the kernel sees
  them. So the exhaustiveness and termination checks happen outside the
  kernel. The kernel checks only the compiled term, which is total by
  construction. The errors below ("Missing cases: `(Or.inr _)`", "fail to show
  termination"; both verified) are still good illustrations, but they come
  from the elaborator, not the trusted checker.
- *Termination.* Lean tries structural recursion, then well-founded
  recursion (`termination_by`/`decreasing_by`). `{struct n}` corresponds to
  `termination_by structural n`, not a purely syntactic subterm check.
- *`partial def`* admits non-terminating functions, but only at return types
  Lean can show are nonempty. It rejects `{X : Type} → Nat → X` (verified),
  and the result is opaque, so `False` stays uninhabited.
- *When the kernel runs.* "When you type `Qed`" becomes: every declaration,
  tactic proofs included, is checked by the kernel when added to the
  environment.
- *TCB caveats* worth a sentence: axioms (`#print axioms`), `sorryAx`, and
  `native_decide`, which extends trust to the compiler.

Rocq-specific heading and text: "Rocq's Trusted Computing Base", and "The Coq
typechecker" in the terse line.

Proposed fix: retitle to "Lean's Trusted Computing Base"; attribute
the exhaustiveness and termination errors to the elaborator and say
the kernel only sees the compiled recursors; replace the `struct`
parenthetical with `termination_by structural n`; replace "when you
type `Qed`" with "when each declaration is added"; optionally add
`#print axioms` and a `partial def` remark.
:::

There are a few additional wrinkles:

First, since Rocq types can themselves be expressions, the checker
must normalize these (by using the computation rules) before
comparing them.

Second, the checker must make sure that `match` expressions are
_exhaustive_.  That is, there must be an arm for every possible
constructor.  To see why, consider the following alleged proof
object:

For example, it rejects this broken proof:

```lean +error -keep
theorem or_bogus : ∀ (P Q : Prop), P ∨ Q → P :=
  fun (P Q : Prop) (A : P ∨ Q) =>
    match A with
    | Or.inl h => h
```

All the types here match correctly, but the `match` only
considers one of the possible constructors for {name}`Or`.  Rocq's
exhaustiveness check will reject this definition.

Third, the checker must make sure that each recursive function
terminates.  It does this using a syntactic check to make sure
that each recursive call is on a subexpression of the original
argument.  To see why this is essential, consider this alleged
proof:

And these:

```lean +error -keep
def infinite_loop {X : Type} (n : Nat) : X :=
  infinite_loop n
termination_by structural n

theorem falso : False := infinite_loop 0
```

Recursive function `infinite_loop` purports to return a
value of any type `X` that you would like.  (The `struct`
annotation on the function tells Rocq that it recurses on argument
`n`, not `X`.)  Were Rocq to allow `infinite_loop`, then `falso`
would be definable, thus giving evidence for `False`.  So Rocq rejects
`infinite_loop`.

Note that the soundness of Rocq depends only on the
correctness of this typechecking engine, not on the tactic
machinery.  If there is a bug in a tactic implementation (which
does happen occasionally), that tactic might construct an invalid
proof term.  But when you type `Qed`, Rocq checks the term for
validity from scratch.  Only theorems whose proofs pass the
type-checker can be used in further proof developments.

The tactic language and its implementation are _not_ part
of Rocq's TCB.  This is fortunate, because complex tactics can (and
occasionally do) produce invalid proof objects.  The `Qed` command
runs the type checker to make sure that the proof object
constructed by the tactic script is valid.
::::

# More Exercises

:::suppressPreviousHeaderWhenTerse
:::

::::::full
Most of the following theorems were already proved with tactics in
{ref "Logic"}[Logic].  Now construct the proof objects for them
directly.

:::dev "Claude" PotentialImprovement
AI: `double_neg`, `contradiction_implies_anything`, `de_morgan_not_or`
(Logic) and `and_assoc` (core) already exist at the root. Rocq allows the
redefinition because each file is a module; here it works because the chapter
lives in `namespace EvenProp`, and `gradeTheorem` resolves to the `EvenProp.`
versions (the chapter builds). Inside the namespace the bare names shadow the
Logic/core ones.
:::

:::::exercise (rating := 2) (name := "and_assoc")
```lean
theorem and_assoc : ∀ (P Q R : Prop),
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  solution!(fun _ _ _ h =>
    match h with
    | And.intro hp (And.intro hq hr) =>
      And.intro (And.intro hp hq) hr)
```
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

# Proof Irrelevance (Advanced)

:::suppressPreviousHeaderWhenTerse
:::

::::::full
In {ref "Logic"}[Logic] we saw that functional extensionality could be
added to Rocq. A similar notion about propositions can also
be defined (and added as an axiom, if desired):

:::dev "Claude" BeforeNextRelease
AI-TODO: This section is wrong for Lean, and its exercises lose their point.

- *Funext.* Lean's Logic chapter presents `funext` as _provided_ by Lean (a
  theorem resting on `Quot.sound`), not as an axiom to be added, so the
  sentence above contradicts it.
- *Propext.* `propext` is already a core axiom. The definition below is
  provable outright (`fun _ _ h => propext h`; verified), so assuming it as a
  hypothesis in the exercises is vacuous.
- *Proof irrelevance.* Lean's kernel has _definitional_ proof irrelevance:
  `example (P : Prop) (h1 h2 : P) : h1 = h2 := rfl` typechecks (verified). So
  `pe_implies_pi` is provable by `rfl` without propositional extensionality.
  The "perhaps surprising consequence" framing and the hint (reduce `pf1` and
  `pf2` to `True.intro`) no longer make sense.

`pe_implies_or_eq` and `pe_implies_true_eq` keep some content. `pe_implies_pi`
needs a redesign or a cut.

Proposed fix: fix the funext sentence to match Logic ("Lean provides
`funext`"); note that `propext` is already a core axiom (show `#print
axioms` on a theorem using it); keep `pe_implies_or_eq` and
`pe_implies_true_eq`; replace `pe_implies_pi` with a short
demonstration that Lean's proof irrelevance is definitional (`example
(P : Prop) (h1 h2 : P) : h1 = h2 := by rfl`), or cut it.
:::

```lean
def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q
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
:::::

:::::exercise (rating := 1) (name := "pe_implies_true_eq") (level := Advanced)
Prove that if a proposition `P` is provable, then it is equal to
`True` — as a consequence of propositional extensionality.

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
:::::

:::::exercise (rating := 3) (name := "pe_implies_pi") (level := Advanced)
(Acknowledgment: this theorem and its proof technique are inspired
by Gert Smolka's manuscript Modeling and Proving in Computational
Type Theory Using the Coq Proof Assistant, 2021.

Another, perhaps surprising, consequence of propositional
extensionality is that it implies _proof irrelevance_, which
asserts that all proof objects for a proposition are equal.

```lean
def proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2
```

Prove that fact. Use `pe_implies_true_eq` to establish that the
proposition `P` in `proof_irrelevance` is equal to `True`. Leverage
that equality to establish that both proof objects `pf1` and
`pf2` must be just {name}`True.intro`.

```lean
theorem pe_implies_pi :
    propositional_extensionality → proof_irrelevance := by
  solution!
    unfold proof_irrelevance
    intro PE P pf1 pf2
    have h : True = P := by
      apply pe_implies_true_eq
      · exact PE
      · exact pf1
    cases h
    cases pf1
    cases pf2
    rfl
```
:::::

::::::

::::hide
```
 Local Variables:
fill-column: 70
End:
```
::::

```lean -show
end EvenProp
```
