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
import SFLMeta.RecallBlock
import LF.IndProp

set_option autoImplicit false

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Proof Objects: The Curry-Howard Correspondence" =>
%%%
htmlSplit := .never
file := "ProofObjects"
tag := "ProofObjects"
%%%

We have seen that Lean has mechanisms both for programming, using inductive
data types like {name}`Nat` or {name}`List` and functions over these types, and
for proving properties of these programs, using inductive propositions (like
{name}`Ev`), implication, universal quantification, and the like. So far, we
have mostly treated these mechanisms as if they were quite separate, and for
many purposes this is a good way to think. But we have also seen hints that
Lean's programming and proving facilities are closely related. For example, the
keyword `inductive` is used to declare both data types and propositions, and `→` is
used both to describe the type of functions on data and logical implication.
This is not just a syntactic accident! In fact, programs and proofs in Lean are
almost the same thing. In this chapter we will study this connection in more
detail.

We have already seen the fundamental idea: provability in Lean is always
witnessed by evidence. When we construct the proof of a basic proposition, we
are actually building a tree of evidence, which can be thought of as a concrete
data structure.

If the proposition is an implication like `A → B`, then its proof is an evidence
transformer: a recipe for converting evidence for `A` into evidence for `B`. So at
a fundamental level, proofs are simply programs that manipulate evidence.

Question: If evidence is data, what are propositions themselves?

Answer: They are types!

:::dev "Chris Henson (@chenson2018)"
These names can be improved
:::

Look again at the formal definition of the {name}`Ev` property.

```recallSource
inductive Ev : Nat → Prop where
  | ev_0                              : Ev 0
  | ev_succ_succ (n : Nat) (h : Ev n) : Ev (n + 2)
```

We can pronounce the ":" here as either "has type" or "is a proof of." For
example, the second line in the definition of {name}`Ev` declares that
{name}`Ev.ev_0` : {lean}`Ev 0`. Instead of "{name}`Ev.ev_0` has type {lean}`Ev
0`," we can say that "{name}`Ev.ev_0` is a proof of {lean}`Ev 0`." 

This pun between types and propositions — between : as "has type" and : as "is
a proof of" or "is evidence for" — is called the Curry-Howard correspondence.
It proposes a deep connection between the world of logic and the world of
computation:

:::table (align := center)
*
  * propositions
  * proofs
*
  * ~
  * ~
*
  * types
  * programs
:::

See {citep Bib.wadler2015}[] for a brief history and modern exposition.

Many useful insights follow from this connection. To begin with, it gives us a
natural interpretation of the type of the {name}`Ev.ev_succ_succ` constructor:

```lean (name := ev_succ_succ_type)
#print Ev.ev_succ_succ
```

```leanOutput ev_succ_succ_type
constructor Ev.ev_succ_succ : ∀ (n : Nat), Ev n → Ev (n + 2)
```
```lean -show
variable (n : Nat)
```

This can be read "{name}`Ev.ev_succ_succ` is a constructor that takes two
arguments — a number {lean}`n` and evidence for the proposition {lean}`Ev n` — and yields
evidence for the proposition {lean}`Ev (n + 2)`."

Now let's look again at an earlier proof involving {name}`Ev`. 

```lean
theorem ev_four : Ev 4 := by
  apply Ev.ev_succ_succ
  apply Ev.ev_succ_succ
  exact Ev.ev_0
```

Just as with ordinary data values and functions, we can use the `#print` command
to see the proof object that results from this proof script.

```lean (name := ev_four_print)
#print ev_four
```

```leanOutput ev_four_print
theorem ev_four : Ev 4 :=
Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

Indeed, we can also write down this proof object directly, with no need for a proof script at all:

```lean (name := ev_four_check)
#check Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

:::dev "Chris Henson (@chenson2018)"
Might want to explain/curcumvent `2 + 2`
:::

```leanOutput ev_four_check
Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0) : Ev (2 + 2)
```

The expression {lean}`Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)`
instantiates the parameterized constructor {name}`Ev.ev_succ_succ` with the specific arguments 2
and 0 plus the corresponding proof objects for its premises {lean}`Ev 2` and {lean}`Ev 0`.
Alternatively, we can think of {name}`Ev.ev_succ_succ` as a primitive "evidence
constructor" that, when applied to a particular number, wants to be further
applied to evidence that this number is even; its type,

```lean (name := check_ev)
 #check (n : Nat) → Ev n → Ev (n + 2)
```

```leanOutput check_ev
∀ (n : Nat), Ev n → Ev (n + 2) : Prop
```

expresses this functionality, in the same way that the polymorphic type `∀ X,
list X` expresses the fact that the constructor nil can be thought of as a
function from types to empty lists with elements of that type.

We saw in the Logic chapter that we can use function application syntax to
instantiate universally quantified variables in lemmas, as well as to supply
evidence for assumptions that these lemmas impose. For instance:

:::dev "Chris Henson (@chenson2018)"
need a new explanation for `by` and `:=` versus Rocq
:::

```lean
theorem ev_four' : Ev 4 := Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

# Proof Scripts

The proof objects we've been discussing lie at the core of how Lean operates.
When Lean is following a proof script, what is happening internally is that it
is gradually constructing a proof object -- a term whose type is the
proposition being proved. The tactics within a `by` block tell it how to build
up a term of the required type. To see this process in action, let's use the
{tactic}`show_term` tactic to display the current state of the proof tree at
various points in the following tactic proof. 

```lean
theorem ev_four'' : Ev 4 := by
  show_term
  show_term apply Ev.ev_succ_succ
  show_term apply Ev.ev_succ_succ
  exact Ev.ev_0
```

At any given moment, Lean has constructed a term with a "hole" (indicated by
`?_` here, and so on), and it knows what type of evidence is needed to fill
this hole.

Each hole corresponds to a subgoal, and the proof is finished when there are no
more subgoals. At this point, the evidence we've built is stored in the
environment under the name given in the `theorem` command.

Tactic proofs are convenient, but they are not essential in Lean: in principle,
we can always just construct the required evidence by hand.

```lean
theorem ev_four''' : Ev 4 := Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

All these different ways of building the proof lead to exactly the same
evidence being saved in the environment

```lean (name := print_ev_four)
#print ev_four
```

```leanOutput print_ev_four
theorem ev_four : Ev 4 :=
Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

```lean (name := print_ev_four')
#print ev_four'
```

```leanOutput print_ev_four'
theorem ev_four' : Ev 4 :=
Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

```lean (name := print_ev_four'')
#print ev_four''
```

```leanOutput print_ev_four''
theorem ev_four'' : Ev 4 :=
Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

```lean (name := print_ev_four''')
#print ev_four'''
```

```leanOutput print_ev_four'''
theorem ev_four''' : Ev 4 :=
Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)
```

# Quantifiers, Implications, Functions

:::dev "Chris Henson (@chenson2018)"
this section needs to be completely different for omitted
:::

# Programming with Tactics

# Logical Connectives as Inductive Types

# Equality

# Lean's Trusted Computing Base

# More Exercises

# Proof Irrelevance (Advanced)

# 
