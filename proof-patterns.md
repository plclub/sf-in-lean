## THIS IS A DRAFT 

The biggest things this needs is:
proof patterns beyond induction 
some fixed verbiage that changes "induction on a type" to something more specific. 
what I mean is "induction on a term of a non-`Prop` inductive type", but that's too verbose. 

# Proof Patterns
You have probably already had this experience: 
You're writing a proof in Lean, and you don't know where to start. So you observe one of the following, and try a corresponding step: 

- You see an inductive type like `Nat` or `list` in the goal, and use `induction` on it.
- You see a goal of the form `∀ n, ...` and type `intro n` to fix the variable. 
- You see a boolean `b` in the context and use `cases b` to consider if `b` is `true` or `false`.

These patterns of observation and action, or "proof patterns," are a a natural consequence of our pattern-matching brains seeing something we recognize and grabbing onto it 
to try to make progress. Indeed, these are often helpful to state explicitly for beginners to recognize- though one must always take care to remember that applying a proof pattern will not _always_
make progress! Sometimes a proof requires more subtle reasoning or the use of other theorems to progress in a meaningful way. With this in mind, we write a few of them here 
for convenience. 

## Induction
There are two types of 'thing' we can use `induction` on: 
1. an inductive _type_, like `Nat`, `list`, or a term `Tm` of some language, and
2. an inductive _proposition_, like `le` (`≤`), a permutation `Perm l l'`, or a typing judgement of the form `Γ ⊢ e : τ`.

When we say an inductive type (or proposition), we mean a type (or proposition) that was defined inductively- i.e., using the `inductive` keyword. 

Very often in this book, if you have some kind of inductive type or proposition available to you, a proof by induction is a reasonable way forward! 
Again, this is not always the case, but it is often a good first step. 


### Choosing what to induct on 
How should you know which one to use `induction` on if more than one inductive type is available, 
or more than one inductive proposition, or both? Sometimes there is more than one right answer, 
but there is very often one _best_ answer. 

The answer to this question often comes in the form of a piece of insight: 
induction on a _type_ is like saying, "I will show this goal is true based on the different ways the type can be constructed,"
where induction on a _proposition_ is like saying, "I will show this goal is true based on the different ways the proposition can hold." 
This can often elucidate the 'better' way to proceed: 

### Induction on Types
For `n : Nat`, for example, this would be to show a goal of the form `P n` is true, where `P : Nat -> Prop`, based on the ways `n` can be constructed: 
namely, `0` and `succ`. So we will have to show `P 0` and `P n -> P (succ n)`, where `P n` is our inductive hypothesis. 

One way to target the 'right' variable to do induction on is: if any variable is going to be the _scrutinee_ of a pattern match--- that is, 
the variable being matched on:

```lean4
      ↶ the scrutinee, n 
match n with
| ...
| ... 

```

that is likely the right target for induction. In fact, a good way to know to use `induction x` over `cases x` for some `x` is when 
`x` is the scrutinee of a pattern match and one or more of the branches calls a function recursively over a subterm of `x`, like so: 

```lean4
def add (n m : Nat) : Nat := 
match m with
| zero => n
| succ m' => succ (add n m')

theorem add_comm (n m : Nat) : n + m = m + n := by ... 
```


Here, we should use `induction m` rather than `induction n`, as this way we are lining up the induction and recursion and are 
much more likely to succeed. 

Exercise: write out the goal states after `induction m`, including contexts. 

### Induction on Propositions
While induction on a type considers solving the goal more or less by case analysis on the type (with an inductive hypothesis for the self-referential cases), 
induction on a _proposition_ `h` is to say, "I will solve this goal by considering the ways `h` can hold true." This is often less intuitive, but it is 
often much more powerful than inducting on a type, as it can tell us much more. 

For example, say we have this proof state: 

```lean4
n m : Nat
h : n ≤ m
⊢ P n m
```

Then `induction h` will give us a goal for all the ways `h : n ≤ m` can hold true. 
Thinking mathematically, this is pretty straightforward: if we know `n` is less than or equal to `m`, we know 
either `n` equals `m` or `n` is less than `m`! The proof-assistant view is exactly analogous of this:
As `≤` is an inductively-defined proposition, we know it must be that `h` can only hold if one of the two constructors 
of `≤` holds on `n` and `m`; that is, either `refl` holds, so `n = m` or `step` holds, so `n ≤ m'`, where `m = S m'`. 
In the `step` case, since `n ≤ m'` still uses `≤`, it is our inductive hypothesis. 

Exercise: write out the goal states after `induction h`, including contexts. 

Inducting on a proposition nearly always gives more information than inducting on a type. In fact, many proofs in research papers 
(whether they use Lean or not) will begin with: "By induction on the assumption that ...". That "assumption" is exactly an inductive proposition!
