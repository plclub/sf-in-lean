/- Imp: Simple Imperative Programs -/

-- Claude: This chapter is being ported from the Rocq `Imp.v` to Lean by
-- Claude.  Human review is needed, especially of the prose and of the
-- pedagogical choices flagged in `MWH`/`dev` notes below.
-- Claude: Some author notes below concern material that is specific to Rocq
-- and has no Lean analogue as yet (the `<{ }>` custom grammar, `Set Printing
-- …`, `Locate`); they are left as notes for a future translation pass to
-- decide what, if anything, the Lean chapter should do instead.  The
-- `HIDEFROMADVANCED` track marker is kept where it wraps a distinct block;
-- `HIDEFROMHTML` (which only ever wraps `Module`/`Require`/`Reserved
-- Notation` lines) has no content or Lean meaning and is not used here.

-- The `INSTRUCTORS`/`BCP`/`SOONER`/`LATER`/`NDS'25`/… blocks throughout this
-- file are internal author notes about further work, not part of the chapter
-- text.
/- INSTRUCTORS: This chapter plus `Maps` takes a little more than one
   80-minute lecture.  It could be streamlined a bit further without
   losing much, by removing (for example) the inference rules and BNF
   notations from the terse version.

   (BCP 21: ... Actually, I tried removing inference rules from the
   TERSE version; eventually decided that it makes some of the
   definitions harder to talk about.) -/
/- SOONER: Needs some WORKINCLASSes and some quizzes -/
/- SOONER: We still need to adjust the explanations of notations in Imp,
   Hoare, and Stlc from some earlier changes... -/
/- LATER: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare (reasoning about arrays /
   aliasing / etc.). -/
/- SOONER: BCP 25: Maybe we should write /\ instead of && in assertions,
   to save a mismatch in the dec_minimum exercise in Hoare2? -/
/- HIDE: At some point we could consider moving material from the old
   HoareLists.v to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures.
   Also, we now have a whole volume on real separation logic... -/
/- HIDE: Check out 8.14 / 8/15 Notation changes -- in particular, note that
   identifiers can now elaborate to strings in a custom grammar -- this may
   help a lot in PLF!
   The release notes now include a section on Notation changes. See
   https://coq.github.io/doc/v8.15/refman/changes.html#id15 for 8.15 and
   https://coq.github.io/doc/v8.14/refman/changes.html#id19 for 8.14
   NDS'25: That does not seem right. I could not find anything to that effect
   in the changelogs, and this hack (from 2022!) also seems to contradict
   this statement: https://github.com/rocq-prover/rocq/issues/15643 -/

-- MWH (port note): Datatype constructors follow Lean naming conventions --
-- lowerCamelCase with no redundant type-name prefix.  `Aexp` is `num`/`id`/
-- `plus`/`minus`/`mult`; `Bexp` folds the two booleans into a single
-- `bool (b : Bool)` constructor (like `num (n : Nat)`) plus `eq`/`neq`/`le`/
-- `gt`/`not`/`and`; `Com` is `skip`/`asgn`/`seq`/`cond`/`whileDo`.
-- Inference-rule constructors keep their SF names (`E_*`, `ST_*`, `nw_*`).
-- Functions on a type live in that type's namespace (`Aexp.eval`,
-- `Bexp.eval`, `Aexp.optimize_0plus`, `Com.no_whiles`, …), so their match
-- bodies use the bare constructor names.  (Convention applied per the
-- chenson2018 PR review.)
-- MWH (port note): The Rocq chapter's "Rocq Automation" tour has been
-- retooled here for Lean.  The tactic *combinators* (`try`, `<;>`,
-- `repeat`) are introduced in this chapter; `simp` was already introduced in
-- Logical Foundations, so we use it freely.  For linear arithmetic we use
-- `lia` (the newer `grind`-based tactic, per the chenson2018 review);
-- NOTE that LF currently introduces `omega`, not `lia`, so this needs to be
-- reconciled volume-wide (either introduce `lia` in LF, or keep `omega`).

import LF.Maps

-- FULL
/-
  In this chapter, we take a more serious look at how to use Lean as a
  tool to study other things.  Our case study is a _simple imperative
  programming language_ called Imp, embodying a tiny core fragment of
  conventional mainstream languages such as C and Java.

  Here is a familiar mathematical function written in Imp.

  ```
  Z := X;
  Y := 1;
  while Z <> 0 do
    Y := Y * Z;
    Z := Z - 1
  end
  ```
-/
-- /FULL
-- HIDEFROMADVANCED
/-
  We concentrate here on defining the _syntax_ and _semantics_ of Imp;
  later, in _Programming Language Foundations_ (_Software Foundations_,
  volume 2), we develop a theory of _program equivalence_ and introduce
  _Hoare Logic_, a popular logic for reasoning about imperative programs.
-/
-- /HIDEFROMADVANCED

/-
  ######################################################################
  # Arithmetic and Boolean Expressions
-/

/- SOONER: At this point, I usually take some of the lecture time to
   give a high-level picture of the structure of an interpreter, the
   processes of lexing and parsing, the notion of ASTs, etc.  Might be
   nice to work some of those ideas into the notes. - BCP -/

-- FULL
/-
  We'll present Imp in three parts: first a core language of _arithmetic
  and boolean expressions_, then an extension of these with _variables_,
  and finally a language of _commands_ including assignment, conditionals,
  sequencing, and loops.
-/
-- /FULL

/-
  ######################################################################
  ## Syntax
-/

namespace AExp

-- FULL
/-
  These two definitions specify the _abstract syntax_ of arithmetic and
  boolean expressions.
-/
-- /FULL
-- TERSE: /- Abstract syntax trees for arithmetic and boolean expressions: -/

inductive Aexp where
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)

-- FULL
/-
  In this chapter, we'll mostly elide the translation from the concrete
  syntax that a programmer would actually write to these abstract syntax
  trees -- the process that, for example, would translate the string
  `"1 + 2 * 3"` to the AST

  ```
  .plus (.num 1) (.mult (.num 2) (.num 3))
  ```

  The optional chapter `ImpParser` develops a simple lexical analyzer and
  parser that can perform this translation.  You do not need to understand
  that chapter to understand this one, but if you haven't already taken a
  course where these techniques are covered (e.g., a course on compilers)
  you may want to skim it.

  For comparison, here's a conventional BNF (Backus-Naur Form) grammar
  defining the same abstract syntax:

  ```
  a := nat
      | a + a
      | a - a
      | a * a

  b := true
      | false
      | a = a
      | a <> a
      | a <= a
      | a > a
      | ~ b
      | b && b
  ```

  Compared to the Lean version above...

    - The BNF is more informal -- for example, it gives some suggestions
      about the surface syntax of expressions (like the fact that the
      addition operation is written with an infix `+`) while leaving other
      aspects of lexical analysis and parsing (like the relative precedence
      of `+`, `-`, and `*`, the use of parens to group subexpressions, etc.)
      unspecified.  Some additional information -- and human intelligence --
      would be required to turn this description into a formal definition,
      e.g., for implementing a compiler.

      The Lean version consistently omits all this information and
      concentrates on the abstract syntax only.

    - Conversely, the BNF version is lighter and easier to read.  Its
      informality makes it flexible, a big advantage in situations like
      discussions at the blackboard, where conveying general ideas is more
      important than nailing down every detail precisely.

      Indeed, there are dozens of BNF-like notations and people switch
      freely among them -- usually without bothering to say which kind of
      BNF they're using, because there is no need to: a rough-and-ready
      informal understanding is all that's important.

  It's good to be comfortable with both sorts of notations: informal ones
  for communicating between humans and formal ones for carrying out
  implementations and proofs.
-/
-- /FULL

/-
  ######################################################################
  ## Evaluation
-/

/- _Evaluating_ an arithmetic expression produces a number. -/

def Aexp.eval (a : Aexp) : Nat :=
  match a with
  | num n => n
  | plus  a1 a2 => eval a1 + eval a2
  | minus a1 a2 => eval a1 - eval a2
  | mult  a1 a2 => eval a1 * eval a2

example : Aexp.eval (.plus (.num 2) (.num 2)) = 4 := by rfl

/- Similarly, evaluating a boolean expression yields a boolean. -/

def Bexp.eval (b : Bexp) : Bool :=
  match b with
  | bool b     => b
  | eq a1 a2  => a1.eval == a2.eval
  | neq a1 a2 => a1.eval != a2.eval
  | le a1 a2  => a1.eval ≤ a2.eval
  | gt a1 a2  => a1.eval > a2.eval
  | not b1    => !eval b1
  | and b1 b2 => eval b1 && eval b2

-- QUIZ
/-
  What does the following expression evaluate to?

  ```
  Aexp.eval (.plus (.num 3) (.minus (.num 4) (.num 1)))
  ```

  (A) true    (B) false    (C) 0    (D) 3    (E) 6
-/
-- /QUIZ

/-
  ######################################################################
  ## Optimization
-/

-- FULL
/-
  We haven't defined very much yet, but we can already get some mileage
  out of the definitions.  Suppose we define a function that takes an
  arithmetic expression and slightly simplifies it, changing every
  occurrence of `0 + e` (i.e., `.plus (.num 0) e`) into just `e`.
-/
-- /FULL

def Aexp.optimize_0plus (a : Aexp) : Aexp :=
  match a with
  | num n => num n
  | plus (num 0) e2 => optimize_0plus e2
  | plus  e1 e2 => plus  (optimize_0plus e1) (optimize_0plus e2)
  | minus e1 e2 => minus (optimize_0plus e1) (optimize_0plus e2)
  | mult  e1 e2 => mult  (optimize_0plus e1) (optimize_0plus e2)

-- FULL
/-
  To gain confidence that our optimization is doing the right thing we
  can test it on some examples and see if the output looks OK.
-/
-- /FULL

/- test_optimize_0plus -/
example :
    Aexp.optimize_0plus (.plus (.num 2)
                     (.plus (.num 0)
                       (.plus (.num 0) (.num 1))))
      = .plus (.num 2) (.num 1) := by rfl

-- FULL
/-
  But if we want to be certain the optimization is correct -- that
  evaluating an optimized expression _always_ gives the same result as
  the original -- we should prove it!

  Here is a first, deliberately explicit proof.  It works, but notice how
  much of it is repetitive: several cases are discharged by exactly the
  same three-step incantation.
-/
-- /FULL

theorem optimize_0plus_sound (a : Aexp) :
    Aexp.eval (Aexp.optimize_0plus a) = Aexp.eval a := by
  induction a with
  | num n => rfl
  | plus a1 a2 ih1 ih2 =>
    cases a1 with
    | num n =>
      cases n with
      | zero =>
        simp only [Aexp.optimize_0plus, Aexp.eval, Nat.zero_add]
        exact ih2
      | succ n =>
        simp only [Aexp.optimize_0plus, Aexp.eval]
        rw [ih2]
    | plus b1 b2 =>
      simp only [Aexp.optimize_0plus, Aexp.eval] at ih1 ⊢
      rw [ih1, ih2]
    | minus b1 b2 =>
      simp only [Aexp.optimize_0plus, Aexp.eval] at ih1 ⊢
      rw [ih1, ih2]
    | mult b1 b2 =>
      simp only [Aexp.optimize_0plus, Aexp.eval] at ih1 ⊢
      rw [ih1, ih2]
  | minus a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize_0plus, Aexp.eval]
    rw [ih1, ih2]
  | mult a1 a2 ih1 ih2 =>
    simp only [Aexp.optimize_0plus, Aexp.eval]
    rw [ih1, ih2]

/-
  ######################################################################
  # Tactic Combinators
-/

-- FULL
/-
  The amount of repetition in that last proof is a little annoying.  And
  if either the language of arithmetic expressions or the optimization
  being proved sound were significantly more complex, it would start to be
  a real problem.

  So far, we've been driving each subgoal by hand.  Lean also provides
  _combinators_ that build bigger tactics out of smaller ones, letting us
  discharge many similar subgoals at once.  Getting used to them takes a
  little energy, but it lets us scale up to more complex definitions and
  more interesting properties without drowning in boring, repetitive
  detail.
-/
-- /FULL
-- TERSE: /- That last proof was repetitive.  Time for a few combinators. -/

/-
  ######################################################################
  ## The `try` combinator
-/

/- LATER: put `<;>`/`;` before `try`? -/

/-
  If `t` is a tactic, then `try t` is a tactic that is just like `t`
  except that, if `t` fails, `try t` _successfully_ does nothing at all
  (rather than failing).
-/

/- LATER: Maybe we want to move the discussion of "try solve" from later to
   here?  It might be helpful for students, but it will make this
   already-longish chapter a bit longer... -/

theorem silly1 (P : Prop) (hp : P) : P := by
  try rfl -- `rfl` would fail here, but `try` swallows the failure...
  exact hp -- ...so we can still finish some other way.

theorem silly2 (ae : Aexp) : Aexp.eval ae = Aexp.eval ae := by
  try rfl -- here `try rfl` just does `rfl`

/-
  There is not much reason to use `try` in completely manual proofs like
  these, but it is very useful together with the `<;>` combinator, which
  we show next.
-/

/-
  ######################################################################
  ## The `<;>` combinator
-/

/-
  The compound tactic `t <;> t'` first performs `t` and then performs `t'`
  on _each subgoal_ generated by `t`.

  For example, consider the following trivial lemma.  Splitting on `n`
  leaves two subgoals that are discharged identically:
-/

theorem foo (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero   => lia
  | succ k => lia

-- TERSE: /- We can collapse the two identical branches with `<;>`: -/
theorem foo' (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n <;> lia -- run `cases n`, then `lia` on each subgoal

-- FULL
/-
  Using `<;>` we can get rid of the repetition in the proof that was
  bothering us a little while ago.  Most cases follow directly from the
  induction hypotheses, so we can dispatch them uniformly and only pause
  on the interesting one.
-/
-- /FULL

theorem optimize_0plus_sound' (a : Aexp) :
    Aexp.eval (Aexp.optimize_0plus a) = Aexp.eval a := by
  induction a with
  | num n => rfl
  | plus a1 a2 ih1 ih2 =>
    -- The interesting case: split on the shape of `a1`; when it is a
    -- literal we must additionally check whether it is `0`.
    cases a1 with
    | num n => cases n <;> simp_all [Aexp.optimize_0plus, Aexp.eval]
    | plus b1 b2  => simp_all [Aexp.optimize_0plus, Aexp.eval]
    | minus b1 b2 => simp_all [Aexp.optimize_0plus, Aexp.eval]
    | mult b1 b2  => simp_all [Aexp.optimize_0plus, Aexp.eval]
  | minus a1 a2 ih1 ih2 => simp_all [Aexp.optimize_0plus, Aexp.eval]
  | mult a1 a2 ih1 ih2 => simp_all [Aexp.optimize_0plus, Aexp.eval]

-- HIDEFROMADVANCED
-- FULL
/-
  Experts often use this "`… <;> try …`" idiom after a tactic like
  `induction` to take care of many similar cases all at once.  Indeed, this
  practice has an analog in informal proofs.  For example, here is an informal
  proof of the optimization theorem that matches the structure of the formal
  one:

  _Theorem_: For all arithmetic expressions `a`,

  ```
  Aexp.eval (Aexp.optimize_0plus a) = Aexp.eval a.
  ```

  _Proof_: By induction on `a`.  Most cases follow directly from the IH.
  The remaining cases are as follows:

    - Suppose `a = .num n` for some `n`.  We must show

      ```
      Aexp.eval (Aexp.optimize_0plus (.num n)) = Aexp.eval (.num n).
      ```

      This is immediate from the definition of `Aexp.optimize_0plus`.

    - Suppose `a = .plus a1 a2` for some `a1` and `a2`.  We must show

      ```
      Aexp.eval (Aexp.optimize_0plus (.plus a1 a2)) = Aexp.eval (.plus a1 a2).
      ```

      Consider the possible forms of `a1`.  For most of them,
      `Aexp.optimize_0plus` simply calls itself recursively for the
      subexpressions and rebuilds a new expression of the same form as
      `a1`; in these cases, the result follows directly from the IH.

      The interesting case is when `a1 = .num n` for some `n`.  If `n = 0`,
      then

      ```
      Aexp.optimize_0plus (.plus a1 a2) = Aexp.optimize_0plus a2
      ```

      and the IH for `a2` is exactly what we need.  On the other hand, if
      `n = n' + 1` for some `n'`, then again `Aexp.optimize_0plus` simply calls
      itself recursively, and the result follows from the IH.  ∎
-/
-- /FULL
-- /HIDEFROMADVANCED

-- FULL
/-
  However, this proof can still be improved: the first case (for
  `a = .num n`) is very trivial -- even more trivial than the cases that
  we said simply followed from the IH -- yet in a fully explicit proof we
  would write it out in full.  It would be better and clearer to drop it and
  just say, at the top, "Most cases are either immediate or direct from the
  IH.  The only interesting case is the one for `.plus`..."  Our `<;>`
  version above already does exactly this.
-/
-- /FULL

/- Claude: A further refinement of the explicit proof appears in `Imp.v` as a
   second theorem, `optimize_0plus_sound''`.  Our `<;>` version above already
   captures the same improvement, so there is nothing more to do here; the
   Rocq proof is kept only as a reference for a future pass to weigh whether a
   distinct Lean variant adds anything:

   ```
   Theorem optimize_0plus_sound'': forall a,
     eval (optimize_0plus a) = eval a.
   Proof.
     intros a.
     induction a;
       (* Most cases follow directly by the IH *)
       try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
       (* ... or are immediate by definition *)
       try reflexivity.
     (* The interesting case is when a = APlus a1 a2. *)
     - (* APlus *)
       destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                         rewrite IHa2; reflexivity).
       + (* a1 = ANum n *) destruct n;
         simpl; rewrite IHa2; reflexivity. Qed.
   ``` -/

/- Claude: The `;` tactical has a more general form worth noting.  Its uniform
   case corresponds to Lean's `<;>` (covered in this chapter); running
   *different* tactics on different subgoals corresponds in Lean to focusing
   with `case`/`·`, which was introduced in an earlier lesson, so this chapter
   does not re-teach it.  For reference: in Rocq, if `T`, `T1`, ..., `Tn` are
   tactics, then

   ```
   T; [T1 | T2 | ... | Tn]
   ```

   first performs `T` and then performs `T1` on the first subgoal generated by
   `T`, `T2` on the second subgoal, etc.  So `T;T'` is just the special case
   where every `Ti` is the same tactic (`T; [T' | T' | ... | T']`).  The
   bracketed-list form has no direct Lean surface syntax. -/

/-
  ######################################################################
  ## The `repeat` combinator
-/

/- LATER: The `do` tactic could also be introduced before the `repeat`
   tactic. -/

/-
  The `repeat` combinator takes another tactic and keeps applying it until
  it fails or until it succeeds but makes no further progress.

  For example, the following proof keeps trying to close the goal with an
  assumption and, failing that, to split it with a constructor, until
  nothing is left to do:
-/

theorem repeat_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q ∧ P ∧ Q := by
  repeat first | exact hp | exact hq | constructor

/-
  The tactic `repeat t` never fails: if `t` doesn't apply to the goal,
  then `repeat` _succeeds_ without changing anything (i.e., it repeats
  zero times).  It also has no upper bound on the number of iterations, so
  a tactic that always makes progress will make `repeat` loop forever.
  Unlike evaluation of Lean _terms_, which is guaranteed to terminate,
  _tactic_ evaluation is not -- but this never threatens soundness: a
  diverging tactic just fails to build a proof.
-/

/- Claude: `repeat` can be illustrated with a few more examples that lean on
   Rocq-specific tactics/lemmas; a future pass could decide whether Lean
   analogues are worth adding.  In Rocq, `10 ∈ [1..10]` was proved first with
   `repeat`:

   ```
   Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
   Proof.
     repeat (try (left; reflexivity); right).
   Qed.
   ```

   then again to show `repeat T` succeeds even when `T` never applies:

   ```
   Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
   Proof.
     repeat simpl.
     repeat (left; reflexivity).
     repeat (right; try (left; reflexivity)).
   Qed.
   ```

   and the infinite-loop hazard was shown with a deliberately non-terminating
   script (the body always makes progress, so `repeat` never stops):

   ```
   Theorem repeat_loop : forall (m n : nat),
     m + n = n + m.
   Proof.
     intros m n.
     (* Uncomment the next line to see the infinite loop occur.  You will
        then need to interrupt Rocq to make it listen to you again.  (In
        Proof General, [C-c C-c] does this.) *)
     (* SOONER: BCP 23: What about in VSCoq? *)
     (* repeat rewrite Nat.add_comm. *)
   Admitted.
   ``` -/

/-
  ######################################################################
  ## Defining new tactics
-/

-- FULL
/-
  Lean also lets us "program" in tactic scripts.  The simplest facility is
  a `macro`, which bundles several tactics into a single new command.  (For
  more sophisticated proof automation Lean offers `macro_rules`, `syntax`,
  and a full metaprogramming API written in Lean itself; see the
  _Metaprogramming in Lean_ book.)

  For example, here is a tiny tactic `crush_conj` that fully splits a goal
  built from `∧` and closes each atom by assumption:
-/
-- /FULL

macro "crush_conj" : tactic => `(tactic| repeat first | assumption | constructor)

theorem crush_example (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (Q ∧ P) := by
  crush_conj

/- Claude: The `macro` above is Lean's counterpart to Rocq's `Ltac` for
   bundling tactics; this note keeps the `Ltac` treatment for reference in a
   future pass.  The `Ltac` idiom defines "shorthand tactics"; it also
   supports syntactic pattern-matching on the goal and context and general
   programming.  A good reference is the textbook "Certified Programming with
   Dependent Types" (CPDT).  Rocq's two other ways of defining tactics -- a
   `Tactic Notation` command and a low-level OCaml API -- correspond in Lean
   to `macro_rules`/`syntax` and the metaprogramming API.  The example `Ltac`
   script:

   ```
   Ltac invert H :=
     inversion H; subst; clear H.
   ```

   defines a tactic `invert` that runs `inversion H; subst; clear H` -- a
   quick way to invert evidence/constructors, rewrite with the generated
   equations, and drop the redundant hypothesis:

   ```
   Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
     intros.
     invert H.
     reflexivity.
   Qed.
   ``` -/

/-
  ######################################################################
  ## The `lia` tactic
-/

-- FULL
/-
  `lia` is a decision procedure for linear arithmetic over the integers and
  naturals.  If the goal is built from

    - numeric constants, addition, subtraction, and multiplication by
      constants,
    - equality (`=`, `≠`) and ordering (`≤`, `<`, `≥`, `>`), and
    - the logical connectives `∧`, `∨`, `¬`, and `→`,

  then `lia` will either solve it or report that it is false.  (Rocq users
  will recognize the name; `lia` is also the name of the corresponding Rocq
  tactic.  Lean's older `omega` does the same job.)
-/
-- /FULL

example (m n o p : Nat) (h : m + n ≤ n + o ∧ o + 3 = p + 3) : m ≤ p := by
  lia

example (m n : Nat) : m + n = n + m := by lia

example (m n p : Nat) : m + (n + p) = m + n + p := by lia

/-
  ######################################################################
  ## A few more handy tactics
-/

/- SOONER: Have we really not introduced any of these? (e.g. subst?) -/

/-
  Finally, here are some miscellaneous tactics -- all introduced in
  Logical Foundations -- that you may find convenient here:

    - `clear h`: delete hypothesis `h` from the context.

    - `subst x`: given a variable `x` with an assumption `x = e` or
      `e = x`, replace `x` by `e` everywhere and clear the assumption;
      `subst_vars` does this for _all_ such assumptions at once.

    - `rename_i x`: give a fresh, readable name to an inaccessible
      hypothesis introduced automatically by a tactic.

    - `assumption`: find a hypothesis that exactly matches the goal and
      use it.

    - `contradiction`: find a hypothesis that is logically `False` and
      close the goal.

    - `constructor`: apply a constructor of the goal's inductive type.
-/

/-
  ######################################################################
  # Optimizing Booleans
-/

-- EX3 (optimize_0plus_b_sound)
/-
  Since the `Aexp.optimize_0plus` transformation doesn't change the value of an
  `Aexp`, we should be able to apply it to all the `Aexp`s that appear in a
  `Bexp` without changing the `Bexp`'s value.  Write a function that
  performs this transformation on `Bexp`s and prove it sound.  Use the
  combinators we've just seen to make the proof as short and elegant as
  possible.
-/

def Bexp.optimize_0plus_b (b : Bexp) : Bexp :=
  -- ADMITDEF
  match b with
  | bool b     => bool b
  | eq a1 a2  => eq a1.optimize_0plus a2.optimize_0plus
  | neq a1 a2 => neq a1.optimize_0plus a2.optimize_0plus
  | le a1 a2  => le a1.optimize_0plus a2.optimize_0plus
  | gt a1 a2  => gt a1.optimize_0plus a2.optimize_0plus
  | not b1    => not (optimize_0plus_b b1)
  | and b1 b2 => and (optimize_0plus_b b1) (optimize_0plus_b b2)
  -- /ADMITDEF

/- optimize_0plus_b_test1 -/
example :
    Bexp.optimize_0plus_b (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = .not (.gt (.num 4) (.num 8)) := by rfl -- ADMITTED
-- GRADE_THEOREM 0.5: optimize_0plus_b_test1

/- optimize_0plus_b_test2 -/
example :
    Bexp.optimize_0plus_b (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = .and (.le (.num 4) (.num 5)) (.bool true) := by rfl -- ADMITTED
-- GRADE_THEOREM 0.5: optimize_0plus_b_test2

theorem optimize_0plus_b_sound (b : Bexp) :
    Bexp.eval (Bexp.optimize_0plus_b b) = Bexp.eval b := by
  -- ADMITTED
  induction b with
  | not b1 ih => simp only [Bexp.optimize_0plus_b, Bexp.eval]; rw [ih]
  | and b1 b2 ih1 ih2 => simp only [Bexp.optimize_0plus_b, Bexp.eval]; rw [ih1, ih2]
  | _ => simp only [Bexp.optimize_0plus_b, Bexp.eval, optimize_0plus_sound]
  -- /ADMITTED
-- GRADE_THEOREM 2: optimize_0plus_b_sound
-- []

/-
  ######################################################################
  # Evaluation as a Relation
-/

-- FULL
/-
  We have presented `Aexp.eval` and `Bexp.eval` as functions defined by
  recursion.  Another way to think about evaluation -- one that is often
  more flexible -- is as a _relation_ between expressions and their
  values.  This perspective leads to inductive definitions like the
  following.  We name the hypotheses in each case (`h1`, `h2`); this
  gives us readable names to refer to during proofs.
-/
-- /FULL

inductive AevalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) :
      AevalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.mult a1 a2) (n1 * n2)

-- FULL
/-
  A small notational aside.  We could instead have presented this relation
  with *positional* hypotheses -- no names for the premises:

  ```
  inductive AevalR : Aexp → Nat → Prop where
    | E_ANum (n : Nat) :
        AevalR (.num n) n
    | E_APlus (e1 e2 : Aexp) (n1 n2 : Nat) :
        AevalR e1 n1 →
        AevalR e2 n2 →
        AevalR (.plus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2 : Aexp) (n1 n2 : Nat) :
        AevalR e1 n1 →
        AevalR e2 n2 →
        AevalR (.minus e1 e2) (n1 - n2)
    | E_AMult (e1 e2 : Aexp) (n1 n2 : Nat) :
        AevalR e1 n1 →
        AevalR e2 n2 →
        AevalR (.mult e1 e2) (n1 * n2)
  ```

  The version above instead gives explicit names to the hypotheses in each
  case (the `h1`/`h2`).  Naming the hypotheses gives us more control over the
  names chosen during proofs involving the relation, at the cost of making
  the definition a little more verbose.  We adopt the named style.
-/
-- /FULL

/-
  It will be convenient to have an infix notation for `AevalR`.  We'll
  write `e ==> n` to mean that arithmetic expression `e` evaluates to
  value `n`.  (We scope the notation to this namespace so it doesn't
  collide with other evaluation relations later.)  In Lean the notation is
  declared right after the inductive.
-/
/- HIDE: OLD: (This notation is one place where the limitation to ASCII
   symbols becomes a little bothersome.  The standard notation for the
   evaluation relation is a double down-arrow.  We'll typeset it like this
   in the HTML version of the notes and use a double slash as the closest
   approximation in [.v] files.) -/

scoped notation:55 e:56 " ==> " n:56 => AevalR e n
/- LATER: Comment from reader: How do I keep the ==> notation for aevalR
   from conflicting with the ==> notation for bevalR ?
   BCP/AAA 1/16: We should explain about notation scopes somewhere.
   NDS: notation scopes were already briefly touched upon in previous
   chapters. -/

/-
  ######################################################################
  ## Inference Rule Notation
-/

-- FULL
/-
  In informal discussions, it is convenient to write the rules for
  `AevalR` and similar relations in the more readable graphical form of
  _inference rules_, where the premises above the line justify the
  conclusion below the line.  For example, the constructor `E_APlus`

  ```
      | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) :
          AevalR a1 n1 →
          AevalR a2 n2 →
          AevalR (.plus a1 a2) (n1 + n2)
  ```

  can be written like this as an inference rule:

  ```
                            e1 ==> n1
                            e2 ==> n2
                      --------------------          (E_APlus)
                      plus e1 e2 ==> n1+n2
  ```

  Formally, there is nothing deep about inference rules: they are just
  implications.  You can read the rule name on the right as the name of the
  constructor and read each of the linebreaks between the premises above the
  line (as well as the line itself) as `→`.  All the variables mentioned in
  the rule (`e1`, `n1`, etc.) are implicitly bound by universal quantifiers
  at the beginning.  (Such variables are often called _metavariables_ to
  distinguish them from the variables of the language we are defining.  At
  the moment, our arithmetic expressions don't include variables, but we'll
  soon be adding them.)  The whole collection of rules is understood as being
  wrapped in an inductive declaration.  In informal prose, this is sometimes
  indicated by saying something like "Let `aevalR` be the smallest relation
  closed under the following rules...".

  To summarize: a group of inference rules corresponds to a single inductive
  definition; each rule's name corresponds to a constructor name; above the
  line are the premises, below the line the conclusion; and metavariables
  like `e1` and `n1` are implicitly universally quantified.  The whole
  collection of rules defines `==>` as the smallest relation closed under
  them:

  ```
                          -----------                (E_ANum)
                          num n ==> n

                            e1 ==> n1
                            e2 ==> n2
                      --------------------           (E_APlus)
                      plus e1 e2 ==> n1+n2

                            e1 ==> n1
                            e2 ==> n2
                     ---------------------           (E_AMinus)
                     minus e1 e2 ==> n1-n2

                            e1 ==> n1
                            e2 ==> n2
                      --------------------           (E_AMult)
                      mult e1 e2 ==> n1*n2
  ```
-/
-- /FULL

-- HIDE
/- INSTRUCTORS: It might be useful to write the inference rules on the
   chalkboard, walking through the translation from the inductive
   definition, and then use these quizzes to check comprehension.
   BCP 21: Too heavy. -/
/- LATER: The first two quizzes here seem kind of boring. -/
-- /HIDE

-- Claude: two comprehension quizzes follow; the first is shown, the second
-- is kept under `HIDE` (both were hidden in the source material).
-- QUIZ
/-
  Which rules are needed to prove the following?

  ```
  .mult (.plus (.num 3) (.num 1)) (.num 0) ==> 0
  ```

  (A) `E_ANum` and `E_APlus`
  (B) `E_ANum` only
  (C) `E_ANum` and `E_AMult`
  (D) `E_AMult` and `E_APlus`
  (E) `E_ANum`, `E_AMult`, and `E_APlus`
-/
-- /QUIZ

-- HIDE
-- QUIZ
/-
  Which rules are needed to prove the following?

  ```
  .minus (.num 3) (.minus (.num 2) (.num 1)) ==> 2
  ```

  (A) `E_ANum` and `E_APlus`
  (B) `E_ANum` only
  (C) `E_ANum` and `E_AMinus`
  (D) `E_AMinus` and `E_APlus`
  (E) `E_ANum`, `E_AMinus`, and `E_APlus`
-/
-- /QUIZ
-- /HIDE

-- FULL
-- EX1? (beval_rules)
/-
  Here, again, is the definition of the `Bexp.eval` function:

  ```
  def Bexp.eval (b : Bexp) : Bool :=
    match b with
    | bool b     => b
    | eq a1 a2  => a1.eval == a2.eval
    | neq a1 a2 => a1.eval != a2.eval
    | le a1 a2  => a1.eval ≤ a2.eval
    | gt a1 a2  => a1.eval > a2.eval
    | not b1    => !eval b1
    | and b1 b2 => eval b1 && eval b2
  ```

  Write out a corresponding definition of boolean evaluation as a relation
  (in inference rule notation).
-/
-- SOLUTION
/-
  Answer (`==>b` is defined below):

  ```
                          -------------              (E_bool)
                          bool b ==>b b

                            e1 ==> n1
                            e2 ==> n2
                     -------------------------        (E_BEq)
                     eq e1 e2 ==>b (n1 =? n2)

                            e1 ==> n1
                            e2 ==> n2
                   -------------------------------    (E_BNeq)
                   neq e1 e2 ==>b negb (n1 =? n2)

                            e1 ==> n1
                            e2 ==> n2
                     --------------------------       (E_BLe)
                     le e1 e2 ==>b (n1 <=? n2)

                            e1 ==> n1
                            e2 ==> n2
                  -------------------------------     (E_BGt)
                  gt e1 e2 ==>b negb (n1 <=? n2)

                             e ==>b b
                        ------------------            (E_BNot)
                        not e ==>b negb b

                            e1 ==>b b1
                            e2 ==>b b2
                    --------------------------        (E_BAnd)
                    and e1 e2 ==>b andb b1 b2
  ```
-/
-- /SOLUTION
-- GRADE_MANUAL 1: beval_rules
-- []
-- /FULL

/-
  ######################################################################
  ## Equivalence of the Definitions
-/

-- HIDEFROMADVANCED
/-
  It is straightforward to prove that the relational and functional
  definitions of evaluation agree.
-/
-- /HIDEFROMADVANCED

/- SOONER: BCP 23: Why can't we do induction on H in the ← direction?? -/

theorem aevalR_iff_aeval (a : Aexp) (n : Nat) :
    a ==> n ↔ Aexp.eval a = n := by
  constructor
  · intro h
    induction h with
    | E_ANum n => rfl
    | E_APlus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval]; rw [ih1, ih2]
    | E_AMinus a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval]; rw [ih1, ih2]
    | E_AMult a1 a2 n1 n2 h1 h2 ih1 ih2 => simp only [Aexp.eval]; rw [ih1, ih2]
  · intro h
    subst h
    induction a with
    | num n => exact .E_ANum n
    | plus a1 a2 ih1 ih2 => exact .E_APlus a1 a2 _ _ ih1 ih2
    | minus a1 a2 ih1 ih2 => exact .E_AMinus a1 a2 _ _ ih1 ih2
    | mult a1 a2 ih1 ih2 => exact .E_AMult a1 a2 _ _ ih1 ih2

-- HIDEFROMADVANCED
/-
  Again, we can make the proof quite a bit shorter using the combinators
  from the previous section.
-/
-- Claude: the `-- WORKINCLASS` marker leaves this shorter proof as a live
-- in-class exercise.

theorem aevalR_iff_aeval' (a : Aexp) (n : Nat) :
    a ==> n ↔ Aexp.eval a = n := by
  -- WORKINCLASS
  constructor
  · intro h; induction h <;> simp_all [Aexp.eval]
  · intro h; subst h; induction a <;> constructor <;> assumption
  -- /WORKINCLASS
-- /HIDEFROMADVANCED

-- EX3 (bevalR)
/-
  Write a relation `BevalR` in the same style as `AevalR`, and prove that
  it is equivalent to `Bexp.eval`.
-/

inductive BevalR : Bexp → Bool → Prop where
  -- SOLUTION
  | E_bool (b : Bool) : BevalR (.bool b) b
  | E_BEq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.eq a1 a2) (n1 == n2)
  | E_BNeq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.neq a1 a2) (n1 != n2)
  | E_BLe (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.le a1 a2) (n1 ≤ n2)
  | E_BGt (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ==> n1) (h2 : a2 ==> n2) :
      BevalR (.gt a1 a2) (n1 > n2)
  | E_BNot (b : Bexp) (bv : Bool) (h : BevalR b bv) :
      BevalR (.not b) (!bv)
  | E_BAnd (b1 b2 : Bexp) (tv1 tv2 : Bool) (h1 : BevalR b1 tv1) (h2 : BevalR b2 tv2) :
      BevalR (.and b1 b2) (tv1 && tv2)
  -- /SOLUTION

scoped notation:55 e:56 " ==>b " b:56 => BevalR e b

theorem bevalR_iff_beval (b : Bexp) (bv : Bool) :
    b ==>b bv ↔ Bexp.eval b = bv := by
  -- ADMITTED
  constructor
  · intro h
    induction h with
    | E_bool b => rfl
    | E_BEq a1 a2 n1 n2 h1 h2 =>
        simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BNeq a1 a2 n1 n2 h1 h2 =>
        simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BLe a1 a2 n1 n2 h1 h2 =>
        simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BGt a1 a2 n1 n2 h1 h2 =>
        simp only [Bexp.eval]; rw [(aevalR_iff_aeval a1 n1).mp h1, (aevalR_iff_aeval a2 n2).mp h2]
    | E_BNot b bv h ih => simp only [Bexp.eval]; rw [ih]
    | E_BAnd b1 b2 tv1 tv2 h1 h2 ih1 ih2 => simp only [Bexp.eval]; rw [ih1, ih2]
  · intro h
    subst h
    induction b with
    | bool b => exact .E_bool b
    | eq a1 a2  => exact .E_BEq a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | neq a1 a2 => exact .E_BNeq a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | le a1 a2  => exact .E_BLe a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | gt a1 a2  => exact .E_BGt a1 a2 _ _ ((aevalR_iff_aeval a1 _).mpr rfl) ((aevalR_iff_aeval a2 _).mpr rfl)
    | not b ih => exact .E_BNot b _ ih
    | and b1 b2 ih1 ih2 => exact .E_BAnd b1 b2 _ _ ih1 ih2
  -- /ADMITTED
-- GRADE_THEOREM 3: bevalR_iff_beval
-- []

/- LATER: Comment from reader: I am mainly following my nose and doing
   trial & error when I write these long `<;>`/`;`-chains. Are there some
   general patterns to follow? For example, what kinds of situations call
   for `try (a_1; a_2; ...; a_k)` and what kinds call for
   `try a_1; try a_2; ...; try a_l`? I know the difference between their
   effects but it is not immediately clear to me what this means for the
   practical uses. Also, are there recommended orders in which to chain
   `intro`s, `rewrite`s, `apply`s, `reflexivity`s and `simpl`s? Should
   `simpl`s be avoided for their slowness? When exactly is `simpl`
   necessary? Most importantly, why was my proof for `bevalR_iff_beval'` so
   much longer than yours for `aevalR_iff_aeval'`? -/

end AExp

/-
  ######################################################################
  ## Computational vs. Relational Definitions
-/

-- FULL
/-
  For the definitions of evaluation for arithmetic and boolean
  expressions, the choice of whether to use functional or relational
  definitions is mainly a matter of taste.  However, there are many
  situations where relational definitions work much better than
  functional ones.
-/
-- /FULL
-- TERSE: /- Sometimes relational definitions are the only reasonable option... -/

namespace AevalRDivision

/-
  For example, suppose that we wanted to extend the arithmetic operations
  with division:
-/

inductive Aexp where
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)
  | div (a1 a2 : Aexp)             -- NEW

/-
  Extending the definition of `Aexp.eval` to handle this new operation would
  not be straightforward (what should we return as the result of
  `.div (.num 5) (.num 0)`?).  But extending the relation is easy.
-/
-- TERSE: /- What should `Aexp.eval` return for `.div (.num 1) (.num 0)`?? -/

inductive AevalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) : AevalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.mult a1 a2) (n1 * n2)
  | E_ADiv (a1 a2 : Aexp) (n1 n2 n3 : Nat)             -- NEW
      (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) (hpos : n2 > 0) (hdiv : n2 * n3 = n1) :
      AevalR (.div a1 a2) n3

/-
  Notice that this evaluation relation corresponds to a _partial_
  function: there are some inputs for which it does not specify an output.
-/

end AevalRDivision

namespace AevalRExtended

-- TERSE: /- Another example: a _nondeterministic_ number generator: -/
/-
  Or suppose that we want to extend the arithmetic operations by a
  nondeterministic number generator `any` that, when evaluated, may
  yield any number.  (This is not the same as making a _probabilistic_
  choice among all numbers -- we only say which results are _possible_.)
-/

inductive Aexp where
  | any                            -- NEW
  | num (n : Nat)
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

/-
  Again, extending `Aexp.eval` would be tricky, since evaluation is now _not_
  a deterministic function from expressions to numbers; but extending the
  relation is no problem.
-/
-- TERSE: /- What should `Aexp.eval` do with nondeterminism?? -/

inductive AevalR : Aexp → Nat → Prop where
  | E_Any (n : Nat) : AevalR .any n                   -- NEW
  | E_ANum (n : Nat) : AevalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : AevalR a1 n1) (h2 : AevalR a2 n2) :
      AevalR (.mult a1 a2) (n1 * n2)

end AevalRExtended

-- FULL
/-
  At this point you may be wondering: which of these styles should I use
  by default?

  Where the thing being defined is not easy to express as a function --
  or is genuinely _not_ a function -- there is no real choice.  When both
  styles are workable, relational definitions can be more elegant and
  easier to understand, and Lean generates useful inversion and induction
  principles from them.  On the other hand, functional definitions are
  automatically deterministic and total (for a relation we must _prove_
  these if we need them), and we can use Lean's computation mechanism to
  simplify them during proofs.

  In large developments it is common to give a definition in _both_
  styles plus a lemma that the two coincide, allowing later proofs to
  switch between points of view at will -- exactly what we did above.
-/
-- /FULL
-- TERSE: /- Functional: computation.  Relational: expressive.  Best: both, proved equivalent. -/

/-
  ######################################################################
  # Expressions With Variables
-/

-- FULL
/-
  Let's return to defining Imp.  The next thing we need to do is to
  enrich our arithmetic and boolean expressions with variables.  To keep
  things simple, we'll assume that all variables are global and that they
  only hold numbers.
-/
-- /FULL

/-
  ######################################################################
  ## States
-/

/- LATER: Maybe this section needs a little preface talking about "what is
   the meaning of an expression with variables?"... -/
/- LATER: (Note copied from Equiv.v right before the assign_aequiv
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating states as
   an ADT should be raised there. -/

/-
  Since we'll want to look variables up to find out their current values,
  we'll use total maps from the `Maps` chapter.  A _machine state_ (or
  just _state_) represents the current values of all variables at some
  point in the execution of a program.
-/
-- FULL
/-
  For simplicity, we assume that the state is defined for _all_ variables,
  even though any given program is only able to mention a finite number of
  them.  Because each variable stores a natural number, we represent the
  state as a total map from strings (variable names) to `Nat`, and will use
  `0` as the default value in the store.
-/
-- /FULL

abbrev State := TotalMap String Nat

/- INSTRUCTORS: BAY, 23 Feb 2011: We tried making state more general,

      state X := id -> option X

   so it could be reused generically later.  However, this ends up
   complicating some of the proofs quite a bit, and not in an interesting
   way.  For example, the factorial invariant would need to be something
   like exists m n, st X = m /\ st Y = n /\ ... which is a pain to deal
   with. The present chapter jumps up the complexity coefficient quite a
   bit already, so we decided it's better to leave the simple version here,
   and go for more generality later on in the course.  BCP/AAA 12/2015:
   This comment led us to implement both total and partial maps in earlier
   chapters, so that we could re-use the total ones here. -/

/-
  ######################################################################
  ## Syntax
-/

/-
  We can add variables to the arithmetic expressions we had before simply
  by including one more constructor.  (This is a fresh `Aexp`, replacing
  the variable-free one from the `AExp` namespace above.)
-/

inductive Aexp where
  | num (n : Nat)
  | id (x : String)                -- NEW
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

/- The `Bexp` definition is unchanged, except that it now refers to the
   new `Aexp`. -/

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)

/- Defining a few variable names as shorthands will make examples easier
   to read. -/
/- INSTRUCTORS: We usually don't use x as a "bare identifier" in examples
   -- it is normally wrapped in an id constructor.  If this were _always_
   the case, then it would make more sense to define the notation [x] to
   mean [id (Id 0)].  But there quite a few counterexamples.  Maybe we
   could define [xx] to mean [id (Id 0)], or some such?  But it's still
   awkward.
   BCP/AAA 2/16: Should we use a coercion for this?  It means introducing a
   new concept -- a somewhat magical one -- but it will make examples look
   quite a bit nicer...
   BCP 11/16: It will also solve some problems later on with confusions
   about bound identifiers in Stlc vs. "global" ones in Imp. I think it's a
   good idea to try it for the next big revision.
   ET 10/17: coercions and notations are done, see below.  (still keeping
   the global variables W, X, Y, Z for readability)
   BCP 7/20: This still needs another look to see if there's a way to make
   it globally better. -/

def W : String := "W"
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

-- FULL
/-
  (This convention for naming program variables (`X`, `Y`, `Z`) clashes a
  bit with our earlier use of uppercase letters for types.  Since we're not
  using polymorphism heavily in the chapters developed to Imp, this
  overloading should not cause confusion.)
-/
-- /FULL

/-
  ######################################################################
  ## Notations
-/

-- Claude (port note): The Rocq chapter builds a custom `<{ ... }>` grammar
-- so that Imp programs can be written with concrete `+`, `:=`, `;`,
-- `if`/`while` syntax.  We take the lighter route used elsewhere in this
-- translation: three coercions let us drop the `id`/`num`/`bool` wrappers,
-- and we otherwise write programs with the ordinary constructors.

-- FULL
/-
  To make Imp programs easier to read and write, we introduce a few implicit
  coercions.  In Lean, a `Coe` instance tells the elaborator how to turn a
  value of one type into another automatically:
   - `Coe String Aexp` lets us write a bare variable (a `String`) where an
     `Aexp` is expected; the string is implicitly wrapped with `id`.
   - `OfNat Aexp n` lets us write a numeric literal where an `Aexp` is
     expected; it is implicitly wrapped with `num`.
   - `Coe Bool Bexp` lets us write a boolean literal (`true`/`false`) where a
     `Bexp` is expected; it is implicitly wrapped with `bool`.
-/
-- /FULL

instance : Coe String Aexp where
  coe := .id

instance (n : Nat) : OfNat Aexp n where
  ofNat := .num n

instance : Coe Bool Bexp where
  coe := .bool

/- With these, we can write `.plus 3 (.mult X 2)` instead of
   `.plus (.num 3) (.mult (.id "X") (.num 2))`, and `.and true (.not …)`
   instead of `.and (.bool true) (.not …)`. -/

def example_aexp : Aexp := .plus 3 (.mult X 2)
def example_bexp : Bexp := .and true (.not (.le X 4))

/- Claude: This chapter uses the two coercions above rather than an embedded
   Imp grammar.  For a future pass, here is the fuller notation machinery a
   `<{ … }>`-style concrete syntax would involve, with the dev notes that
   went with it.  (LATER: Maybe these notations/coercions should be
   introduced earlier in the chapter?)

   To make Imp programs easier to read and write one can introduce notations
   and implicit coercions.  (The details are a bit hideous, but not important
   to understand.)  Briefly:
    - A `Coercion` declaration lets a function/constructor be used implicitly
      to coerce a value of the input type to the output type; e.g. a coercion
      for `id` lets plain strings stand where an `aexp` is expected.
    - `Declare Custom Entry com` creates a custom grammar for parsing Imp;
      anything between `<{` and `}>` is parsed with it, giving _new_
      interpretations to familiar operators (`+`, `-`, `*`, `=`, `<=`, …).

   ```
   Coercion AId : string >-> aexp.
   Coercion ANum : nat >-> aexp.

   Declare Custom Entry com.
   Declare Scope com_scope.

   Notation "<{ e }>" := e
     (e custom com, format "'[hv' <{ '/  ' '[v' e ']' '/' }> ']'") : com_scope.
   Notation "( x )" := x (in custom com, x at level 99).
   Notation "x" := x (in custom com at level 0, x constr at level 0).
   Notation "f x .. y" := (.. (f x) .. y)
                     (in custom com at level 0, only parsing,
                     f constr at level 0, x constr at level 1,
                         y constr at level 1).
   Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
   Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
   Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
   Notation "'true'"  := true (at level 1).
   Notation "'true'"  := BTrue (in custom com at level 0).
   Notation "'false'" := false (at level 1).
   Notation "'false'" := BFalse (in custom com at level 0).
   Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
   Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
   Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
   Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
   Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
   Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

   Open Scope com_scope.
   ```

   NOTATION dev notes:
    - LATER: We could perhaps avoid this (somewhat confusing) coercion by
      just defining all the single uppercase letters to be identifiers,
      rather than using strings. But we can't make a similar change in the
      lambda-expression syntax, where many more variable names are needed, so
      not clear it's a good idea here.
      NDS'25: the string/int literal mechanism is not really meant for custom
      scopes (rocq-prover/rocq#9516, #9518).  We attempted to hack around
      this but you'd end up with `<{ 5%com + "X"%com }>`, which is not a clear
      win.  We also briefly attempted the hack in rocq-prover/rocq#15643;
      this worked for the syntax but caused issues with pattern-matching.
    - INSTRUCTORS: Some notations are declared under a scope despite being
      also in a custom entry, to allow us to change some of them later, e.g.
      in Hoare2.v.  NDS'25: Maybe migrate to a model without scopes (other
      than for entrypoints) but with multiple custom entries?
    - INSTRUCTORS: If anything changes here, make the same adjustment in all
      the other grammars for Imp-like languages.  (There are notes at the
      bottom of the source file about the technical choices; search for
      REASONS.)
    - SAZ 2024: rationale for putting embedded-function arguments at level 9
      of the constr grammar: in the general `term` grammar, applications are
      parsed at level 10 as `SELF ; list1 arg` where `arg` invokes `term` at
      level 9; but we want special precedence for some arguments in Hoare.v,
      so we ask these to parse at level 1 of `constr`, enabling looser
      precedence for the assertions in Hoare.v.
    - NDS'25: I'd recommend making `Open Scope com_scope` `Local` and opening
      the scope in every file which wants the notation, as that seems better
      practice.

   And a grammar sanity-check (this was hidden):

   ```
   Locate "=".
   Check <{ X + Y }>.
   Check <{ X + Y = 0 }>.
   Check <{ ~ (Y = X) }>.
   Check <{ X + Y }>.
   Check <{ ~ (X + Y = Y) && Z = W }>.
   ``` -/

/-
  ######################################################################
  ## Evaluation
-/

-- FULL
/-
  The arithmetic and boolean evaluators must now be extended to handle
  variables, taking a state `st` as an extra argument.  A variable is
  looked up in the state with the map-indexing notation `st[x]` from the
  `Maps` chapter.
-/
-- /FULL
-- TERSE: /- Now we need to add an `st` parameter to both evaluation functions: -/

def Aexp.eval (st : State) (a : Aexp) : Nat :=
  match a with
  | num n => n
  | id x => st[x]                  -- NEW
  | plus  a1 a2 => eval st a1 + eval st a2
  | minus a1 a2 => eval st a1 - eval st a2
  | mult  a1 a2 => eval st a1 * eval st a2

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b     => b
  | eq a1 a2  => Aexp.eval st a1 == Aexp.eval st a2
  | neq a1 a2 => Aexp.eval st a1 != Aexp.eval st a2
  | le a1 a2  => Aexp.eval st a1 ≤ Aexp.eval st a2
  | gt a1 a2  => Aexp.eval st a1 > Aexp.eval st a2
  | not b1    => !eval st b1
  | and b1 b2 => eval st b1 && eval st b2

/- We write the empty state (every variable `0`) as `∅`, and reuse the
   total-map update notation `x →ₜ v ; st` for states. -/
-- Claude: we write single-variable states inline as `X →ₜ 5 ; empty_st`
-- rather than introducing a dedicated "singleton state" shorthand.

def empty_st : State := ∅

/- test_aexp1 -/
example : Aexp.eval (X →ₜ 5 ; empty_st) (.plus 3 (.mult X 2)) = 13 := by rfl

/- test_aexp2 -/
example : Aexp.eval (X →ₜ 5 ; Y →ₜ 4 ; empty_st) (.plus Z (.mult X Y)) = 20 := by rfl

/- test_bexp1 -/
example : Bexp.eval (X →ₜ 5 ; empty_st) (.and true (.not (.le X 4))) = true := by rfl

/-
  ######################################################################
  # Commands
-/

-- FULL
/-
  Now we are ready to define the syntax and behavior of Imp _commands_
  (or _statements_).  Informally, commands `c` are described by the
  following BNF grammar:

  ```
  c := skip
     | x := a
     | c ; c
     | if b then c else c end
     | while b do c end
  ```

  Here is the formal definition of the abstract syntax of commands.
-/
-- /FULL

inductive Com where
  | skip
  | asgn (x : String) (a : Aexp)
  | seq (c1 c2 : Com)
  | cond (b : Bexp) (c1 c2 : Com)
  | whileDo (b : Bexp) (c : Com)

/- Claude: This chapter writes commands with the ordinary constructors (see
   the port note above) rather than an embedded grammar.  For a future pass,
   here are the concrete-syntax `Notation` declarations and their dev notes:

  ```
  Notation "'skip'"  := CSkip
    (in custom com at level 0) : com_scope.
  Notation "x := y"  := (CAsgn x y)
    (in custom com at level 0, x constr at level 0, y at level 85,
      no associativity, format "x  :=  y") : com_scope.
  Notation "x ; y" := (CSeq x y)
    (in custom com at level 90, right associativity,
      format "'[v' x ; '/' y ']'") : com_scope.
  Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
    (in custom com at level 89, x at level 99, y at level 99, z at level 99,
      format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
  Notation "'while' x 'do' y 'end'" := (CWhile x y)
    (in custom com at level 89, x at level 99, y at level 99,
      format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.
  ```

  NOTATION dev notes carried over:
   - NDS'25 changed the syntax to include new lines.  Whether the boxes
     (`'[..`) should be regular, vertical (`v`) or horizontal-or-else-vertical
     (`hv`) is up for debate.  I went with "force newlines" (vertical boxes)
     because this should lead to fewer (bad) surprises.  The crux of my pain
     is that Rocq has a very local definition of "fits on one line": if a
     subbox spans multiple lines but the current notation does not require
     line breaks other than the ones in the sub-notation, then it "fits on
     one line".
   - SOONER (NOTATION NDS'25): I considered changing maps to also span
     multiple lines, but have not attempted this yet, as it would require
     changes in earlier chapters.
   - NDS'25: We may want to experiment with forcing a newline after
     `<{ ... }>`.  We currently get a "snake-like" display in some cases
     (see Smallstep:mult_while_h), e.g. a long disjunction of `while`/`if`
     programs that wraps awkwardly.  As much as this is an improvement over
     no line-breaks, it is far from optimal...

  Grammar sanity-check (this was hidden):

  ```
  Check <{ skip }>.
  Check <{ skip; skip; skip; skip; skip; skip; skip }>.
  Check <{ (skip ; skip) ; skip }>.
  Check <{ 1 + 2 }>.
  Check <{ 2 = 1 }>.
  Check <{ Z := X }>.
  Check <{ Z := X + 3 }>.
  Definition func (c : com) : com := <{ c ; skip }>.
  Check <{ skip; func <{ skip }> }>.
  Definition func2 (c1 c2 : com) : com := <{ c1 ; c2 }>.
  Check <{ skip ; func2 <{skip}> <{skip}> }>.
  Check <{ true && ~(false && true) }>.
  Check <{ if true then skip else skip end }>.
  Check <{ if true && true then skip; skip else skip; X:=X+1 end }>.
  Check <{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }>.
  ``` -/

-- FULL
/-
  For example, here is the factorial function again, written as a formal
  definition.  When this command terminates, the variable `Y` will
  contain the factorial of the initial value of `X`.  (Compare this to
  the concrete Imp program at the very start of the chapter.)
-/
-- /FULL

def fact_in_lean : Com :=
  .seq (.asgn Z X)
  (.seq (.asgn Y 1)
  (.whileDo (.neq Z 0)
    (.seq (.asgn Y (.mult Y Z))
           (.asgn Z (.minus Z 1)))))

/- Claude: The following two topics are entirely about Rocq's `<{ }>` grammar
   and `Set Printing …`/`Locate` commands, which this port does not use.  A
   future pass could decide whether a Lean analogue (e.g. `set_option pp.*`)
   is worth adding.

  Desugaring notations. (LATER: MRC'20: somewhat redundant with the `Set
  Printing Coercions` discussion above.)  Rocq offers coercions and notations
  to manage complexity; heavy usage can obscure what the expressions we enter
  actually mean, so it is often instructive to "turn off" those features
  (also usable mid-proof):

    - `Unset Printing Notations` (undo with `Set Printing Notations`)
    - `Set Printing Coercions` (undo with `Unset Printing Coercions`)
    - `Set Printing All` (undo with `Unset Printing All`)

  ```
  Unset Printing Notations.
  Print fact_in_coq.
  (* ===>
     fact_in_coq =
     CSeq (CAsgn Z X)
          (CSeq (CAsgn Y (S O))
                (CWhile (BNot (BEq Z O))
                        (CSeq (CAsgn Y (AMult Y Z))
                              (CAsgn Z (AMinus Z (S O))))))
          : com *)
  Set Printing Notations.

  Print example_bexp.
  (* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

  Set Printing Coercions.
  (* LATER: Ori: CoqIde error msg: "Set this option from the IDE menu
     instead". I guess this is a recent change? *)
  Print example_bexp.
  (* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

  Print fact_in_coq.
  (* ===>
    fact_in_coq =
    <{ Z := (AId X);
       Y := (ANum 1);
       while ~ (AId Z) = (ANum 0) do
         Y := (AId Y) * (AId Z);
         Z := (AId Z) - (ANum 1)
       end }>
         : com *)
  Unset Printing Coercions.
  ```

  Locate again. (HIDE: MRC'20: somewhat redundant with a similar discussion
  in Maps.  BCP 21: left both, with pointers in each so it doesn't look like a
  mistake.)

  Finding identifiers.  When used with an identifier, `Locate` prints the
  full path to every value in scope with the same name -- useful to
  troubleshoot variable shadowing.

  ```
  Locate aexp.
  (* ===>
       Inductive LF.Imp.aexp
       Inductive LF.Imp.AExp.aexp  (shorter: AExp.aexp)
       Inductive LF.Imp.aevalR_division.aexp  (shorter: aevalR_division.aexp)
       Inductive LF.Imp.aevalR_extended.aexp  (shorter: aevalR_extended.aexp) *)
  ```

  Finding notations.  When faced with an unknown notation, use `Locate`
  with a string containing one of its symbols to see its interpretations.

  ```
  Locate "&&".
  (* ===>
      "x && y" := and x y (default interpretation)
      "x && y" := andb x y : bool_scope (default interpretation) *)
  Locate ";".
  (* ===>
      "x '|->' v ';' m" := (update m x v) (default interpretation)
      "x ; y" := (seq x y) (default interpretation)
      "x '!->' v ';' m" := (t_update m x v) (default interpretation)
      "[ x ; y ; .. ; z ]" := cons x (cons y .. (cons z nil) ..) : list_scope *)
  Locate "while".
  (* ===>
      "'while' x 'do' y 'end'" := (whileDo x y) (default interpretation) *)
  ``` -/

/- HIDE: the factorial command was printed here with `Print fact_in_coq.` -/

-- HIDEFROMADVANCED
/- A few more examples. -/

/- *** Assignment: -/
def plus2 : Com := .asgn X (.plus X 2)
def XtimesYinZ : Com := .asgn Z (.mult X Y)

/- *** Loops: -/
def subtract_slowly_body : Com :=
  .seq (.asgn Z (.minus Z 1))
        (.asgn X (.minus X 1))

def subtract_slowly : Com :=
  .whileDo (.neq X 0) subtract_slowly_body

def subtract_3_from_5_slowly : Com :=
  .seq (.asgn X 3)
  (.seq (.asgn Z 5)
    subtract_slowly)

/- *** An infinite loop: -/
def loop : Com := .whileDo true .skip

-- HIDE
/- Exponentiation: -/
def exp_body : Com :=
  .seq (.asgn Z (.mult Z X))
        (.asgn Y (.minus Y 1))
def pexp : Com := .whileDo (.neq Y 0) exp_body
/- (Note that `pexp` should be run in a state where `Z` is `1`.) -/
-- /HIDE
-- /HIDEFROMADVANCED

/-
  ######################################################################
  # Evaluating Commands
-/

-- FULL
/-
  Next we need to define what it means to evaluate an Imp command.  The
  fact that `while` loops don't necessarily terminate makes defining an
  evaluation function tricky.
-/
-- /FULL

/-
  ######################################################################
  ## Evaluation as a Function (Failed Attempt)
-/

/-
  Here's an attempt at defining an evaluation function for commands (with
  a bogus `while` case).
-/

/- LATER: In SmallStep we need to package the state and command into a pair,
   so that we can talk about normal forms and such.  Probably we should do it
   here too, for consistency.  (Won't change much except the type
   declarations, but we'll need to add a comment why we wrote them this
   way.) -/

def Com.ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | skip => st
  | asgn x a => (x →ₜ Aexp.eval st a ; st)
  | seq c1 c2 =>
      let st' := ceval_fun_no_while st c1
      ceval_fun_no_while st' c2
  | cond b c1 c2 =>
      if Bexp.eval st b then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | whileDo _ _ => st               -- bogus

-- FULL
/-
  In a more conventional functional language like OCaml or Haskell we
  could add the `while` case as follows:

  ```
  | .whileDo b c =>
      if Bexp.eval st b then ceval_fun st (.seq c (.whileDo b c))
      else st
  ```

  Lean doesn't accept such a definition ("fail to show termination")
  because the function we want to define is not guaranteed to terminate.
  Indeed, it _doesn't_ always terminate: the full `ceval_fun` applied to
  the `loop` program above would run forever.  Since Lean aims to be not
  just a programming language but also a consistent logic, any
  potentially non-terminating function must be rejected.  Here is what
  would go wrong if Lean allowed non-terminating recursive functions:

  ```
  def loop_false (n : Nat) : False := loop_false n
  ```

  That is, propositions like `False` would become provable (`loop_false 0`
  would be a proof of `False`), a disaster for logical consistency.

  Thus, because it doesn't terminate on all inputs, the full `ceval_fun`
  cannot be written in Lean -- at least not without additional tricks and
  workarounds.
-/
-- /FULL
/- HIDE: Perhaps that discussion should be moved to -- or previewed in --
   Logic.v?  MRC'20: It's already in ProofObjects (which not everyone
   sees). -/
-- TERSE: /- A nonterminating `def loop_false (n) : False := loop_false n` would make `False` provable, so Lean rejects it. -/

/-
  ######################################################################
  ## Evaluation as a Relation
-/

/-
  Here's a better way: define `ceval` as a _relation_ rather than a
  _function_ -- i.e., make its result a `Prop` rather than a `State`,
  similar to what we did for `AevalR` above.
-/

-- FULL
-- HIDEFROMADVANCED
/-
  This is an important change.  Besides freeing us from awkward workarounds,
  it gives us a ton more flexibility in the definition.  For example, if we
  add nondeterministic features like `any` to the language, we want the
  definition of evaluation to be nondeterministic -- i.e., not only will it
  not be total, it will not even be a function!
-/
-- /HIDEFROMADVANCED
-- /FULL

/-
  We'll use the notation `st =[ c ]=> st'` for the `ceval` relation:
  `st =[ c ]=> st'` means that executing program `c` in a starting state
  `st` results in an ending state `st'`.  This can be pronounced "`c` takes
  state `st` to `st'`".
-/

/- *** Operational Semantics -/

/- SOONER: BCP 21: I wonder if E_Seq would be easier to work with if st' and
   st'' were swapped... -/

/-
  Here is an informal definition of evaluation, presented as inference rules
  for readability:

  ```
                        -----------------                  (E_Skip)
                        st =[ skip ]=> st

                        Aexp.eval st a = n
                --------------------------------           (E_Asgn)
                st =[ x := a ]=> (x →ₜ n ; st)

                        st  =[ c1 ]=> st'
                        st' =[ c2 ]=> st''
                      ---------------------                (E_Seq)
                      st =[ c1;c2 ]=> st''

                       Bexp.eval st b = true
                        st =[ c1 ]=> st'
             --------------------------------------        (E_IfTrue)
             st =[ if b then c1 else c2 end ]=> st'

                      Bexp.eval st b = false
                        st =[ c2 ]=> st'
             --------------------------------------        (E_IfFalse)
             st =[ if b then c1 else c2 end ]=> st'

                      Bexp.eval st b = false
                 -----------------------------             (E_WhileFalse)
                 st =[ while b do c end ]=> st

                       Bexp.eval st b = true
                        st =[ c ]=> st'
               st' =[ while b do c end ]=> st''
               --------------------------------            (E_WhileTrue)
               st  =[ while b do c end ]=> st''
  ```

  Here is the formal definition.  Make sure you understand how it
  corresponds to the inference rules.
-/
-- /FULL

/- HIDE: APT: Investigate rewriting these to use equality hypotheses rather
   than repeated variables in the conclusion.  For example:

   ```
   E_Skip : forall st st', st = st' -> st =[ skip ]=> st'.
   ```

   This makes the constructors easier to apply, and allows us to "swap in" an
   equivalence in place of equality.
   BAY: It sounds nice, but I tried this (23 Feb 2011) and didn't really find
   any benefit. The only difference seemed to be that it made quite a few
   proofs a tiny bit more annoying, due to the need for an extra
   'reflexivity' or 'subst' or what have you. -/

inductive Ceval : Com → State → State → Prop where
  | E_Skip (st : State) :
      Ceval .skip st st
  | E_Asgn (st : State) (a : Aexp) (n : Nat) (x : String)
      (h : Aexp.eval st a = n) :
      Ceval (.asgn x a) st (x →ₜ n ; st)
  | E_Seq (c1 c2 : Com) (st st' st'' : State)
      (h1 : Ceval c1 st st') (h2 : Ceval c2 st' st'') :
      Ceval (.seq c1 c2) st st''
  | E_IfTrue (st st' : State) (b : Bexp) (c1 c2 : Com)
      (hb : Bexp.eval st b = true) (hc : Ceval c1 st st') :
      Ceval (.cond b c1 c2) st st'
  | E_IfFalse (st st' : State) (b : Bexp) (c1 c2 : Com)
      (hb : Bexp.eval st b = false) (hc : Ceval c2 st st') :
      Ceval (.cond b c1 c2) st st'
  | E_WhileFalse (b : Bexp) (st : State) (c : Com)
      (hb : Bexp.eval st b = false) :
      Ceval (.whileDo b c) st st
  | E_WhileTrue (st st' st'' : State) (b : Bexp) (c : Com)
      (hb : Bexp.eval st b = true) (hc : Ceval c st st')
      (hloop : Ceval (.whileDo b c) st' st'') :
      Ceval (.whileDo b c) st st''

/- NOTATION: LATER: Consider `st '={' c '}=>' st'` or `st '=<{' c '}>=>' st'`. -/
/- NOTATION: NDS'25 should we change the level to force parentheses around
   `when` on the left-hand side of an arrow? -/
notation:40 st0 " =[ " c " ]=> " st1 => Ceval c st0 st1

/-
  The cost of defining evaluation as a relation instead of a function is
  that we now need to construct a _proof_ that some program evaluates to
  some result state, rather than letting Lean's computation mechanism do
  it for us.
-/

example :
    empty_st =[ .seq (.asgn X 2)
                  (.cond (.le X 1) (.asgn Y 3) (.asgn Z 4)) ]=>
      (Z →ₜ 4 ; X →ₜ 2 ; empty_st) := by
  -- We must supply the intermediate state.
  apply Ceval.E_Seq (st' := (X →ₜ 2 ; empty_st))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_IfFalse
    · rfl
    · apply Ceval.E_Asgn; rfl

-- EX2 (ceval_example2)
example :
    empty_st =[ .seq (.asgn X 0) (.seq (.asgn Y 1) (.asgn Z 2)) ]=>
      (Z →ₜ 2 ; Y →ₜ 1 ; X →ₜ 0 ; empty_st) := by
  -- ADMITTED
  apply Ceval.E_Seq (st' := (X →ₜ 0 ; empty_st))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_Seq (st' := (Y →ₜ 1 ; X →ₜ 0 ; empty_st))
    · apply Ceval.E_Asgn; rfl
    · apply Ceval.E_Asgn; rfl
  -- /ADMITTED
-- []

/- HIDE: the implicit arguments of the previous example were inspected here
   with `Set Printing Implicit. Check @ceval_example2.` (Rocq-specific). -/

-- TERSE: /- What sorts of things might we want to prove using these definitions?  Here are some simple examples... -/

/- HIDE: PR: I phrased these quizzes with the following alternatives:
   (A) Not true
   (B) True and easily provable
   (C) True and takes more work to prove
   (D) True and cannot be proved without additional axioms -/

-- QUIZ
/-
  Is the following proposition provable?

  ```
  ∀ (c : Com) (st st' : State),
    st =[ .seq .skip c ]=> st' →
    st =[ c ]=> st'
  ```

  (A) Yes    (B) No    (C) Not sure
-/
-- HIDE
theorem quiz1_answer (c : Com) (st st' : State)
    (h : st =[ .seq .skip c ]=> st') : st =[ c ]=> st' := by
  cases h with
  | E_Seq _ _ _ smid _ h1 h2 =>
      cases h1 with
      | E_Skip _ => exact h2
-- /HIDE
-- /QUIZ

-- QUIZ
/-
  Is the following proposition provable?

  ```
  ∀ (c1 c2 : Com) (st st' : State),
    st =[ .seq c1 c2 ]=> st' →
    st =[ c1 ]=> st →
    st =[ c2 ]=> st'
  ```

  (A) Yes    (B) No    (C) Not sure
-/
-- INSTRUCTORS: Answer is given later (`quiz2_answer`) as it depends on
-- `ceval_deterministic`.
-- /QUIZ

-- QUIZ
/-
  Is the following proposition provable?

  ```
  ∀ (b : Bexp) (c : Com) (st st' : State),
    st =[ .cond b c c ]=> st' →
    st =[ c ]=> st'
  ```

  (A) Yes    (B) No    (C) Not sure
-/
-- INSTRUCTORS
theorem quiz3_answer (b : Bexp) (c : Com) (st st' : State)
    (h : st =[ .cond b c c ]=> st') : st =[ c ]=> st' := by
  cases h with
  | E_IfTrue _ _ _ _ _ hb hc => exact hc
  | E_IfFalse _ _ _ _ _ hb hc => exact hc
-- /INSTRUCTORS
-- /QUIZ

-- QUIZ
/-
  Is the following proposition provable?

  ```
  ∀ (b : Bexp),
    (∀ st, Bexp.eval st b = true) →
    ∀ (c : Com) (st : State),
      ¬ ∃ st', st =[ .whileDo b c ]=> st'
  ```

  (A) Yes    (B) No    (C) Not sure
-/
-- HIDE
-- This one is tricky!
theorem quiz4_answer (b : Bexp) (hbtrue : ∀ st, Bexp.eval st b = true)
    (c : Com) (st : State) : ¬ ∃ st', st =[ .whileDo b c ]=> st' := by
  rintro ⟨st', hev⟩
  have key : ∀ (cmd : Com) (s s' : State),
      (s =[ cmd ]=> s') → cmd = .whileDo b c → False := by
    intro cmd s s' hce
    induction hce with
    | E_WhileFalse b0 s0 c0 hbf =>
        intro heq; injection heq with e1 _; subst e1
        rw [hbtrue s0] at hbf; simp at hbf
    | E_WhileTrue s0 s0' s0'' b0 c0 hbt hc0 hloop ih1 ih2 =>
        intro heq; exact ih2 heq
    | E_Skip s0 => intro heq; simp at heq
    | E_Asgn s0 a n x h => intro heq; simp at heq
    | E_Seq d1 d2 s0 s0' s0'' hh1 hh2 ih1 ih2 => intro heq; simp at heq
    | E_IfTrue s0 s0' b0 d1 d2 hb0 hc0 ih => intro heq; simp at heq
    | E_IfFalse s0 s0' b0 d1 d2 hb0 hc0 ih => intro heq; simp at heq
  exact key _ st st' hev rfl
-- /HIDE
-- /QUIZ

-- QUIZ
/-
  Is the following proposition provable?

  ```
  ∀ (b : Bexp) (c : Com) (st : State),
    (¬ ∃ st', st =[ .whileDo b c ]=> st') →
    ∀ st'', Bexp.eval st'' b = true
  ```

  (A) Yes    (B) No    (C) Not sure
-/
/- HIDE: This claim is *false*, so it cannot be proved -- the proof gets
   stuck immediately:

   ```
   Lemma quiz5_answer: forall (b : bexp) (c : com) (st : state),
     ~(exists st', st =[ while b do c end ]=> st') ->
     forall st'', beval st'' b = true.
   Proof.
     intros b c st H st''.
   Abort. (* Can't make any progress - claim is false! *)
   ``` -/
-- /QUIZ

/-
  ######################################################################
  ## Determinism of Evaluation
-/

/- LATER: Maybe this should go at the end of the file in a section marked
   optional?  Not everybody will want to spend time on it. -/

-- FULL
/-
  Changing from a computational to a relational definition of evaluation
  is a good move because it frees us from the artificial requirement that
  evaluation be a total function.  But it raises a question: is the
  relational definition really a partial _function_?  Could the same
  command, from the same state, evaluate to two different final states?
  In fact this cannot happen: `ceval` _is_ a partial function.
-/
-- /FULL
-- TERSE: /- Finally, we should pause to check that our evaluation relation really is a (partial) function... -/

/- LATER: Informal proof needed!  (And one can surely be found in some past
   CIS500 exam solutions!) -/

theorem ceval_deterministic (c : Com) (st st1 st2 : State)
    (e1 : st =[ c ]=> st1) (e2 : st =[ c ]=> st2) : st1 = st2 := by
  induction e1 generalizing st2 with
  | E_Skip st =>
      cases e2 with
      | E_Skip => rfl
  | E_Asgn st a n x h =>
      cases e2 with
      | E_Asgn _ _ n' _ h' => subst h; subst h'; rfl
  | E_Seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
      cases e2 with
      | E_Seq _ _ _ st2' _ h1' h2' =>
          have hst : st' = st2' := ih1 _ h1'
          subst hst
          exact ih2 _ h2'
  | E_IfTrue st st' b c1 c2 hb hc ih =>
      cases e2 with
      | E_IfTrue _ _ _ _ _ hb' hc' => exact ih _ hc'
      | E_IfFalse _ _ _ _ _ hb' hc' => simp_all
  | E_IfFalse st st' b c1 c2 hb hc ih =>
      cases e2 with
      | E_IfTrue _ _ _ _ _ hb' hc' => simp_all
      | E_IfFalse _ _ _ _ _ hb' hc' => exact ih _ hc'
  | E_WhileFalse b st c hb =>
      cases e2 with
      | E_WhileFalse _ _ _ hb' => rfl
      | E_WhileTrue _ _ _ _ _ hb' hc' hl' => simp_all
  | E_WhileTrue st st' st'' b c hb hc hloop ih1 ih2 =>
      cases e2 with
      | E_WhileFalse _ _ _ hb' => simp_all
      | E_WhileTrue _ st2' _ _ _ hb' hc' hl' =>
          have hst : st' = st2' := ih1 _ hc'
          subst hst
          exact ih2 _ hl'

-- HIDE
/- Answer to the second quiz above (deferred because it depends on
   `ceval_deterministic`). -/
theorem quiz2_answer (c1 c2 : Com) (st st' : State)
    (h1 : st =[ .seq c1 c2 ]=> st') (h2 : st =[ c1 ]=> st) : st =[ c2 ]=> st' := by
  cases h1 with
  | E_Seq _ _ _ smid _ hc1 hc2 =>
      have hmid : smid = st := ceval_deterministic c1 st smid st hc1 h2
      subst hmid
      exact hc2
-- /HIDE

-- EX3 (pup_to_n)
-- (Rocq marked this exercise optional -- `EX3?`.)
/-
  Write an Imp program that sums the numbers from `1` to `X` (inclusive)
  in the variable `Y`.  Your program should update the state as shown in
  `pup_to_2_ceval`, which you can reverse-engineer to discover the program
  you should write.  The proof of that theorem will be somewhat lengthy.
-/
/- HIDE: CH: This is hard to solve without eapply.  Decreased number of
   iterations to 2.  Made the whole thing optional. -/

def pup_to_n : Com :=
  -- ADMITDEF
  .seq (.asgn Y 0)
    (.whileDo (.le 1 X)
      (.seq (.asgn Y (.plus Y X))
             (.asgn X (.minus X 1))))
  -- /ADMITDEF

/- HIDE: Result is the same as `(X →ₜ 0 ; Y →ₜ 3 ; ∅)` if one admits
   functional extensionality. -/
theorem pup_to_2_ceval :
    (X →ₜ 2 ; empty_st) =[ pup_to_n ]=>
      (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st) := by
  -- ADMITTED
  unfold pup_to_n
  apply Ceval.E_Seq (st' := (Y →ₜ 0 ; X →ₜ 2 ; empty_st))
  · apply Ceval.E_Asgn; rfl
  · apply Ceval.E_WhileTrue (st' := (X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st))
    · rfl
    · apply Ceval.E_Seq (st' := (Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st)) <;>
        (apply Ceval.E_Asgn; rfl)
    · apply Ceval.E_WhileTrue
        (st' := (X →ₜ 0 ; Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st))
      · rfl
      · apply Ceval.E_Seq (st' := (Y →ₜ 3 ; X →ₜ 1 ; Y →ₜ 2 ; Y →ₜ 0 ; X →ₜ 2 ; empty_st)) <;>
          (apply Ceval.E_Asgn; rfl)
      · apply Ceval.E_WhileFalse; rfl
  -- /ADMITTED
-- []

/- LATER: Comment from reader: Another good place to mention lack of
   functional extensionality.  The 6 `→ₜ`/`t_update`s in the above theorem
   are not redundant, nor would `pup_to_2_ceval` be provable if the
   algorithm were defined differently (e.g., if it used `Z` as a "buffer"
   variable instead of decrementing `X`). -/

/-
  ######################################################################
  # Reasoning About Imp Programs
-/

/- LATER: This section doesn't seem very useful -- to anybody!  It takes too
   much time to go through it in class, and even for advanced students it's
   too low-level and grubby to be a very convincing motivation for what
   follows -- i.e., to feel motivated by its grubbiness, you have to
   understand it, but this takes more time than it's worth.  Better to cut
   the whole rest of the file (except the further exercises at the very end),
   or at least make it optional.
   (BCP 10/18: However, this removes quite a few exercises. Is the homework
   assignment still meaty enough?  I'm going to leave it as-is for now, but
   we should reconsider this later.) -/

-- FULL
/-
  We'll get into more systematic and powerful techniques for reasoning
  about Imp programs in _Programming Language Foundations_, but we can
  already do a few things (albeit in a somewhat low-level way) just by
  working with the bare definitions.  This section explores some examples.
-/
-- /FULL

theorem plus2_spec (st : State) (n : Nat) (st' : State)
    (hx : st[X] = n) (heval : st =[ plus2 ]=> st') :
    st'[X] = n + 2 := by
  -- Inverting `heval` forces one step of the `ceval` computation: since
  -- `plus2` is an assignment, `st'` must be `st` extended at `X`.
  unfold plus2 at heval
  cases heval with
  | E_Asgn _ _ m _ h =>
      simp only [Aexp.eval] at h
      rw [TotalMap.update_eq]
      lia

/- LATER: This used to be recommended.  Should it be reinstated? -/
-- EX3 (XtimesYinZ_spec)
-- (Rocq marked this exercise optional -- `EX3?`.)
/- State and prove a specification of `XtimesYinZ`. -/

-- SOLUTION
/- Here is a specification in the style of `plus2_spec`: -/
theorem XtimesYinZ_spec1 (st : State) (nx ny : Nat) (st' : State)
    (hx : st[X] = nx) (hy : st[Y] = ny) (heval : st =[ XtimesYinZ ]=> st') :
    st'[Z] = nx * ny := by
  unfold XtimesYinZ at heval
  cases heval with
  | E_Asgn _ _ n _ h =>
      simp only [Aexp.eval] at h
      subst hx hy
      rw [TotalMap.update_eq]
      exact h.symm

/- Though perhaps a cleaner specification would be: -/
theorem XtimesYinZ_spec (st : State) :
    st =[ XtimesYinZ ]=> (Z →ₜ st[X] * st[Y] ; st) := by
  unfold XtimesYinZ
  apply Ceval.E_Asgn
  rfl

/- A less informative specification would be ... -/
theorem XtimesYinZ_spec2 (st : State) : ∃ st', st =[ XtimesYinZ ]=> st' := by
  exact ⟨(Z →ₜ st[X] * st[Y] ; st), by unfold XtimesYinZ; apply Ceval.E_Asgn; rfl⟩
-- /SOLUTION
-- GRADE_MANUAL 3: XtimesYinZ_spec
-- []

-- EX3! (loop_never_stops)
/-
  Hint: proceed by induction on the assumed derivation showing that `loop`
  terminates.  Most of the cases are immediately contradictory and so can be
  solved in one step (by `simp`/`discriminate` on the impossible command
  equation).
-/
theorem loop_never_stops (st st' : State) : ¬ (st =[ loop ]=> st') := by
  -- ADMITTED
  intro contra
  -- Generalize over the command so the induction remembers what `loop` is.
  have key : ∀ (c : Com) (s s' : State), (s =[ c ]=> s') → c = loop → False := by
    intro c s s' hce
    induction hce with
    | E_WhileFalse b s0 c0 hb =>
        intro heq; unfold loop at heq; injection heq with e1 _
        subst e1; simp [Bexp.eval] at hb
    | E_WhileTrue s0 s0' s0'' b c0 hb hc hloop ih1 ih2 =>
        intro heq; exact ih2 heq
    | E_Skip s0 => intro heq; simp [loop] at heq
    | E_Asgn s0 a n x h => intro heq; simp [loop] at heq
    | E_Seq c1 c2 s0 s0' s0'' h1 h2 ih1 ih2 => intro heq; simp [loop] at heq
    | E_IfTrue s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
    | E_IfFalse s0 s0' b c1 c2 hb hc ih => intro heq; simp [loop] at heq
  exact key loop st st' contra rfl
  -- /ADMITTED
-- []

/- LATER: Marc Bezem 2022:
   There are trade-offs between using tactics and additional lemmas.  Here is
   a case where a lemma would make things clearer.  For `loop_never_stops`,
   the surprise is that it is proved by induction, and the Rocq tactic
   `remember` is hard to understand.  The following formulation explains the
   induction better:

     Theorem loop_never_stops' : forall st st' c,
       st =[ c ]=> st' -> c = loop -> False.

   The equivalence of the two formulations is an easy lemma.  (Note: the Lean
   proof above already takes exactly this generalized-`key` shape.)
   BCP 23: Not sure I see a big difference between the two presentations: both
   statements are negations, and the `remember` in the proof is avoided in
   the new one by introducing an equality in the theorem statement that IMO
   is not very pretty... -/

-- EX3 (no_whiles_eqv)
/-
  The following function yields `true` just on programs with no while
  loops.  Using `inductive`, write a property `NoWhilesR` that holds
  exactly when `c` is while-free, then prove it equivalent to `Com.no_whiles`.
-/

def Com.no_whiles (c : Com) : Bool :=
  match c with
  | skip      => true
  | asgn _ _  => true
  | seq c1 c2 => no_whiles c1 && no_whiles c2
  | cond _ ct cf => no_whiles ct && no_whiles cf
  | whileDo _ _ => false

inductive NoWhilesR : Com → Prop where
  -- SOLUTION
  | nw_Skip : NoWhilesR .skip
  | nw_Asgn (x : String) (a : Aexp) : NoWhilesR (.asgn x a)
  | nw_Seq (c1 c2 : Com) (h1 : NoWhilesR c1) (h2 : NoWhilesR c2) :
      NoWhilesR (.seq c1 c2)
  | nw_If (b : Bexp) (c1 c2 : Com) (h1 : NoWhilesR c1) (h2 : NoWhilesR c2) :
      NoWhilesR (.cond b c1 c2)
  -- /SOLUTION

theorem no_whiles_eqv (c : Com) : Com.no_whiles c = true ↔ NoWhilesR c := by
  -- ADMITTED
  constructor
  · induction c with
    | skip => intro _; exact .nw_Skip
    | asgn x a => intro _; exact .nw_Asgn x a
    | seq c1 c2 ih1 ih2 =>
        intro h; simp only [Com.no_whiles, Bool.and_eq_true] at h
        exact .nw_Seq _ _ (ih1 h.1) (ih2 h.2)
    | cond b c1 c2 ih1 ih2 =>
        intro h; simp only [Com.no_whiles, Bool.and_eq_true] at h
        exact .nw_If _ _ _ (ih1 h.1) (ih2 h.2)
    | whileDo b c ih => intro h; simp [Com.no_whiles] at h
  · intro h
    induction h with
    | nw_Skip => rfl
    | nw_Asgn x a => rfl
    | nw_Seq c1 c2 h1 h2 ih1 ih2 => simp [Com.no_whiles, ih1, ih2]
    | nw_If b c1 c2 h1 h2 ih1 ih2 => simp [Com.no_whiles, ih1, ih2]
  -- /ADMITTED
-- []

-- EX4 (no_whiles_terminating)
/-
  Imp programs that don't involve while loops always terminate.  State and
  prove a theorem `no_whiles_terminating` that says this.  Use either
  `Com.no_whiles` or `NoWhilesR`, as you prefer.
-/

theorem no_whiles_terminating (c : Com) (st : State) (h : NoWhilesR c) :
    ∃ st', st =[ c ]=> st' := by
  -- SOLUTION
  induction h generalizing st with
  | nw_Skip => exact ⟨st, .E_Skip st⟩
  | nw_Asgn x a => exact ⟨(x →ₜ Aexp.eval st a ; st), .E_Asgn st a (Aexp.eval st a) x rfl⟩
  | nw_Seq c1 c2 h1 h2 ih1 ih2 =>
      obtain ⟨st', hc1⟩ := ih1 st
      obtain ⟨st'', hc2⟩ := ih2 st'
      exact ⟨st'', .E_Seq c1 c2 st st' st'' hc1 hc2⟩
  | nw_If b c1 c2 h1 h2 ih1 ih2 =>
      cases hb : Bexp.eval st b with
      | true =>
          obtain ⟨st', hc1⟩ := ih1 st
          exact ⟨st', .E_IfTrue st st' b c1 c2 hb hc1⟩
      | false =>
          obtain ⟨st', hc2⟩ := ih2 st
          exact ⟨st', .E_IfFalse st st' b c1 c2 hb hc2⟩

/- And here is an alternative solution by induction on `c` (using
   `Com.no_whiles` instead of `NoWhilesR`): -/
theorem no_whiles_terminating' (c : Com) (st1 : State)
    (hb : Com.no_whiles c = true) : ∃ st2, st1 =[ c ]=> st2 := by
  induction c generalizing st1 with
  | skip => exact ⟨st1, .E_Skip st1⟩
  | asgn x a => exact ⟨(x →ₜ Aexp.eval st1 a ; st1), .E_Asgn st1 a (Aexp.eval st1 a) x rfl⟩
  | seq c1 c2 ih1 ih2 =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      obtain ⟨st1', hc1⟩ := ih1 st1 hb.1
      obtain ⟨st1'', hc2⟩ := ih2 st1' hb.2
      exact ⟨st1'', .E_Seq c1 c2 st1 st1' st1'' hc1 hc2⟩
  | cond b ct cf ih1 ih2 =>
      simp only [Com.no_whiles, Bool.and_eq_true] at hb
      cases hbev : Bexp.eval st1 b with
      | true =>
          obtain ⟨st2, h⟩ := ih1 st1 hb.1
          exact ⟨st2, .E_IfTrue st1 st2 b ct cf hbev h⟩
      | false =>
          obtain ⟨st2, h⟩ := ih2 st1 hb.2
          exact ⟨st2, .E_IfFalse st1 st2 b ct cf hbev h⟩
  | whileDo b c ih => simp [Com.no_whiles] at hb
  -- /SOLUTION
-- []

/-
  Claude: PORT STATUS — this chapter is a work in progress.

  DONE (compiling; survives to_verso → HL.ImpVerso builds):
    - AExp module: Aexp/Bexp syntax, Aexp.eval/Bexp.eval, Aexp.optimize_0plus + soundness
    - Tactic combinators (try, <;>, repeat, macro), lia, handy-tactics recap
    - Bexp.optimize_0plus_b (EX3)
    - Evaluation as a Relation: AevalR + `==>`, inference rules,
      aevalR_iff_aeval (x2), BevalR (EX3) + bevalR_iff_beval,
      AevalRDivision / AevalRExtended, tradeoffs
    - Expressions With Variables: State, coercions, Aexp.eval/Bexp.eval, Com + examples
    - Evaluating Commands: Com.ceval_fun_no_while, Ceval + `=[ c ]=>`, examples,
      ceval_deterministic
    - Reasoning About Imp Programs: pup_to_n/pup_to_2_ceval, plus2_spec,
      XtimesYinZ_spec (EX3), loop_never_stops (EX3!), Com.no_whiles/NoWhilesR +
      no_whiles_eqv (EX3), no_whiles_terminating (EX4)

  NOT DONE YET — remaining sections of sfdev/lf/Imp.v to port:
    - Case Study (Optional), Imp.v:2774
        * subtract_slowly_spec (EX4?, Imp.v:2919): loop-invariant style proof
          about `subtract_slowly`.
    - Additional Exercises, Imp.v:2986
        * stack_compiler (EX3, Imp.v:2988): define `s_execute` (stack machine)
          and `s_compile : aexp -> list sinstr`; needs a `SInstr` inductive
          (SPush/SLoad/SPlus/SMinus/SMult) and a list-based stack.
        * execute_app (EX3, Imp.v:3114)
        * stack_compiler_correct (EX3, Imp.v:3134): the correctness theorem;
          the standard proof needs a strengthened lemma over an arbitrary
          initial stack (generalize the stack before inducting).
        * short_circuit (EX3?, Imp.v:3184): short-circuiting `Bexp.eval`.
        * break_imp (EX4?, Imp.v:3227): extends Com with `CBreak`; new
          relational semantics `ceval` carrying a `result` (SContinue/SBreak).
          Large. See verso-book branch (lf/Imp.lean ~line 1141, CEvalBreak) for
          a prior take on the signal type.
        * while_break_true (EX3A?, Imp.v:3454)
        * ceval_deterministic for break (EX4A?, Imp.v:3477)
        * exn_imp (EX4A?, Imp.v:3524): exceptions variant. Large.
        * add_for_loop (EX4?, Imp.v:3728): add a C-style `for` loop to Com,
          its notation, and extend ceval.

  When resuming: keep the established conventions (dot-notation constructors,
  `→ₜ`/`st[x]` state ops, no `<{ }>` grammar, `-- EXn`/`-- SOLUTION`/`-- ADMITTED`
  /`-- GRADE_*` markers, ``` fences for display blocks), and after each chunk
  run `make check-verso-chapters` so the to_verso round-trip stays green.
-/
