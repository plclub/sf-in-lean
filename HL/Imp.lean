/- Imp: Simple Imperative Programs -/

/- INSTRUCTORS: This chapter plus `Maps` takes a little more than one
   80-minute lecture.  It could be streamlined a bit further without
   losing much, by removing (for example) the inference rules and BNF
   notations from the terse version.

   (BCP 21: ... Actually, I tried removing inference rules from the
   TERSE version; eventually decided that it makes some of the
   definitions harder to talk about.) -/
/- SOONER: Needs some WORKINCLASSes and some quizzes -/
/- LATER: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare (reasoning about arrays /
   aliasing / etc.). -/
/- SOONER: BCP 25: Maybe we should write /\ instead of && in assertions,
   to save a mismatch in the dec_minimum exercise in Hoare2? -/
/- HIDE: At some point we could consider moving material from the old
   HoareLists to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures.
   Also, we now have a whole volume on real separation logic... -/

-- MWH (port note): The Rocq chapter's "Rocq Automation" tour has been
-- retooled here for Lean.  The tactic combinators `try` and `repeat` (and the
-- custom-tactic `macro`) are introduced in this chapter; `<;>` and `simp` were
-- already introduced in Logical Foundations (`<;>` in `Induction`)
-- so we use them freely and the `<;>` section
-- below is a recap.  For linear arithmetic we use `lia`;
-- NOTE that LF currently
-- introduces `omega`, not `lia`, so this needs to be reconciled volume-wide
-- (either introduce `lia` in LF, or keep `omega`).

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
  later in this volume we develop a theory of _program equivalence_ and introduce
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

-- MWH: Will we develop `ImpParser`? Mentioned below as an optional chapter
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

  b := bool
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

/- chenson2018: TODO: seal evaluators with `@[irreducible]` and prove
   *characterizing lemmas* (one
   `rfl` equation per constructor) that proofs rewrite with instead of
   unfolding the definition; tag lemmas `@[simp]`.
 -/

def Aexp.eval (a : Aexp) : Nat :=
  match a with
  | num   n     =>  n
  | plus  a1 a2 =>  eval a1 + eval a2
  | minus a1 a2 =>  eval a1 - eval a2
  | mult  a1 a2 =>  eval a1 * eval a2

example : Aexp.eval (.plus (.num 2) (.num 2)) = 4 := by rfl

/- Similarly, evaluating a boolean expression yields a boolean. -/

def Bexp.eval (b : Bexp) : Bool :=
  match b with
  | bool b     =>  b
  | eq   a1 a2 =>  a1.eval == a2.eval
  | neq  a1 a2 =>  a1.eval != a2.eval
  | le   a1 a2 =>  a1.eval ≤ a2.eval
  | gt   a1 a2 =>  a1.eval > a2.eval
  | not  b1    =>  !eval b1
  | and  b1 b2 =>  eval b1 && eval b2

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
  out of the definitions. Suppose we define a function that takes an
  arithmetic expression and slightly simplifies it, changing every
  occurrence of `0 + e` (i.e., `.plus (.num 0) e`) into just `e`.
-/
-- /FULL

def Aexp.optimize_0plus (a : Aexp) : Aexp :=
  match a with
  | num   n          => num n
  | plus  (num 0) e2 => optimize_0plus e2
  | plus  e1      e2 => plus  (optimize_0plus e1) (optimize_0plus e2)
  | minus e1      e2 => minus (optimize_0plus e1) (optimize_0plus e2)
  | mult  e1      e2 => mult  (optimize_0plus e1) (optimize_0plus e2)

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

  Here is a first, deliberately explicit proof. It works, but notice how
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

/- mwhicks1: We need to redo this section based on the assumption that
   a bunch of this stuff will be covered in the IndPropRegexp chapter.
-/

-- FULL
/-
  The amount of repetition in that last proof is a little annoying.  And
  if either the language of arithmetic expressions or the optimization
  being proved sound were significantly more complex, it would start to be
  a real problem.

  So far, we've been driving each subgoal by hand. Lean also provides
  _combinators_ that build bigger tactics out of smaller ones, letting us
  discharge many similar subgoals at once. Getting used to them takes a
  little energy, but it lets us scale up to more complex definitions and
  more interesting properties without drowning in boring, repetitive
  detail.
-/
-- /FULL
-- TERSE: /- That last proof was repetitive. Time for a few combinators. -/

/-
  ######################################################################
  ## The `try` combinator
-/

/-
  If `t` is a tactic, then `try t` is a tactic that is just like `t`
  except that, if `t` fails, `try t` _successfully_ does nothing at all
  (rather than failing).
-/

/- LATER: Maybe we want to move the discussion of "try solve" from later to
   here?  It might be helpful for students, but it will make this
   already-longish chapter a bit longer... -/

example (P : Prop) (hp : P) : P := by
  try rfl -- `rfl` would fail here, but `try` swallows the failure...
  exact hp -- ...so we can still finish some other way.

example (ae : Aexp) : Aexp.eval ae = Aexp.eval ae := by
  try rfl -- here `try rfl` just does `rfl`

/-
  There is not much reason to use `try` in completely manual proofs like
  these, but it is very useful together with the `<;>` combinator,
  which we introduced in _Logical Foundations_' `Induction` chapter.
-/

/-
  For example, consider the following trivial lemma.  Splitting on `n`
  leaves two subgoals that are discharged identically:
-/

example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero   => lia
  | succ k => lia

-- TERSE: /- We can collapse the two identical branches with `<;>`: -/
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n <;> lia -- run `cases n`, then `lia` on each subgoal

-- FULL
/-
  Using `<;>` we can get rid of the repetition in the proof that was
  bothering us a little while ago.  Most cases follow directly from the
  induction hypotheses, so we can dispatch them uniformly and only pause
  on the interesting one.
-/
-- /FULL

/- mwhicks1: The following proof is badly formed. It doesn't follow
   from the tacticals we just introduced, i.e., `try` and `<;>`.
-/

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

      and the IH for `a2` is exactly what we need. On the other hand, if
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
  would write it out in full. It would be better and clearer to drop it and
  just say, at the top, "Most cases are either immediate or direct from the
  IH. The only interesting case is the one for `.plus`..."  Our `<;>`
  version above already does exactly this.
-/
-- /FULL

/- mwhicks1: The following is the Rocq version of this proof, which
   hasn't yet been translated. It might be we won't need it, depending
   on the best way to do it in Lean.

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

/-
  mwhicks1: The `;` tactical has a more general form in Rocq; we might
  want to introduce the equivalent (or a different!) pattern in Lean.
  In Rocq: if `T`, `T1`, ..., `Tn` are tactics, then

  ```
  T; [T1 | T2 | ... | Tn]
  ```

  first performs `T` and then performs `T1` on the first subgoal generated by
  `T`, `T2` on the second subgoal, etc.  So `T;T'` is just the special case
  where every `Ti` is the same tactic (`T; [T' | T' | ... | T']`). This
  bracketed-list form has no direct Lean surface syntax.
-/

/-
  mwhicks1: The original Rocq has a long discussion of the `repeat`
  combinator, using the example of list membership. None of it is
  specific to Imp, so I have removed it, assuming it gets handled
  in LF, or gets dropped.

  In Rocq, `10 ∈ [1..10]` was proved first with `repeat`:

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
   ```
-/

/-
  ######################################################################
  ## Defining new tactics
-/

-- mwhicks1: Much of this will need to change. Leaving it here for reference.

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

example (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (Q ∧ P) := by
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

-- mwhicks1: Probably this will get introduced in an earlier LF chapter.

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

/- mwhicks1: Probably this section gets dropped; will be in LF. -/

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
  | bool b    =>  bool b
  | eq a1 a2  =>  eq a1.optimize_0plus a2.optimize_0plus
  | neq a1 a2 =>  neq a1.optimize_0plus a2.optimize_0plus
  | le a1 a2  =>  le a1.optimize_0plus a2.optimize_0plus
  | gt a1 a2  =>  gt a1.optimize_0plus a2.optimize_0plus
  | not b1    =>  not (optimize_0plus_b b1)
  | and b1 b2 =>  and (optimize_0plus_b b1) (optimize_0plus_b b2)
  -- /ADMITDEF

/- optimize_0plus_b_test1 -/
example :
    Bexp.optimize_0plus_b
        (.not (.gt (.plus (.num 0) (.num 4)) (.num 8)))
      = (.not (.gt (.num 4) (.num 8))) := by rfl -- ADMITTED
-- GRADE_THEOREM 0.5: optimize_0plus_b_test1

/- optimize_0plus_b_test2 -/
example :
    Bexp.optimize_0plus_b
        (.and (.le (.plus (.num 0) (.num 4)) (.num 5)) (.bool true))
      = (.and (.le (.num 4) (.num 5)) (.bool true)) := by rfl -- ADMITTED
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
  recursion. Another way to think about evaluation -- one that is often
  more flexible -- is as a _relation_ between expressions and their
  values. This perspective leads to inductive definitions like the
  following. We name the hypotheses in each case (`h1`, `h2`); this
  gives us readable names to refer to during proofs.
-/
-- /FULL

inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) :
      Aexp.evalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat)
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.mult a1 a2) (n1 * n2)

-- FULL
/-
  A small notational aside. We could instead have presented this relation
  with *positional* hypotheses -- no names for the premises:

  ```
  inductive Aexp.evalR : Aexp → Nat → Prop where
    | E_ANum (n : Nat) :
        Aexp.evalR (.num n) n
    | E_APlus (e1 e2 : Aexp) (n1 n2 : Nat) :
        Aexp.evalR e1 n1 →
        Aexp.evalR e2 n2 →
        Aexp.evalR (.plus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2 : Aexp) (n1 n2 : Nat) :
        Aexp.evalR e1 n1 →
        Aexp.evalR e2 n2 →
        Aexp.evalR (.minus e1 e2) (n1 - n2)
    | E_AMult (e1 e2 : Aexp) (n1 n2 : Nat) :
        Aexp.evalR e1 n1 →
        Aexp.evalR e2 n2 →
        Aexp.evalR (.mult e1 e2) (n1 * n2)
  ```

  The version above instead gives explicit names to the hypotheses in each
  case (the `h1`/`h2`). Naming the hypotheses gives us more control over the
  names chosen during proofs involving the relation, at the cost of making
  the definition a little more verbose. We adopt the named style.
-/
-- /FULL

/-
  mwhicks1: We will very likely want to use different notation, both
  here and for defining AExp and BExp terms themselves.
-/

/-
  It will be convenient to have an infix notation for `Aexp.evalR`.  We'll
  write `e ⇓ n` to mean that arithmetic expression `e` evaluates to
  value `n`.  (We scope the notation to this namespace so it doesn't
  collide with other evaluation relations later.)  In Lean the notation is
  declared right after the inductive.
-/

scoped notation:55 e:56 " ⇓ " n:56 => Aexp.evalR e n

/-
  ######################################################################
  ## Inference Rule Notation
-/

-- FULL
/-
  In informal discussions, it is convenient to write the rules for
  `Aexp.evalR` and similar relations in the more readable graphical form of
  _inference rules_, where the premises above the line justify the
  conclusion below the line.  For example, the constructor `E_APlus`

  ```
      | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) :
          Aexp.evalR a1 n1 →
          Aexp.evalR a2 n2 →
          Aexp.evalR (.plus a1 a2) (n1 + n2)
  ```

  can be written like this as an inference rule:

  ```
                            e1 ⇓ n1
                            e2 ⇓ n2
                      --------------------          (E_APlus)
                      plus e1 e2 ⇓ n1+n2
  ```

  Formally, there is nothing deep about inference rules: they are just
  implications. You can read the rule name on the right as the name of the
  constructor and read each of the linebreaks between the premises above the
  line (as well as the line itself) as `→`.  All the variables mentioned in
  the rule (`e1`, `n1`, etc.) are implicitly bound by universal quantifiers
  at the beginning. (Such variables are often called _metavariables_ to
  distinguish them from the variables of the language we are defining. At
  the moment, our arithmetic expressions don't include variables, but we'll
  soon be adding them.) The whole collection of rules is understood as being
  wrapped in an inductive declaration. In informal prose, this is sometimes
  indicated by saying something like "Let `aevalR` be the smallest relation
  closed under the following rules...".

  To summarize: a group of inference rules corresponds to a single inductive
  definition; each rule's name corresponds to a constructor name; above the
  line are the premises, below the line the conclusion; and metavariables
  like `e1` and `n1` are implicitly universally quantified. The whole
  collection of rules defines `⇓` as the smallest relation closed under
  them:

  ```
                          -----------                (E_ANum)
                          num n ⇓ n

                            e1 ⇓ n1
                            e2 ⇓ n2
                      --------------------           (E_APlus)
                      plus e1 e2 ⇓ n1+n2

                            e1 ⇓ n1
                            e2 ⇓ n2
                     ---------------------           (E_AMinus)
                     minus e1 e2 ⇓ n1-n2

                            e1 ⇓ n1
                            e2 ⇓ n2
                      --------------------           (E_AMult)
                      mult e1 e2 ⇓ n1*n2
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

/-
  mwhicks1: both of the next two quizzes were hidden in the source
  material; the first quiz here is shown, the second is kept under `HIDE`.
-/
-- QUIZ
/-
  Which rules are needed to prove the following?

  ```
  .mult (.plus (.num 3) (.num 1)) (.num 0) ⇓ 0
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
  .minus (.num 3) (.minus (.num 2) (.num 1)) ⇓ 2
  ```

  (A) `E_ANum` and `E_APlus`
  (B) `E_ANum` only
  (C) `E_ANum` and `E_AMinus`
  (D) `E_AMinus` and `E_APlus`
  (E) `E_ANum`, `E_AMinus`, and `E_APlus`
-/
-- /QUIZ
-- /HIDE

/-
  mwhicks1: Not sure if we need ⇓b is needed, or whether we can define
  ⇓ overloaded. Don't understand Lean notation yet!
-/

-- FULL
-- EX1? (beval_rules)
/-
  Here, again, is the definition of the `Bexp.eval` function:

  ```
  def Bexp.eval (b : Bexp) : Bool :=
    match b with
    | bool b     => b
    | eq   a1 a2 => a1.eval == a2.eval
    | neq  a1 a2 => a1.eval != a2.eval
    | le   a1 a2 => a1.eval ≤ a2.eval
    | gt   a1 a2 => a1.eval > a2.eval
    | not  b1    => !eval b1
    | and  b1 b2 => eval b1 && eval b2
  ```

  Write out a corresponding definition of boolean evaluation as a relation
  (in inference rule notation).
-/
-- SOLUTION
/-
  Answer (`⇓b` is defined below):

  ```
                          -------------              (E_bool)
                          bool b ⇓b b

                            e1 ⇓ n1
                            e2 ⇓ n2
                     -------------------------        (E_BEq)
                     eq e1 e2 ⇓b (n1 =? n2)

                            e1 ⇓ n1
                            e2 ⇓ n2
                   -------------------------------    (E_BNeq)
                   neq e1 e2 ⇓b negb (n1 =? n2)

                            e1 ⇓ n1
                            e2 ⇓ n2
                     --------------------------       (E_BLe)
                     le e1 e2 ⇓b (n1 <=? n2)

                            e1 ⇓ n1
                            e2 ⇓ n2
                  -------------------------------     (E_BGt)
                  gt e1 e2 ⇓b negb (n1 <=? n2)

                             e ⇓b b
                        ------------------            (E_BNot)
                        not e ⇓b negb b

                            e1 ⇓b b1
                            e2 ⇓b b2
                    --------------------------        (E_BAnd)
                    and e1 e2 ⇓b andb b1 b2
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
    a ⇓ n ↔ Aexp.eval a = n := by
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
    a ⇓ n ↔ Aexp.eval a = n := by
  -- WORKINCLASS
  constructor
  · intro h; induction h <;> simp_all [Aexp.eval]
  · intro h; subst h; induction a <;> constructor <;> assumption
  -- /WORKINCLASS
-- /HIDEFROMADVANCED

-- EX3 (bevalR)
/-
  Write a relation `Bexp.evalR` in the same style as `Aexp.evalR`, and prove that
  it is equivalent to `Bexp.eval`.
-/

inductive Bexp.evalR : Bexp → Bool → Prop where
  -- SOLUTION
  | E_bool (b : Bool) : Bexp.evalR (.bool b) b
  | E_BEq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.eq a1 a2) (n1 == n2)
  | E_BNeq (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.neq a1 a2) (n1 != n2)
  | E_BLe (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.le a1 a2) (n1 ≤ n2)
  | E_BGt (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : a1 ⇓ n1) (h2 : a2 ⇓ n2) :
      Bexp.evalR (.gt a1 a2) (n1 > n2)
  | E_BNot (b : Bexp) (bv : Bool) (h : Bexp.evalR b bv) :
      Bexp.evalR (.not b) (!bv)
  | E_BAnd (b1 b2 : Bexp) (tv1 tv2 : Bool) (h1 : Bexp.evalR b1 tv1) (h2 : Bexp.evalR b2 tv2) :
      Bexp.evalR (.and b1 b2) (tv1 && tv2)
  -- /SOLUTION

scoped notation:55 e:56 " ⇓b " b:56 => Bexp.evalR e b

theorem bevalR_iff_beval (b : Bexp) (bv : Bool) :
    b ⇓b bv ↔ Bexp.eval b = bv := by
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

end AExp

/-
  ######################################################################
  ## Computational vs. Relational Definitions
-/

-- FULL
/-
  For the definitions of evaluation for arithmetic and boolean
  expressions, the choice of whether to use functional or relational
  definitions is mainly a matter of taste. However, there are many
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
  `.div (.num 5) (.num 0)`?). But extending the relation is easy.
-/
-- TERSE: /- What should `Aexp.eval` return for `.div (.num 1) (.num 0)`?? -/

inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_ANum (n : Nat) : Aexp.evalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.mult a1 a2) (n1 * n2)
  | E_ADiv (a1 a2 : Aexp) (n1 n2 n3 : Nat)             -- NEW
      (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) (hpos : n2 > 0) (hdiv : n2 * n3 = n1) :
      Aexp.evalR (.div a1 a2) n3

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

inductive Aexp.evalR : Aexp → Nat → Prop where
  | E_Any (n : Nat) : Aexp.evalR .any n                   -- NEW
  | E_ANum (n : Nat) : Aexp.evalR (.num n) n
  | E_APlus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.plus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.minus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : Aexp) (n1 n2 : Nat) (h1 : Aexp.evalR a1 n1) (h2 : Aexp.evalR a2 n2) :
      Aexp.evalR (.mult a1 a2) (n1 * n2)

end AevalRExtended

/-
  mwhicks1: The following text seems not quite right to me. First, you can
  use options for partial functions, and that's very natural to do in Lean
  as a monad. Second, and related, monadic functions need not even be
  terminating if the implement the `CCPO` typeclass and are labeled as
  a `partial_fixpoint`. Maybe we don't want to get into the second thing here,
  but failing to mention options (which I think were introduced in LF) seems
  a bit surprising.
-/

-- FULL
/-
  At this point you may be wondering: which of these styles should I use
  by default?

  Where the thing being defined is not easy to express as a function --
  or is genuinely _not_ a function -- there is no real choice. When both
  styles are workable, relational definitions can be more elegant and
  easier to understand, and Lean generates useful inversion and induction
  principles from them. On the other hand, functional definitions are
  automatically deterministic and total (for a relation we must _prove_
  these if we need them), and we can use Lean's computation mechanism to
  simplify them during proofs.

  In large developments it is common to give a definition in _both_
  styles plus a lemma that the two coincide, allowing later proofs to
  switch between points of view at will -- exactly what we did above.
-/
-- /FULL
-- TERSE: /- Functional: computation. Relational: expressive. Best: both, proved equivalent. -/

/-
  ######################################################################
  # Expressions With Variables
-/

-- FULL
/-
  Let's return to defining Imp. The next thing we need to do is to
  enrich our arithmetic and boolean expressions with variables. To keep
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
/- LATER: (Note copied from Equiv right before the assign_aequiv
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating states as
   an ADT should be raised there. -/

/-
  Since we'll want to look variables up to find out their current values,
  we'll use total maps from the `Maps` chapter. A _machine state_ (or
  just _state_) represents the current values of all variables at some
  point in the execution of a program.
-/
-- FULL
/-
  For simplicity, we assume that the state is defined for _all_ variables,
  even though any given program is only able to mention a finite number of
  them. Because each variable stores a natural number, we represent the
  state as a total map from strings (variable names) to `Nat`, and will use
  `0` as the default value in the store.
-/
-- /FULL

/- We give the type of variable identifiers a name, `Ident`. For now it is just
   `String`; naming it makes the intent clearer.
-/
abbrev Ident := String
abbrev State := TotalMap Ident Nat

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
  | id (x : Ident)                -- NEW
  | plus (a1 a2 : Aexp)
  | minus (a1 a2 : Aexp)
  | mult (a1 a2 : Aexp)

/-
  chenson2018: Rather than define identifiers as Ident, a more general approach is
  to use a *type variable* with `DecidableEq` (as the
  `Maps` chapter does), threaded through `Aexp`/`Bexp`/`Com`/`State`.  Stashed
  for a future decision; the parameterized version would look like:

  ```
  inductive Aexp (V : Type) where
    | num (n : Nat)
    | id (x : V)
    | plus (a1 a2 : Aexp V)
    | minus (a1 a2 : Aexp V)
    | mult (a1 a2 : Aexp V)
  -- … then `Bexp V`, `Com V`, `abbrev State (V) [DecidableEq V] :=
  -- TotalMap V Nat`, and `[DecidableEq V]` wherever a lookup/update is
  -- performed.
  ```
-/

/- The `Bexp` definition is unchanged, except that it now refers to the new `Aexp`. -/

inductive Bexp where
  | bool (b : Bool)
  | eq (a1 a2 : Aexp)
  | neq (a1 a2 : Aexp)
  | le (a1 a2 : Aexp)
  | gt (a1 a2 : Aexp)
  | not (b : Bexp)
  | and (b1 b2 : Bexp)

/-
  mwhicks1: SHould we be defining variables as lowercase letters, rather
  than uppercase ones? Maybe notational conventions in Lean should be
  different.
-/

/- Defining a few variable names as shorthands will make examples easier
   to read. -/
/- INSTRUCTORS: We usually don't use x as a "bare identifier" in examples
   -- it is normally wrapped in an id constructor.  If this were _always_
   the case, then it would make more sense to define the notation [x] to
   mean [id (Id 0)].  But there quite a few counterexamples. Maybe we
   could define [xx] to mean [id (Id 0)], or some such? But it's still
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

def W : Ident := "W"
def X : Ident := "X"
def Y : Ident := "Y"
def Z : Ident := "Z"

-- FULL
/-
  (This convention for naming program variables (`X`, `Y`, `Z`) clashes a
  bit with our earlier use of uppercase letters for types. Since we're not
  using polymorphism heavily in the chapters developed to Imp, this
  overloading should not cause confusion.)
-/
-- /FULL

/-
  ######################################################################
  ## Notations
-/

/-
  mwhicks1: The Rocq chapter builds a custom `<{ ... }>` grammar
  so that Imp programs can be written with concrete `+`, `:=`, `;`,
  `if`/`while` syntax. We take a lighter route for now:
  three coercions let us drop the `id`/`num`/`bool` wrappers,
  and we otherwise write programs with the ordinary constructors.
-/

-- FULL
/-
  To make Imp programs easier to read and write, we introduce a few implicit
  coercions. In Lean, a `Coe` instance tells the elaborator how to turn a
  value of one type into another automatically:
   - `Coe Ident Aexp` lets us write a bare variable (an `Ident`) where an
     `Aexp` is expected; the identifier is implicitly wrapped with `id`.
   - `OfNat Aexp n` lets us write a numeric literal where an `Aexp` is
     expected; it is implicitly wrapped with `num`.
   - `Coe Bool Bexp` lets us write a boolean literal (`true`/`false`) where a
     `Bexp` is expected; it is implicitly wrapped with `bool`.
-/
-- /FULL

instance : Coe Ident Aexp where
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
  | num   n     =>  n
  | id    x     =>  st[x]                    -- NEW
  | plus  a1 a2 =>  eval st a1 + eval st a2
  | minus a1 a2 =>  eval st a1 - eval st a2
  | mult  a1 a2 =>  eval st a1 * eval st a2

def Bexp.eval (st : State) (b : Bexp) : Bool :=
  match b with
  | bool b      =>  b
  | eq   a1 a2  =>  Aexp.eval st a1 == Aexp.eval st a2
  | neq  a1 a2  =>  Aexp.eval st a1 != Aexp.eval st a2
  | le   a1 a2  =>  Aexp.eval st a1 ≤ Aexp.eval st a2
  | gt   a1 a2  =>  Aexp.eval st a1 > Aexp.eval st a2
  | not  b1     =>  !eval st b1
  | and  b1 b2  =>  eval st b1 && eval st b2

/- We abbreviate the empty state `∅` (every variable `0`) as `empty_st`,
   and reuse the total-map update notation `x →ₜ v ; st` for states. -/

abbrev empty_st : State := ∅

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
  (or _statements_). Informally, commands `c` are described by the
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
  | asgn (x : Ident) (a : Aexp)
  | seq (c1 c2 : Com)
  | cond (b : Bexp) (c1 c2 : Com)
  | whileDo (b : Bexp) (c : Com)

-- FULL
/-
  As an example, here is the factorial function again, written as a formal
  definition. When this command terminates, the variable `Y` will
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

/- mwhicks1: At this point in the Rocq chapter there was discussion about
   desugaring notation to help with proofs and debugging. Refer back there
   for pedagogy once we work out the Lean notation story.
-/

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
   so that we can talk about normal forms and such. Probably we should do it
   here too, for consistency. (Won't change much except the type
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
  the `loop` program above would run forever. Since Lean aims to be not
  just a programming language but also a consistent logic, any
  potentially non-terminating function must be rejected. Here is what
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
  similar to what we did for `Aexp.evalR` above.
-/

-- FULL
-- HIDEFROMADVANCED
/-
  This is an important change. Besides freeing us from awkward workarounds,
  it gives us more flexibility in the definition. For example, if we
  add nondeterministic features like `any` to the language, we want the
  definition of evaluation to be nondeterministic -- i.e., not only will it
  not be total, it will not even be a function!
-/
-- /HIDEFROMADVANCED
-- /FULL

/-
  mwhicks1: I kind of hate this notation. Is there something more standard
  in Lean? CSLib precedent maybe?
-/

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

inductive Ceval : Com → State → State → Prop where
  | E_Skip (st : State) :
      Ceval .skip st st
  | E_Asgn (st : State) (a : Aexp) (n : Nat) (x : Ident)
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
-- INSTRUCTORS: Answer is given later (`quiz2_answer`) as it depends on `ceval_deterministic`.
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
   optional? Not everybody will want to spend time on it. -/

-- FULL
/-
  Changing from a computational to a relational definition of evaluation
  is a good move because it frees us from the artificial requirement that
  evaluation be a total function. But it raises a question: is the
  relational definition really a partial _function_? Could the same
  command, from the same state, evaluate to two different final states?
  In fact this cannot happen: `ceval` _is_ a partial function.
-/
-- /FULL
-- TERSE: /- Finally, we should pause to check that our evaluation relation really is a (partial) function... -/

/- LATER: Informal proof needed! (And one can surely be found in some past
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

-- EX3? (pup_to_n)
/-
  Write an Imp program that sums the numbers from `1` to `X` (inclusive)
  in the variable `Y`.  Your program should update the state as shown in
  `pup_to_2_ceval`, which you can reverse-engineer to discover the program
  you should write.  The proof of that theorem will be somewhat lengthy.
-/

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

/- LATER: This section doesn't seem very useful -- to anybody! It takes too
   much time to go through it in class, and even for advanced students it's
   too low-level and grubby to be a very convincing motivation for what
   follows -- i.e., to feel motivated by its grubbiness, you have to
   understand it, but this takes more time than it's worth. Better to cut
   the whole rest of the file (except the further exercises at the very end),
   or at least make it optional.
   (BCP 10/18: However, this removes quite a few exercises. Is the homework
   assignment still meaty enough? I'm going to leave it as-is for now, but
   we should reconsider this later.) -/

-- FULL
/-
  We'll get into more systematic and powerful techniques for reasoning
  about Imp programs in the next chapter, but we can
  already do a few things (albeit in a somewhat low-level way) just by
  working with the bare definitions. This section explores some examples.
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
-- EX3? (XtimesYinZ_spec)
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
   There are trade-offs between using tactics and additional lemmas. Here is
   a case where a lemma would make things clearer. For `loop_never_stops`,
   the surprise is that it is proved by induction, and the Rocq tactic
   `remember` is hard to understand. The following formulation explains the
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
  loops. Using `inductive`, write a property `NoWhilesR` that holds
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
  | nw_Asgn (x : Ident) (a : Aexp) : NoWhilesR (.asgn x a)
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
  mwhicks1: NOT PORTED YET — remaining sections of sfdev/lf/Imp.v to port:
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
-/
