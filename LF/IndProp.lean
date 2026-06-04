-- IndProp: Inductively Defined Propositions

/- INSTRUCTORS: In one 80-minute lecture, I (BCP) was able to get
   _to_, but not _through_, the proof of in_re_match in the regexp
   case study.  I covered the rest in an hour, going pretty slowly and
   working lots of examples in real time.  That left 20 minutes to
   show them just the first half of the ProofObjects chapter.

   Making time for at least a bit of discussion of ProofObjects is
   pretty important, even if you don't go into it in detail.  Entirely
   skipping this material leads to needless confusion and beating
   around the bush in later discussions. -/

/- HIDE: BCP 25: After teaching the chapter this semester, I feel
   that (a) the ev example, while arguably suboptimal, actually works
   acceptably well. (I just wish that the n in `ev_SS n H` was not
   two smaller than the n that is being shown to be even -- that's
   always awkward.  Wonder if there is some clever way around that...)

   However, (b) the chapter is very long, and quite a few of the
   exercises are hard, especially if you do as I did this year and
   require the advanced exercises for everybody (on the assumption
   that they could get plenty of help from LLMs, etc.).  I think it
   really needs to be at least significantly trimmed, if not split up. -/

/- HIDE: MRC 3/22: I offer a few remarks. I'm putting them here, above
   the BCP'21 comment, not to say that they are in any way more
   important; rather, just to preserve some chronological legibility.

   - This chapter is an outlier in length. It now has the maximum line
     length (in the FULL version) of any chapter in LF, at about 2300
     LoC. That's a z-score of about 1.75 for the "blue arrow" chapters
     in the dependency diagram.

   - This chapter has 39 exercises, of which 25 (!) are optional.

   - The running example of evenness is known to be uncompelling
     because it is representable without inductively-defined
     propositions. There do exist compelling examples:

     + Functions like `factorial` whose "natural" definitions are not
       structurally recursive. [Coq'Art 8.4]  [BCP 25: FWIW, I don't
       find the "natural" definition of factorial suitable for present
       purposes: the reasons it is better and more natural than a
       simple fixpoint seem rather subtle.]

     + Partial functions.

     + Relations (that are not strictly functions).

   I have a couple of personal opinions based on those observations:

   - I favor BCP'21's "path 1" of de-emphasizing (to the extent
     perhaps of eliminating) evenness.

   - I favor re-factoring this chapter into two files, with a main
     (blue) path that covers the essentials without cluttering
     optional exercises throughout the file. -/

/- HIDE: BCP '21: This chapter has been the subject of a lot of
   discussion over the past couple of years, with lots of people
   expressing dissatisfaction with the use of evenness as a main
   example.  In this revision, I have attempted a compromise: keeping
   evenness as the running example (because, aside from the
   artificiality of the example, it is pretty well polished) but
   preceding it with short discussions of several better-motivated
   examples.

   I'm not yet convinced that this goes far enough, though (I was not
   satisfied with my lecture on this part of the chapter, even after
   adding these examples, though I did do some further streamlining
   afterward and there are some further opportunities for
   streamlining -- perhaps enough to make the present treatment
   palatible).  I see three possible paths forward:
     - 1) Choose a better example and simply replace all the even
       stuff.  (But which one is better?  I don't think we've found it
       yet.)
     - 2) Mix and match -- use different examples from the top of the
       chapter to make different points.
     - 3) Leave the examples as-is but streamline as much as possible
       so we don't get stuck in them.

   Here, for reference, is the whole discussion from before:

       -----------------

       CH: In my Lyon course it became obvious to pretty much everyone
       that the inductive definition of evenness that this chapter uses
       intensiviely is so silly and artificial that it makes
       understanding very hard for most students. There's zero need to
       define evenness inductively, when `∃ k, n = 2*k` does the job
       fine, so inductive propositions seem to students not something
       useful, but just self-inflicted pain. All the inductive
       propositions, up to subsequences and the matching on Regular
       Expressions at the end, have this useless self-inflicted pain
       flavour. So I returned to this the following morning and showed
       to the students how to define reflexive-transitive closure as an
       inductive relation, and afterwards the were able to follow much
       better.  The code I quickly hacked up for this is at:
       https://prosecco.gforge.inria.fr/personal/hritcu/teaching/lyon2019/Multi.v

       BCP: Yes, this chapter needs a revamp!  For the moment I am
       going to just add a couple of sentences to the opening sequence
       below, to warn students about this potential confusion.  Moving
       forward, I wonder whether something like ordered binary trees
       would be a simple enough running example.

       BCP 20: I remain puzzled by what is the really right example for
       this chapter.  Ordered trees (and sorted lists) don't feel quite
       right because students might think we should define them with
       Fixpoint, not Inductive.  APT 21: Ordered trees are also
       surprisingly complex to describe (see VFA/SearchTree.v). Maybe
       Permutations would be be a good choice?  The only problem is
       convincing students that the standard Lean inductive definition
       is actually correct (see VFA/Perm.v)!

       We should also think about how to make the material flow better
       between this chapter and ProofObjects.  When lecturing about
       this one I ended up introducing a lot of the concepts from that
       one.

       --------

       LATER: BCP 19: After lecturing on the first part of this
       chapter, I'm afraid I have to agree that the ev / even / evenb
       stuff is a total mess.  Besides the "why are there so many
       definitions of evenness?" problem, evenness is just not a very
       natural inductively defined proposition as a first example,
       because we already have so many intuitions about what evenness
       is, and they clash with the new definition.

       So what to do?

       An early version of this chapter, years ago, used a completely
       artificial inductively defined property of numbers (0 is
       beautiful, twice a beautiful number is beautiful, etc.).  We
       could consider going back to that.  Or perhaps there is a more
       natural example, either involving numbers or perhaps using some
       other inductive structure like lists or binary trees.  Not sure
       what's best.

       A related issue is that later chapters (ProofObjects,
       IndPrinciples) also rely heavily on this example.  Sigh.

       BCP 20: Tried to sort this out a bit better by renaming the
       propositional definition from `ev` to `eveni`, for symmetry with
       `evenb`, and renaming the definition that says "a number is
       even if it is twice something" to `evend`.  What do people think
       of this?

       BCP 20 update: In parallel, APT tried to sort it out a different
       way; his is more consistent with the standard library, so let's
       try to go with that one consistently... -/

/- SOONER: This chapter needs more (and better!) quizzes -/

/- LATER: BCP 19: The following suggestion seems interesting.

  Robert Rand:

  I had an interesting experience in my most recent class which
  covered the IndProp (skipping over Regular Expressions and stuff we
  already know.)

  When we were walking through the attempted first proof of evSS_ev (I
  use WORKINCLASS quite a bit more than the book does), I had to
  explain how `destruct` is dumb in that it does case analysis while
  ignoring details of the hypothesis. To be precise, in the first case
  it doesn't notice that `ev_0` is not a constructor for any
  `ev (S (S n))`, and in the second, it throws away `S (S n)`.

  Immediately a student asked: Can we use `eqn` to tell it not to
  throw away that information?

  So we tried `eqn:E` and saw that it didn't save the information we
  cared about.

  The student followed up with: Can we use eqn on `S (S n)` itself?

  At that point I caved and introduced `remember` (actually,
  `destruct (S (S n)) eqn:E'` would have worked, but it's
  unnecessarily messy) and the class produced the following proof:

    Theorem evSS_ev : forall n,
      ev (S (S n)) -> ev n.
    Proof.
      intros n E.
      remember (S (S n)) as m.
      destruct E.
      - discriminate Heqm.
      - injection Heqm as E'.
        rewrite <- E'.
        apply E.
    Qed.

  I thought this was really nice as it helps spell out what
  `inversion` is doing behind the scenes, and I've always found
  inversion itself kind of hard to understand. It's also convenient in
  that `remember` is introduced in the same chapter in (from my
  perspective) a somewhat more awkward position.

  Thoughts on moving `remember` up and using it to introduce
  inversion?

  __________________

  from wldhx:

  Agree. My class has generally been keen on small essentials of
  tactics (revert, assert) and finding them on their own, especially
  after they found eqn sometimes breaks / is unwieldy; they also much
  like having clear and composable mental models of tactics.

  Most of them were already familiar with set by the time of IndProp,
  so we talked through inversion in terms of it, and remember was like
  a nice bonus. Moving it up does sound like a more consistent
  narrative though. -/

-- HIDEFROMHTML
import LF.Logic
-- /HIDEFROMHTML

-- ######################################################################
-- * Inductively Defined Propositions

/- In the Logic chapter, we looked at several ways of writing
   propositions, including conjunction, disjunction, and existential
   quantification.

   In this chapter, we bring yet another new tool into the mix:
   _inductively defined propositions_.

   To begin, some examples... -/

-- ##############################################
-- ** Example: The Collatz Conjecture

/- The _Collatz Conjecture_ is a famous open problem in number theory.

   Its statement is quite simple.  First, we define a function `csf`
   on numbers, as follows (where `csf` stands for "Collatz step
   function"): -/

def div2 (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => div2 n' + 1

def csf (n : Nat) : Nat :=
  if even n then div2 n
  else (3 * n) + 1

/- HIDE: CH: This is now called `csf` and not just `f` for a good
   reason. If one adds single letter global identifiers that badly
   interferes with inadvertently reusing the same names in pattern
   matching patterns, leading to confusing error messages from Lean. -/

/- TERSE: *** -/

/- Next, we look at what happens when we repeatedly apply `csf` to
   some given starting number.  For example, `csf 12` is `6`, and
   `csf 6` is `3`, so by repeatedly applying `csf` we get the
   sequence `12, 6, 3, 10, 5, 16, 8, 4, 2, 1`.

   Similarly, if we start with `19`, we get the longer sequence `19,
   58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
   4, 2, 1`.

   Both of these sequences eventually reach `1`.  The question posed
   by Collatz was: Is the sequence starting from _any_ positive
   natural number guaranteed to reach `1` eventually? -/

/- To formalize this question in Lean, we might try to define a
   recursive _function_ that calculates the total number of steps
   that it takes for such a sequence to reach `1`.  You can write
   this definition in a standard programming language, but it is
   rejected by Lean's termination checker, since the argument to
   the recursive call, `csf n`, is not "obviously smaller" than `n`. -/

/--
error: fail to show termination for
  reaches1_in
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    reaches1_in (csf n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 1) = true
⊢ csf n < n
-/
#guard_msgs in
def reaches1_in (n : Nat) : Nat :=
  if n == 1 then 0
  else 1 + reaches1_in (csf n)

/-
   You can write this definition in a standard programming language.
   This definition is, however, rejected by Lean's termination
   checker, since the argument to the recursive call, `csf n`, is not
   "obviously smaller" than `n`.
   Indeed, this isn't just a pointless limitation: functions in Lean
   are required to be total, to ensure logical consistency.

   Moreover, we can't fix it by devising a more clever termination
   checker: deciding whether this particular function is total
   would be equivalent to settling the Collatz conjecture! -/

/- TERSE: *** -/

/- Another idea could be to express the concept "eventually reaches
   `1` in the Collatz sequence" as a _recursively defined property_
   of numbers `CollatzHoldsFor : Nat → Prop`.  This is also rejected:
   while we could in principle convince Lean that `div2 n` is
   smaller than `n`, we certainly can't convince it that
   `(3 * n) + 1` is smaller than `n`! -/

/--
error: fail to show termination for
  collatz_holds_for
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    collatz_holds_for (div2 n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n x✝ : Nat
h✝ : even n = true
⊢ div2 n < x✝
-/
#guard_msgs in
def collatz_holds_for (n : Nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then collatz_holds_for (div2 n)
                   else collatz_holds_for ((3 * n) + 1)

/-- This recursive function is also rejected by the termination
    checker, since, while we could in principle convince Lean that
    `div2 n` is smaller than `n`, we certainly can't convince it that
    `(3 * n) + 1` is smaller than `n`! -/

/- TERSE: *** -/

/- Fortunately, there is another way to do it: We can express the
   concept "reaches `1` eventually in the Collatz sequence" as an
   _inductively defined property_ of numbers. Intuitively, this
   property is defined by a set of rules:

                       ─────────────────── (chf_one)
                       CollatzHoldsFor 1

         even n = true     CollatzHoldsFor (div2 n)
         ─────────────────────────────────────────── (chf_even)
                        CollatzHoldsFor n

         even n = false    CollatzHoldsFor ((3 * n) + 1)
         ─────────────────────────────────────────────── (chf_odd)
                        CollatzHoldsFor n

   So there are three ways to prove that a number `n` eventually
   reaches `1` in the Collatz sequence:
     - `n` is `1`;
     - `n` is even and `div2 n` eventually reaches `1`;
     - `n` is odd and `(3 * n) + 1` eventually reaches `1`. -/

/- TERSE: *** -/

/- We can prove that a number reaches `1` by constructing a (finite)
   derivation using these rules. For instance, here is the
   derivation proving that `12` reaches `1` (where we leave out the
   evenness/oddness premises):

                    ─────────────────────── (chf_one)
                    CollatzHoldsFor 1
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 2
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 4
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 8
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 16
                    ─────────────────────── (chf_odd)
                    CollatzHoldsFor 5
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 10
                    ─────────────────────── (chf_odd)
                    CollatzHoldsFor 3
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 6
                    ─────────────────────── (chf_even)
                    CollatzHoldsFor 12 -/

/- TERSE: *** -/

/- Formally in Lean, the `CollatzHoldsFor` property is
   _inductively defined_: -/

inductive CollatzHoldsFor : Nat → Prop where
  | chf_one  : CollatzHoldsFor 1
  | chf_even (n : Nat) : even n = true →
                         CollatzHoldsFor (div2 n) →
                         CollatzHoldsFor n
  | chf_odd  (n : Nat) : even n = false →
                         CollatzHoldsFor ((3 * n) + 1) →
                         CollatzHoldsFor n

/- FULL: What we've done here is to use Lean's `inductive`
   definition mechanism to characterize the property "Collatz holds
   for..." by stating three different ways in which it can hold:
   (1) Collatz holds for `1`, (2) if Collatz holds for `div2 n` and
   `n` is even then Collatz holds for `n`, and (3) if Collatz holds
   for `(3 * n) + 1` and `n` is odd then Collatz holds for `n`.
   This Lean definition directly corresponds to the three rules we
   wrote informally above. -/

/- TERSE: *** -/

/- LATER: BCP 23: Maybe better to postpone / suppress these
   examples? Dunno. -/

/- For particular numbers, we can now prove that the Collatz
   sequence reaches `1` (we'll look more closely at how it works a
   bit later in the chapter).  Each step applies a rule and
   discharges the boolean evenness premise by `rfl`; the recursive
   premise is then reduced by the kernel from
   `CollatzHoldsFor (div2 12)` to `CollatzHoldsFor 6`, etc. -/

example : CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_odd;   rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_odd;   rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  apply CollatzHoldsFor.chf_even;  rfl
  exact CollatzHoldsFor.chf_one

-- HIDE
/- Here is a more compact definition that seems better for proofs,
   but requires more mental unfolding for getting intuition,
   illustrates less about inductive definitions, and also informal
   derivations look less informative.

   The way to read this one is: "The number `1` reaches `1`, and
   any number `n` reaches `1` if `csf n` does." -/

inductive Reaches1 : Nat → Prop where
  | reach_done : Reaches1 1
  | reach_more (n : Nat) : Reaches1 (csf n) → Reaches1 n

/- Alternatively, we can define the partial function
   `Collatz_holds_for_in` as a two-argument inductive relation... -/

inductive ChfIn : Nat → Nat → Prop where
  | tst_done : ChfIn 1 0
  | tst_more (n k : Nat) : ChfIn (csf n) k → ChfIn n (k + 1)

/- ... and then say that `n` reaches `1` if there is some `k` such
   that the sequence beginning at `n` reaches `1` in `k` total
   steps. -/

def CollatzHoldsFor' (n : Nat) : Prop := ∃ k, ChfIn n k
-- /HIDE

/- TERSE: *** -/

/- The Collatz conjecture then states that the sequence beginning
   from _any_ positive number reaches `1`: -/

def collatz := ∀ n, n ≠ 0 → CollatzHoldsFor n

/- If you succeed in proving this conjecture, you've got a bright
   future as a number theorist!  But don't spend too long on it --
   it's been open since 1937. -/

/- HIDE: CH: We may want to add an exercise later proving false if
   one assumes Collatz' conjecture without the `n ≠ 0` assumption.
   We had that mistake in the script for years and no one noticed,
   wow! -/

-- ##############################################
-- ** Example: Binary relation for comparing numbers

/- A binary _relation_ on a set `α` has Lean type `α → α → Prop`.
   This is a family of propositions parameterized by two elements
   of `α` -- i.e., a proposition about pairs of elements of `α`. -/

/- For example, one familiar binary relation on `Nat` is `Le : Nat
   → Nat → Prop`, the less-than-or-equal-to relation, which can be
   inductively defined by the following two rules:

                            ─────── (le_n)
                            Le n n

                             Le n m
                          ───────────── (le_s)
                          Le n (m + 1) -/

/- FULL: These rules say that there are two ways to show that a
   number is less than or equal to another: either observe that
   they are the same number, or, if the second has the form
   `m + 1`, give evidence that the first is less than or equal to
   `m`. -/

-- HIDEFROMHTML
namespace LePlayground
-- /HIDEFROMHTML

inductive Le : Nat → Nat → Prop where
  | le_n (n : Nat)              : Le n n
  | le_s (n m : Nat) : Le n m → Le n (m + 1)

infix:50 " ⊑ " => Le

/- FULL: This definition is a bit simpler and more elegant than the
   Boolean function `leb` we defined in `Basics`.  As usual, `Le`
   and `leb` are equivalent, and there is an exercise about that
   later. -/

example : 3 ⊑ 5 := by
  apply Le.le_s; apply Le.le_s; exact Le.le_n 3

-- HIDEFROMHTML
end LePlayground
-- /HIDEFROMHTML

-- ##############################################
/- ** Example: Transitive Closure -/

/- Another example: The _reflexive and transitive closure_ of a
    relation [R] is the smallest relation that contains [R] and that
    is reflexive and transitive. This can be defined by the following
    three rules (where we added a reflexivity rule to [ClosTrans]):
[[[
                     R x y
                ---------------- (t_step)
                ClosTrans R x y

       ClosTrans R x y    ClosTrans R y z
       ------------------------------------ (t_trans)
                ClosTrans R x z
]]]

    In Lean this looks as follows:
-/

inductive ClosTrans {α: Type} (R: α->α->Prop) : α → α → Prop where
  | t_step (x y : α) :
      R x y ->
      ClosTrans R x y
  | t_trans (x y z : α) :
      ClosTrans R x y ->
      ClosTrans R y z ->
      ClosTrans R x z

-- TERSE:

/- For example, suppose we define a "parent of" relation on a group
    of people... -/

inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person -> Person -> Prop where
  | po_SC : ParentOf .sage .cleo
  | po_SR : ParentOf .sage .ridley
  | po_CM : ParentOf .cleo .moss

/- FULL: In this example, `sage` is a parent of both `cleo` and
    `ridley`; and `cleo` is a parent of `moss`. -/

/- The [parent_of] relation is not transitive, but we can define
   an "ancestor of" relation as its transitive closure: -/

def AncestorOf : Person -> Person -> Prop := ClosTrans ParentOf


/- Here is a derivation showing that Sage is an ancestor of Moss:
[[

 ———————————————————(po_SC)     ———————————————————(po_CM)
 ParentOf .sage .cleo            ParentOf .cleo .moss
—————————————————————(t_step)  —————————————————————(t_step)
AncestorOf .sage .cleo          AncestorOf .cleo .moss
————————————————————————————————————————————————————(t_trans)
                AncestorOf .sage .moss
]]
-/

-- TERSE: HIDEFROMHTML
example : AncestorOf .sage .moss := by
  apply ClosTrans.t_trans
  . apply ClosTrans.t_step; apply ParentOf.po_SC
  . apply ClosTrans.t_step; apply ParentOf.po_CM
-- TERSE: /HIDEFROMHTML

/- HIDE: CH: A simple exercise could be nice here? -/

/- FULL: Computing the transitive closure can be undecidable even for
    a relation R that is decidable (e.g., the `cms` relation below), so in
    general we can't expect to define transitive closure as a boolean
    function. Fortunately, Lean allows us to define transitive closure
    as an inductive relation.

    The transitive closure of a binary relation cannot, in general, be
    expressed in first-order logic. The logic of Lean is, however, much
    more powerful, and can easily define such inductive relations. -/

-- ##############################################
-- ** Example: Reflexive and Transitive Closure

/- As another example, the _reflexive and transitive closure_
    of a relation `R` is the
    smallest relation that contains `R` and that is reflexive and
    transitive. This can be defined by the following three rules
    (where we added a reflexivity rule to `ClosTrans`):
[[[
                        R x y
                --------------------- (rt_step)
                ClosReflTrans R x y

                --------------------- (rt_refl)
                ClosReflTrans R x x

        ClosReflTrans R x y    ClosReflTrans R y z
     ---------------------------------------------- (rt_trans)
                ClosReflTrans R x z
]]]
-/

-- TERSE: HIDEFROMHTML
inductive ClosReflTrans {α: Type} (R: α -> α -> Prop) : α -> α -> Prop where
  | rt_step (x y : α) :
      R x y ->
      ClosReflTrans R x y
  | rt_refl (x : α) :
      ClosReflTrans R x x
  | rt_trans (x y z : α) :
      ClosReflTrans R x y ->
      ClosReflTrans R y z ->
      ClosReflTrans R x z
-- TERSE: /HIDEFROMHTML


-- TERSE: ***

/- For instance, this enables an equivalent definition of the Collatz
    conjecture.  First we define a binary relation corresponding to
    the "Collatz step function" `csf`: -/

def cs (n m : Nat) : Prop := csf n = m

/- This Collatz step relation can be used in conjunction with the
    reflexive and transitive closure operation to define a _Collatz
    multi-step_ (`cms`) relation, expressing that a number `n`
    reaches another number `m` in zero or more Collatz steps: -/

def cms (n m : Nat) : Prop := ClosReflTrans cs n m
def collatz' : Prop := forall (n : Nat), n ≠ 0 -> cms n 1


/- FULL: This `cms` relation defined in terms of
    `ClosReflTrans` allows for more interesting derivations than the
    linear ones of the directly-defined `CollatzHoldsFor` relation:
[[

csf 16 = 8         csf 8 = 4         csf 4 = 2         csf 2 = 1
————————(rt_step)  ———————(rt_step)  ———————(rt_step)  ———————(rt_step)
cms 16 8           cms 8 4           cms 4 2           cms 2 1
—————————————————————————(rt_trans)  ————————————————————————(rt_trans)
        cms 16 4                              cms 4 1
        —————————————————————————————————————————————(rt_trans)
                           cms 16 1
]]
-/

/- HIDE: CH: Would it be helpful to add an exercise later proving cms
   equivalent to CollatzHoldsFor -/

/- FULL -/
/- EX1M? (clos_refl_trans_sym) -/
/- How would you modify the [ClosReflTrans] definition above so as
    to define the reflexive, symmetric, and transitive closure? -/

-- SOLUTION
inductive ClosReflTransSym {α: Type} (R: α->α->Prop) : α->α->Prop where
  | srt_refl (x : α) :
      ClosReflTransSym R x x
  | srt_step (x y : α) :
      R x y ->
      ClosReflTransSym R x y
  | srt_sym (x y : α) :
      ClosReflTransSym R y x ->
      ClosReflTransSym R x y
  | srt_trans (x y z : α) :
      ClosReflTransSym R x y ->
      ClosReflTransSym R y z ->
      ClosReflTransSym R x z
-- /SOLUTION
-- []
-- /FULL


-- ##############################################
/- Example: Permutations -/

/- The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements.

    We can define such permulations by the following rules:
[[[
               --------------------- (perm3_swap12)
               Perm3 [a;b;c] [b;a;c]

               --------------------- (perm3_swap23)
               Perm3 [a;b;c] [a;c;b]

            Perm3 l1 l2       Perm3 l2 l3
            ----------------------------- (perm3_trans)
                     Perm3 l1 l3
]]]
    For instance we can derive [Perm3 [1;2;3] [3;2;1]] as follows:
[[
    ————————(perm_swap12)  —————————————————————(perm_swap23)
    Perm3 [1;2;3] [2;1;3]  Perm3 [2;1;3] [2;3;1]
    ——————————————————————————————(perm_trans)  ————————————(perm_swap12)
        Perm3 [1;2;3] [2;3;1]                   Perm [2;3;1] [3;2;1]
        —————————————————————————————————————————————————————(perm_trans)
                          Perm3 [1;2;3] [3;2;1]
]]
-/

/- FULL: This definition says:
      - If `l2` can be obtained from `l1` by swapping the first and
        second elements, then `l2` is a permutation of `l1`.
      - If `l2` can be obtained from `l1` by swapping the second and
        third elements, then `l2` is a permutation of `l1`.
      - If `l2` is a permutation of `l1` and `l3` is a permutation of
        `l2`, then `l3` is a permutation of `l1`. -/

-- TERSE: ***

/- In Lean, we can define `Perm3` as follows: -/

inductive Perm3 {α : Type} : List α -> List α -> Prop where
  | perm3_swap12 (a b c : α) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : α) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l1 l2 l3 : List α) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3


-- FULL
-- EX1M? (perm)
/- According to this definition, is [[1;2;3]] a permutation of
    itself? -/

-- SOLUTION
/- Yes! Just apply `perm3_swap12` twice (or `perm3_swap23` twice). -/
-- /SOLUTION
-- []
-- /FULL

-- ##############################################
/- ** Example: Evenness (yet again) -/

/- We've already seen two ways of stating a proposition that a number
    `n` is even: We can say

      (1) `even n = true` (using the recursive boolean function `even`), or

      (2) `exists k, n = double k` (using an existential quantifier). -/

-- TERSE: ***

/- A third possibility, which we'll use as a simple running example
    in this chapter, is to say that a number is even if we can
    _establish_ its evenness from the following two rules:
[[[
                          ---- (ev_0)
                          ev 0

                          ev n
                      ------------ (ev_succ_succ)
                      ev ((n + 1) + 1)
]]]
-/

/- FULL: Intuitively these rules say that:
       - The number `0` is even.
       - If `n` is even, then `(n + 1) + 1` is even. -/

/- FULL: (Defining evenness in this way may seem a bit confusing,
    since we have already seen two perfectly good ways of doing
    it. It makes a convenient running example because it is
    simple and compact, but we will soon return to the more compelling
    examples above.) -/

/- To illustrate how this new definition of evenness works, let's
    imagine using it to show that [4] is even:
[[
                           ———— (ev_0)
                           ev 0
                       ———————————— (ev_SS)
                       ev (S (S 0))
                   ———————————————————— (ev_SS)
                   ev (S (S (S (S 0))))
]]
-/

/- FULL: In words, to show that `4` is even, by rule `ev_succ_succ`, it
   suffices to show that `2` is even. This, in turn, is again
   guaranteed by rule `ev_succ_succ`, as long as we can show that `0` is
   even. But this last fact follows directly from the `ev_0` rule. -/

-- TERSE: ***

/- We can translate the informal definition of evenness from above
    into a formal `inductive` declaration, where each "way that a
    number can be even" corresponds to a separate constructor: -/

inductive Ev : Nat -> Prop where
  | ev_0                       : Ev 0
  | ev_succ_succ (n : Nat) (H : Ev n) : Ev ((n + 1) + 1)


/- TERSE: There are both similarities and a few differences between
    inductive _properties_ like `Ev` and the inductive _types_ like
    `Nat` or `List` that we have been using throughout the course:
[[
    inductive list (α:Type) : Type where
      | nil                       : list α
      | cons (x : α) (l : list α) : list α.
]]]
    The most important difference is that the constructors of `Ev`,
    `ev_0` and `ev_succ_succ`, yield different types (`Ev 0` and `Ev ((n + 1) + 1)`),
    whereas the `List` constructors both build `List α` values. -/

-- FULL
/- Such definitions are interestingly different from previous uses of
    `inductive` for defining inductive datatypes like `Nat` or `List`.
    For one thing, we are defining not a [Type] (like `Nat`) or a
    function yielding a `Type` (like `List`), but rather a function
    from `Nat` to `Prop` -- that is, a property of numbers. But what
    is really new is that, because the `Nat` argument of `Ev` appears
    to the _right_ of the colon on the first line, it is allowed to
    take _different_ values in the types of different constructors:
    `0` in the type of `ev_0` and `((n + 1) + 1)` in the type of `ev_succ_succ`.
    Accordingly, the type of each constructor must be specified
    explicitly (after a colon), and each constructor's type must have
    the form `Ev n` for some natural number `n`.

    In contrast, recall the definition of `List`:
[[
    inductive List (α:Type) : Type where
      | nil
      | cons (x : α) (l : List α)
]]
    or (equivalently but more explicitly):
[[
    inductive List (α:Type) : Type where
      | nil                       : List α
      | cons (x : α) (l : List α) : List α
]]
   This definition introduces the `α` parameter _globally_, to the
   _left_ of the colon, forcing the result of `nil` and `cons` to be
   the same type (i.e., `List α`).  But if we had tried to bring `Nat`
   to the left of the colon in defining `Ev`, we would have seen an
   error: -/

/--
error: Mismatched inductive type parameter in
  WrongEv 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive WrongEv (n : Nat) : Prop where
  | wrong_ev_0 : WrongEv 0
  | wrong_ev_SS (H: WrongEv n) : WrongEv ((n + 1) + 1)


/- In an `inductive` definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in `inductive List (α : Type) := ...`, the `α` is a
    parameter, while in `inductive Ev : nat -> Prop := ...`, the
    unnamed `Nat` argument is an index. -/
-- /FULL

-- TERSE: ***

/- We can think of the inductive definition of `Ev` as defining a
    Lean property `Ev : nat -> Prop`, together with two "evidence
    constructors": -/

#check (Ev.ev_0) -- Ev 0
#check Ev.ev_succ_succ -- forall (n : Nat) (H : Ev n) : Ev ((n + 1) + 1)

-- FULL
/- Indeed, Lean also accepts the following equivalent definition of `Ev` -/

namespace EvPlayground

inductive Ev : Nat -> Prop where
  | ev_0  : Ev 0
  | ev_SS : forall (n : Nat), Ev n -> Ev ((n + 1) + 1)

end EvPlayground
-- /FULL

-- TERSE: ***
/- These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used later on just like proven
    theorems.  In particular, we can use Lean's `apply` and `exact` tactics with the
    constructor names to obtain evidence for `Ev` of particular
    numbers... -/

theorem ev_4 : Ev 4 := by
  apply Ev.ev_succ_succ; apply Ev.ev_succ_succ; exact Ev.ev_0

/- ... or we can use function application syntax to combine several
    constructors: -/

theorem ev_4' : Ev 4 := by
  exact Ev.ev_succ_succ 2 (Ev.ev_succ_succ 0 Ev.ev_0)

/- In this way, we can also prove theorems that have hypotheses
    involving `Ev`. -/

theorem ev_plus4 : forall n, Ev n -> Ev (4 + n) := by
  intro n Hn
  rw [Nat.add_comm]
  exact (Ev.ev_succ_succ _ (Ev.ev_succ_succ _ Hn))

-- FULL
-- EX1 (ev_double)
theorem ev_double : forall n, Ev (double n) := by
  -- ADMITTED
  intros n; induction n
  case zero =>
    rw [double_zero]; exact Ev.ev_0
  case succ n IH =>
    rw [double_succ]; exact Ev.ev_succ_succ _ IH
  -- /ADMITTED
-- []
-- /FULL

-- ** Constructing Evidence for Permutations

/- Similarly we can apply the evidence constructors to obtain
    evidence of `Perm3 [1, 2, 3] [3, 2, 1]`: -/

theorem Perm3_rev : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply Perm3.perm3_trans (l2:= [2, 3, 1])
  . apply Perm3.perm3_trans (l2:=[2, 1, 3])
    . apply Perm3.perm3_swap12
    . apply Perm3.perm3_swap23
  . apply Perm3.perm3_swap12

-- TERSE: ***
/- And again we can equivalently use function application syntax to
    combine several constructors. (Note that the Lean type checker can
    infer not only types, but also Nats and List, when they are clear
    from the context.) -/

theorem Perm3_rev' : Perm3 [1, 2, 3] [3, 2, 1] := by
  exact (Perm3.perm3_trans _ [2, 3, 1] _
          (Perm3.perm3_trans _ [2, 1, 3] _
            (Perm3.perm3_swap12 _ _ _)
            (Perm3.perm3_swap23 _ _ _))
          (Perm3.perm3_swap12 _ _ _))

/--/ So the informal derivation trees we drew above are not too far
    from what's happening formally.  Formally we're using the evidence
    constructors to build _evidence trees_, similar to the finite trees we
    built using the constructors of data types such as nat, list,
    binary trees, etc. -/

-- FULL
-- EX1 (Perm3)
theorem Perm3_ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  -- ADMITTED
  apply Perm3.perm3_trans (l2 := [2, 1, 3])
  . apply Perm3.perm3_swap12
  . apply Perm3.perm3_swap23
  -- /ADMITTED

theorem Perm3_refl : forall (α : Type) (a b c : α ), Perm3 [a, b, c] [a, b, c] := by
  -- ADMITTED
  intro α a b c
  apply Perm3.perm3_trans (l2:=[b, a, c])
  . apply Perm3.perm3_swap12
  . apply Perm3.perm3_swap12
-- /ADMITTED
-- GRADE_THEOREM 0.5: Perm3_ex1
-- GRADE_THEOREM 0.5: Perm3_refl
-- []
-- /FULL


-- #######################################################
-- * Using Evidence in Proofs

/- Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Defining `Ev` with an `inductive` declaration tells Rocq not
    only that the constructors `ev_0` and `ev_succ_succ` are valid ways to
    build evidence that some number is `Ev`, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are `Ev`. -/

/- TERSE: *** -/
/- In other words, if someone gives us evidence `E` for the proposition
    `ev n`, then we know that `E` must be one of two things:

      - `E = ev_0` and `n = O`, or
      - `E = ev_succ_succ n' E'` and `n = n' + 2)`, where `E'` is
        evidence for `ev n'`. -/

/- FULL: This suggests that it should be possible to analyze a
    hypothesis of the form `ev n` much as we do inductively defined
    data structures; in particular, it should be possible to argue either by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. -/
/- TERSE: This suggests that it should be possible to do _case
    analysis_ and even _induction_ on evidence of evenness... -/

/- ** Destructing and Inverting Evidence -/

/- FULL: Suppose we are proving some fact involving a number `n`, and
    we are given `ev n` as a hypothesis.  We already know how to
    perform case analysis on `n` using `cases` or `induction`,
    generating separate subgoals for the case where `n = O` and the
    case where `n = S n'` for some `n'`.  But for some proofs we may
    instead want to analyze the evidence for `ev n` _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of `ev n`, using
    `cases`. -/

/- TERSE: We can prove our characterization of evidence for `ev n`,
    using `cases`. -/

theorem ev_inversion : forall (n : Nat),
    Ev n ->
    (n = 0) ∨ exists n', n = n' + 2 ∧ Ev n' := by
    intro n H
    cases H
    case ev_0 =>
      left; rfl
    case ev_succ_succ n H =>
      right; exists n

/- Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived. -/
/- FULL: Here there are two ways to prove `Ev n`, and the inversion
    lemma makes this explicit. -/

-- FULL
-- EX1 (le_inversion)
-- Let's prove a similar inversion lemma for [le].
namespace LePlayground
theorem le_inversion : forall (n m : Nat),
  Le n m ->
  (n = m) ∨ (exists m', m = m' + 1 ∧ Le n m') := by
  /- ADMITTED -/
  intros n m E
  cases E
  case le_n => left; rfl
  case le_s m H => right; exists m
/- /ADMITTED -/
/-* [] -/
end LePlayground
/- /FULL -/
