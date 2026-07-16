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
   that (a) the Ev example, while arguably suboptimal, actually works
   acceptably well. (I just wish that the n in ``ev_succ_succ` n H` was not
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
       Fixpoint, not inductive.  APT 21: Ordered trees are also
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
       chapter, I'm afraid I have to agree that the Ev / even / evenb
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
       propositional definition from `Ev` to `eveni`, for symmetry with
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
  `Ev (S (S n))`, and in the second, it throws away `S (S n)`.

  Immediately a student asked: Can we use `eqn` to tell it not to
  throw away that information?

  So we tried `eqn:E` and saw that it didn't save the information we
  cared about.

  The student followed up with: Can we use eqn on `S (S n)` itself?

  At that point I caved and introduced `remember` (actually,
  `destruct (S (S n)) eqn:E'` would have worked, but it's
  unnecessarily messy) and the class produced the following proof:

    theorem evSS_ev : forall n,
      Ev (S (S n)) → Ev n.
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
import LF.CustomTactics
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

/- This recursive function is also rejected by the termination
    checker, since, while we could in principle convince Lean that
    `div2 n` is smaller than `n`, we certainly can't convince it that
    `(3 * n) + 1` is smaller than `n`! -/

/- TERSE: *** -/

/- Fortunately, there is another way to do it: We can express the
   concept "reaches `1` eventually in the Collatz sequence" as an
   _inductively defined property_ of numbers. Intuitively, this
   property is defined by a set of rules:
[[
                       ─────────────────── (chf_one)
                       CollatzHoldsFor 1

         even n = true     CollatzHoldsFor (div2 n)
         ─────────────────────────────────────────── (chf_even)
                        CollatzHoldsFor n

         even n = false    CollatzHoldsFor ((3 * n) + 1)
         ─────────────────────────────────────────────── (chf_odd)
                        CollatzHoldsFor n
]]
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
[[
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
                    CollatzHoldsFor 12
]]
-/

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
[[
                            ─────── (le_refl)
                            Le n n

                             Le n m
                          ───────────── (le_step)
                          Le n (m + 1)
]]
-/

/- FULL: These rules say that there are two ways to show that a
   number is less than or equal to another: either observe that
   they are the same number, or, if the second has the form
   `m + 1`, give evidence that the first is less than or equal to
   `m`. -/

-- HIDEFROMHTML
namespace LePlayground
-- /HIDEFROMHTML

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat)              : Le n n
  | step (n m : Nat) : Le n m → Le n (m + 1)

scoped infix:50 (priority := high) " ≤ " => Le

/- FULL: This definition is a bit simpler and more elegant than the
   Boolean function `ble` we defined in `Basics`.  As usual, `Le`
   and `ble` are equivalent, and there is an exercise about that
   later. -/

example : 3 ≤ 5 := by
  apply Le.step; apply Le.step; exact Le.refl 3

-- HIDEFROMHTML
end LePlayground
-- /HIDEFROMHTML

-- ##############################################
/- ## Example: Transitive Closure -/

/- Another example: The _transitive closure_ of a
    relation [R] is the smallest relation that contains [R] and that
    is transitive. This can be defined by the following
    two rules:
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

inductive ClosTrans {α: Type} (R: α→α→Prop) : α → α → Prop where
  | t_step (x y : α) :
      R x y →
      ClosTrans R x y
  | t_trans (x y z : α) :
      ClosTrans R x y →
      ClosTrans R y z →
      ClosTrans R x z

-- TERSE: ***

/- For example, suppose we define a "parent of" relation on a group
    of people... -/

inductive Person : Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf : Person → Person → Prop where
  | po_SC : ParentOf .sage .cleo
  | po_SR : ParentOf .sage .ridley
  | po_CM : ParentOf .cleo .moss

/- FULL: In this example, `sage` is a parent of both `cleo` and
    `ridley`; and `cleo` is a parent of `moss`. -/

/- The [parent_of] relation is not transitive, but we can define
   an "ancestor of" relation as its transitive closure: -/

def AncestorOf : Person → Person → Prop := ClosTrans ParentOf


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
inductive ClosReflTrans {α: Type} (R: α → α → Prop) : α → α → Prop where
  | rt_step (x y : α) :
      R x y →
      ClosReflTrans R x y
  | rt_refl (x : α) :
      ClosReflTrans R x x
  | rt_trans (x y z : α) :
      ClosReflTrans R x y →
      ClosReflTrans R y z →
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
def collatz' : Prop := ∀ (n : Nat), n ≠ 0 → cms n 1


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
inductive ClosReflTransSym {α: Type} (R: α→α→Prop) : α→α→Prop where
  | srt_refl (x : α) :
      ClosReflTransSym R x x
  | srt_step (x y : α) :
      R x y →
      ClosReflTransSym R x y
  | srt_sym (x y : α) :
      ClosReflTransSym R y x →
      ClosReflTransSym R x y
  | srt_trans (x y z : α) :
      ClosReflTransSym R x y →
      ClosReflTransSym R y z →
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

    We can define such permutations by the following rules:
[[[
               ------------------------- (perm3_swap12)
               Perm3 [a, b, c] [b, a, c]

               ------------------------- (perm3_swap23)
               Perm3 [a, b, c] [a, c, b]

            Perm3 l₁ l₂       Perm3 l₂ l₃
            ----------------------------- (perm3_trans)
                     Perm3 l₁ l₃
]]]
    For instance we can derive `Perm3 [1, 2, 3] [3, 2, 1]` as follows:
[[
    ─────────────────────────(perm3_swap12)   ─────────────────────────(perm3_swap23)
    Perm3 [1, 2, 3] [2, 1, 3]                 Perm3 [2, 1, 3] [2, 3, 1]
    ──────────────────────────────────────────────────(perm3_trans)   ─────────────────────────(perm3_swap12)
    Perm3 [1, 2, 3] [2, 3, 1]                                          Perm3 [2, 3, 1] [3, 2, 1]
    ──────────────────────────────────────────────────────────────────────────(perm3_trans)
    Perm3 [1, 2, 3] [3, 2, 1]
]]
-/

/- FULL: This definition says:
      - If `l₂` can be obtained from `l₁` by swapping the first and
        second elements, then `l₂` is a permutation of `l₁`.
      - If `l₂` can be obtained from `l₁` by swapping the second and
        third elements, then `l₂` is a permutation of `l₁`.
      - If `l₂` is a permutation of `l₁` and `l₃` is a permutation of
        `l₂`, then `l₃` is a permutation of `l₁`. -/

-- TERSE: ***

/- In Lean, we can define `Perm3` as follows: -/

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 (a b c : α) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : α) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l₁ l₂ l₃ : List α) :
      Perm3 l₁ l₂ → Perm3 l₂ l₃ → Perm3 l₁ l₃


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
/- ## Example: Evenness (yet again) -/

/- We've already seen two ways of stating a proposition that a number
    `n` is even: We can say

      (1) `even n = true` (using the recursive boolean function `even`), or

      (2) `∃ k, n = double k` (using an existential quantifier). -/

-- TERSE: ***

/- A third possibility, which we'll use as a simple running example
    in this chapter, is to say that a number is even if we can
    _establish_ its evenness from the following two rules:
[[[
                          ---- (ev_0)
                          Ev 0

                          Ev n
                      ------------ (ev_succ_succ)
                      Ev (n + 2)
]]]
-/

/- FULL: Intuitively these rules say that:
       - The number `0` is even.
       - If `n` is even, then `n + 2` is even. -/

/- FULL: (Defining evenness in this way may seem a bit confusing,
    since we have already seen two perfectly good ways of doing
    it. It makes a convenient running example because it is
    simple and compact, but we will soon return to the more compelling
    examples above.) -/

/- To illustrate how this new definition of evenness works, let's
    imagine using it to show that [4] is even:
[[
                           ———— (ev_0)
                           Ev 0
                       ———————————— (`ev_succ_succ`)
                       Ev (S (S 0))
                   ———————————————————— (`ev_succ_succ`)
                   Ev (S (S (S (S 0))))
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

inductive Ev : Nat → Prop where
  | ev_0                       : Ev 0
  | ev_succ_succ (n : Nat) (H : Ev n) : Ev (n + 2)


/- TERSE: There are both similarities and a few differences between
    inductive _properties_ like `Ev` and the inductive _types_ like
    `Nat` or `List` that we have been using throughout the course:
[[
    inductive List (α:Type) : Type where
      | nil                       : List α
      | cons (x : α) (l : List α) : List α.
]]
    The most important difference is that the constructors of `Ev`,
    `ev_0` and `ev_succ_succ`, yield different types (`Ev 0` and `Ev (n + 2)`),
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
    `0` in the type of `ev_0` and `(n + 2)` in the type of `ev_succ_succ`.
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
  | wrong_ev_succ_succ (H: WrongEv n) : WrongEv (n + 2)


/- In an `inductive` definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in `inductive List (α : Type) := ...`, the `α` is a
    parameter, while in `inductive Ev : Nat → Prop := ...`, the
    unnamed `Nat` argument is an index. -/
-- /FULL

-- TERSE: ***

/- We can think of the inductive definition of `Ev` as defining a
    Lean property `Ev : Nat → Prop`, together with two "evidence
    constructors": -/

#check (Ev.ev_0) -- Ev 0
#check Ev.ev_succ_succ -- ∀ (n : Nat) (H : Ev n) : Ev (n + 2)

-- FULL
/- Indeed, Lean also accepts the following equivalent definition of `Ev` -/

namespace EvPlayground

inductive Ev : Nat → Prop where
  | ev_0  : Ev 0
  | ev_succ_succ : ∀ (n : Nat), Ev n → Ev (n + 2)

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

/- ... or we can also use the `constructor` tactic we saw earlier to select the appropriate
   inductive constructor -/

theorem ev_4'' : Ev 4 := by
  constructor; constructor; constructor

/- In this way, we can also prove theorems that have hypotheses
    involving `Ev`. -/

theorem ev_plus4 : ∀ n, Ev n → Ev (4 + n) := by
  intro n Hn
  rw [Nat.add_comm]
  exact (Ev.ev_succ_succ _ (Ev.ev_succ_succ _ Hn))

-- FULL
-- EX1 (ev_double)
theorem ev_double : ∀ n, Ev (double n) := by
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
  apply Perm3.perm3_trans (l₂:= [2, 3, 1])
  . apply Perm3.perm3_trans (l₂:=[2, 1, 3])
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

/- So the informal derivation trees we drew above are not too far
    from what's happening formally.  Formally we're using the evidence
    constructors to build _evidence trees_, similar to the finite trees we
    built using the constructors of data types such as Nat, List,
    binary trees, etc. -/

-- FULL
-- EX1 (Perm3)
theorem Perm3_ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  -- ADMITTED
  apply Perm3.perm3_trans (l₂ := [2, 1, 3])
  . apply Perm3.perm3_swap12
  . apply Perm3.perm3_swap23
  -- /ADMITTED

theorem Perm3_refl : ∀ (α : Type) (a b c : α ), Perm3 [a, b, c] [a, b, c] := by
  -- ADMITTED
  intro α a b c
  apply Perm3.perm3_trans (l₂:=[b, a, c])
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

    Defining `Ev` with an `inductive` declaration tells Lean not
    only that the constructors `ev_0` and `ev_succ_succ` are valid ways to
    build evidence that some number is `Ev`, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are `Ev`. -/

/- TERSE: *** -/
/- In other words, if someone gives us evidence `E` for the proposition
    `Ev n`, then we know that `E` must be one of two things:

      - `E = ev_0` and `n = 0`, or
      - `E = ev_succ_succ n' E'` and `n = n' + 2`, where `E'` is
        evidence for `Ev n'`. -/

/- FULL: This suggests that it should be possible to analyze a
    hypothesis of the form `Ev n` much as we do inductively defined
    data structures; in particular, it should be possible to argue either by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. -/
/- TERSE: This suggests that it should be possible to do _case
    analysis_ and even _induction_ on evidence of evenness... -/

/- ## Destructing and Inverting Evidence -/

/- FULL: Suppose we are proving some fact involving a number `n`, and
    we are given `Ev n` as a hypothesis.  We already know how to
    perform case analysis on `n` using `cases` or `induction`,
    generating separate subgoals for the case where `n = 0` and the
    case where `n = n' + 1` for some `n'`.  But for some proofs we may
    instead want to analyze the evidence for `Ev n` _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of `Ev n`, using
    `cases`. -/

/- TERSE: We can prove our characterization of evidence for `Ev n`,
    using `cases`. -/

theorem ev_inversion : ∀ (n : Nat),
    Ev n →
    (n = 0) ∨ ∃ n', n = n' + 2 ∧ Ev n' := by
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
theorem le_inversion : ∀ (n m : Nat),
  Le n m →
  (n = m) ∨ (∃ m', m = m' + 1 ∧ Le n m') := by
  /- ADMITTED -/
  intros n m E
  cases E
  case refl => left; rfl
  case step m H => right; exists m
/- /ADMITTED -/
/- [] -/
end LePlayground
/- /FULL -/

/- HIDE -/
    /- QUIZ -/
    /- Which tactics are needed to prove this goal?
    [[
      n : Nat
      E : Ev n
      F : n = 1
      ======================
      true = false
    ]]

       (A) [cases]

       (B) [contradiction]

       (C) both [cases] and [contradiction]

       (D) These tactics are not sufficient to solve the goal. -/
    /- FOLD -/
    theorem quiz_1_not_ev : ∀ n, Ev n → n = 1 → true = false := by
      intro n E F
      cases E
      . contradiction
      . injection F; contradiction
    /- /FOLD -/
    /- /QUIZ -/
/- /HIDE -/

/- HIDE -/
   /- /-LATER: BCP 21: This part of the chapter has gotten way too dense.
       To streamline it, I am experimentally deleting the whole discussion
       from here... -/
    /- Similarly, the following theorem can easily be proved using
        `cases` on evidence. -/

    theorem ev_minus2 : forall n,
      Ev n → Ev (pred (pred n)).
    Proof.
      intros n E.  destruct E as [| n' E'] eqn:EE.
      - /-E = ev_0 -/
        simpl. apply ev_0.
      - /-E = `ev_succ_succ` n' E' -/
        simpl. apply E'.
    Qed.

    /- TERSE: *** -/
    /- However, the following simple variation shows that `cases` can
        sometimes throw away critical information: -/

    theorem evSS_ev : forall n,
      Ev (S (S n)) → Ev n.
    /- FULL: Intuitively, we know that evidence for the hypothesis cannot
        consist just of the `ev_0` constructor, since `0` and `succ` are
        different constructors of the type `Nat`; hence, `ev_succ_succ` is the
        only case that applies.  Unfortunately, `cases` is not smart
        enough to realize this, and it still generates two subgoals.  Even
        worse, in doing so, it keeps the final goal unchanged, failing to
        provide any useful information for completing the proof.  -/
    Proof.
      intros n E.  destruct E as [| n' E'] eqn:EE.
      - /-E = ev_0. -/
        /-Looks like we must prove that [n] is even... but there are no
           useful assumptions! -/
    Abort.

    /- TERSE: Tactic `cases` replaced [S (S n)] with [0] in [E],
        because that's what `ev_0` proves. -/

    /- FULL: What happened here, exactly?  Calling `cases` has the effect
        of replacing all occurrences of the property argument by the
        values that correspond to each constructor.  This is enough in the
        case of [ev_minus2] because that argument [n] is mentioned
        directly in the final goal. However, it doesn't help in the case
        of [evSS_ev] since the term that gets replaced -- [S (S n)] -- is
        not mentioned anywhere! -/

    /-LATER: BCP 21: That whole explanation is pretty thick... Could we
       streamline it?  E.g., do students really need to know all these
       details about how destruct works -- and are they likely to retain
       them anyway, from this discussion?  Maybe we could just get to
       inversion more directly.  I'm going to leave it alone for now, but
       I think it is a candidate for radical simplification. -/
    /-HIDE: MRC: I found it helpful (2/19/19) in class to introduce
       [remember] just a little early here. -/

    /- TERSE: *** -/
    /- FULL: We can fix this by [remember]ing that term [S (S n)], the
        proof goes through.  (We'll discuss [remember] in more detail
        below.) -/

    /- TERSE: So let's [remember] that term [S (S n)]. -/

    theorem evSS_ev_remember : forall n,
      Ev (S (S n)) → Ev n.
    Proof.
      intros n E. remember (S (S n)) as k eqn:Hk.
      destruct E as [|n' E'] eqn:EE.
      - /-E = ev_0 -/
        /-Now we do have an assumption, in which [k = S (S n)] has been
           rewritten as [0 = S (S n)] by `cases`. That assumption
           gives us a contradiction. -/
        discriminate Hk.
      - /-E = ev_S n' E' -/
        /-This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. -/
        injection Hk as Heq. rewrite <- Heq. apply E'.
    Qed.

    /- TERSE: *** -/
    /- Alternatively, the proof is straightforward using the inversion
        lemma that we proved above. -/
/-LATER: BCP 21: ... to here -- i.e., now we go straight to inversion
   without all this noodling around about destruct. -/
/-HIDE: MRC 3/22: Yes, I favor going straight to inversion. -/ -/
/-/HIDE -/
/- We can use the inversion lemma that we proved above to help
    structure proofs: -/

theorem ev_succ_succ_ev : ∀ n, Ev (n + 2) → Ev n := by
  intro n H
  apply ev_inversion at H
  cases H
  case inl _ => contradiction
  case inr h =>
    let ⟨n', ⟨h₁,  h₂⟩⟩ := h
    injections h₁ heq
    subst heq
    exact  h₂

/- HIDE -/
/- HIDE: CH: Tried, but there is no similarly simple lemma for le? -/
/-theorem leS_le : forall n m, le n (S m) → le n m.
Proof.
  intros n m H. apply le_inversion in H. destruct H as [H0|h₁].
  - rewrite H0. Abort. /- This one is false! -/

theorem leS_le : forall n m, le (S n) (S m) → le n m.
Proof.
  intros n m H. apply le_inversion in H. destruct H as [Hn|HS].
  - injection Hn as Hnm. rewrite Hnm. apply le_refl.
  - destruct HS as [m' [Hmm' Hle]]. injection Hmm' as Hmm'.
    rewrite Hmm' in *. /- This one seems true, but needs more work -/
Abort.-/
/- /HIDE -/


/- FULL: Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving `Ev`.  The first subgoal is
    a contradiction that is discharged with `contradiction`.  The
    second subgoal makes use of `injections` and `subst`.

    We've defined a handy tactic called `inversion` that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every `inductive` definition we
    make.

    Here, the `inversion` tactic can detect (1) that the first case,
    where `n = 0`, does not apply and (2) that the `n'` that appears
    in the `ev_succ_succ` case must be the same as `n`.

    The details of how `inversion` is implemented are beyond the scope
    of this course, but suffice to say Lean's metaprogramming capabilities
    are such that almost any sequence of reasoning steps can be implemented
    as a new tactic.
    -/
-- TERSE: ***
/- TERSE: We've provided a handy tactic called `inversion` that does
    the work of our inversion lemma and more besides. -/

theorem ev_succ_succ_ev' : ∀ n, Ev (n + 2) → Ev n := by
  intro n h
  inversion h; assumption

/- HIDE -/
    /- PR: The following dialogue used to be between two versions of
        theorem ev_minus2' (using `inversion` and `cases`). The
        concerns are affected by but not made obsolete by the new
        treatment of `inversion` here. I think more work is needed. -/
    /- AAA: I'm finding it a bit awkward to discuss `inversion` here
       instead of `cases`, especially given that we are using
       `cases` to talk about [reflect] below... Would it be too crazy
       to use `inversion` only where it is actually needed? -/
    /- BCP: I have never been satisfied with our discussion of destruct
        vs. inversion.  What's here now is much better than we've ever had
        before.  But if you have a clear idea for how to clean it up
        further, I'm all ears.  One possibility -- perhaps easy enough to
        do now -- would be to replace inversion by destruct in this
        discussion and move the inversion vs. destruct discussion into the
        following subsection.  (In fact, I favor trying this.  The next
        section also needs some help, and consolidating the discussion
        would be a good beginning.) -/
    /- AAA: I'm in favor of trying this too, but I'm afraid that it might
        have significant impact on other sections. Let's leave it like
        this for now -- at least it's better than what we had before. -/
/- /HIDE -/

/- FULL -/
/- The `inversion` tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: -/

theorem one_not_even : ¬ Ev 1 := by
  intro H; apply ev_inversion at H; cases H
  /- HIDE: OL20: Someone asked here before "Why doesn't eqn:EE work
         here??".  It has to do with the use of _ in the pattern.
         Anyway when destructing \/,/\, or exists, what we get from
         eqn:EE is only confusing for students. I think that we should
         remove all "eqn"s in these cases. I did it in this file. -/
  case inl _ => contradiction
  case inr h =>
    let ⟨n', ⟨h₁,  h₂⟩⟩ := h
    injections

theorem one_not_even' : ¬ Ev 1 := by
  intro h; inversion h
-- /FULL


-- FULL
-- EX1 (inversion_practice)
/- Prove the following result using `inversion`.  (For extra
    practice, you can also prove it using the inversion lemma.) -/

theorem ev_4_ev_n : ∀ n,
  Ev (n + 4) → Ev n := by
  -- ADMITTED -/
  intros n h
  inversion h
  case ev_succ_succ h' => apply ev_succ_succ_ev; exact h'
/- /ADMITTED -/
/- GRADE_THEOREM 1: ev_4_ev_n -/
/-* [] -/

-- EX1 (ev5_nonsense)
/- Prove the following result using `inversion`. -/

theorem ev5_nonsense : Ev 5 → 2 + 2 = 9 := by
  /- ADMITTED -/
  intro h
  /- Contradiction, as neither constructor can possibly apply... -/
  inversion h
  case ev_succ_succ h' =>
    inversion h'
    case ev_succ_succ h'' =>
    inversion h''
/- /ADMITTED -/
/-* [] -/
/- /FULL -/

/- We can use `inversion` to re-prove some theorems from
    `Tactics.lean`.

    Note that `inversion` also works on equality propositions. -/

theorem inversion_ex1 : ∀ (n m o : Nat),
  [n, m] = [o, o] → [n] = [m] := by
  intro n m o h
  inversion h; rfl

theorem inversion_ex2 : ∀ (n : Nat),
  n + 1 = 0 → 2 + 2 = 5 := by
  intro n h
  inversion h

/- TERSE: The `inversion` tactic works on any `H : P` where
    `P` is defined inductively:

      - For each constructor of `P`, make a subgoal where `H` is
        constrained by the form of this constructor.

      - Discard contradictory subgoals (such as `ev_0` above).

      - Generate auxiliary equalities (as with `ev_succ_succ` above). -/
/- SOONER: The wording there is totally awkward! -/
/- LATER: Is this too dense??  Since equality is defined in the next
   lecture [BCP: for some paths through the material -- they might
   also not see it at all!], it might actually be better to postpone
   the conversation here and do it all at once there. [PR: It is
   dense, but I don't think seeing the definition of equality helps,
   so I'm not sure postponing it would make a difference.] -/
/- FULL: Here's how `inversion` works in general.
      - Suppose the name `H` refers to an assumption `P` in the
        current context, where `P` has been defined by an `inductive`
        declaration.
      - Then, for each of the constructors of `P`, `inversion h`
        generates a subgoal in which `H` has been replaced by the
        specific conditions under which this constructor could have
        been used to prove `P`.
      - Some of these subgoals will be self-contradictory; `inversion`
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, `inversion` adds
        to the proof context all equations that must hold of the
        arguments given to `P` -- e.g., `n' = n` in the proof of
        `ev_succ_succ_ev`). -/

/- HIDE -/
    /- QUIZ -/
    /- HIDE: LY: not quite a fair question because this is the first
       time they are facing a situation where the index does not start
       with a constructor. -/
    /- Which tactics are needed to prove this goal, in addition to
        [simpl] and [apply]?
    [[
      n : Nat
      E : Ev (n + 2)
      =====================
      Ev n
    ]]

       (A) `inversion`

       (B) `inversion`, [discriminate]

       (C) `inversion`, [rewrite add_comm]

       (D) `inversion`, [rewrite add_comm], [discriminate]

       (E) These tactics are not sufficient to prove the goal.

     -/
    /- FOLD -/
   /- theorem quiz_ev_plus_2 : forall n, Ev (n + 2) → Ev n.
    Proof.
      intros n E.  rewrite add_comm in E.
      inversion E as [| n' E' Eq]. apply E'.
    Qed. -/
    /- /FOLD -/
    /- /QUIZ -/
/- /HIDE -/
/- TERSE: *** -/


/- HIDEFROMADVANCED -/
/- FULL: The `ev_double` exercise above allows us to easily show that
    our new notion of evenness is implied by the two earlier ones
    (since, by `even_bool_prop` in chapter \CHAP{Logic}, we already
    know that those are equivalent to each other). To show that all
    three coincide, we just need the following lemma. -/
/- TERSE: Let's try to show that our new notion of evenness implies
    our earlier notion (the one based on `double`). -/
/- SOONER: This whole part of the section is a mess!! -/
/- /HIDEFROMADVANCED -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : ∀ n, Ev n → Even n := by
  /- WORKINCLASS -/
  /- We could try to proceed by case analysis or induction on `n`.  But
      since `Ev` is mentioned in a premise, this strategy seems
      unpromising, because (as we've noted before) the induction
      hypothesis will talk about `n-1` (which is _not_ even!).  Thus, it
      seems better to first try `inversion` on the evidence for `Ev`.
      Indeed, the first case can be solved trivially. -/
  intro n h
  inversion h
  /- h = ev_0 -/
  case ev_0 => exists 0  -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  /- h = ev_succ_succ n' h' -/
  case ev_succ_succ n' h' =>
  /- Unfortunately, the second case is harder.  We need to show
    `∃ n₀, n' + 2 = double n₀`, but the only available assumption is
    `h'`, which states that `Ev n'` holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on `h` was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on `h`, we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for `Ev`: namely
    `h'`.  More formally, we could finish our proof if we could show
    that
[[
        ∃ k', n' = double k',
]]
    which is the same as the original statement, but with `n'` instead
    of `n`.  Indeed, it is not difficult to convince Lean that this
    intermediate result would suffice. -/
    have he : (∃ k', n' = double k') → (∃ n₀, n' + 2 = double n₀) := by
      intro ⟨k, hk⟩; exists (k + 1); rw [double_succ, hk]
    apply he
    /- Unfortunately, now we are stuck: we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about `n'` instead of `n`. -/
    sorry
/- LATER: APT: Added the explicit assert to "convince Lean" but the
   flow of the preceding discussion seems confusing to me. -/
/- SOONER: BCP 21: I agree that it's all pretty chewy. Wonder if we
   really need any of it or if the point could be made just as well
   with less detail...  When I explained it in class this time, I just
   observed that the destruct was giving us a hypothesis about 2 being
   even, which just can't be what we want, and skipped all the rest...
   After thinking about it for a bit, though, I do think the full
   story here is useful (at least for the FULL version -- the TERSE
   could still be streamlined). So I'm going to leave it for now. -/
/- SOONER: BCP 25: I think best just to shorten it! And maybe make it
   not a WORKINCLASS. -/
/- /WORKINCLASS -/


/- ####################################################### -/
/- ## Induction on Evidence -/

/- If this story feels familiar, it is no coincidence: We
    encountered similar problems in the \CHAP{Induction} chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! -/

/- FULL: The behavior of `induction` on evidence is the same as its
    behavior on data: It causes Lean to generate one subgoal for each
    constructor that could have been used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of `n` holds for all even numbers (i.e.,
    those for which `Ev n` holds), we can use induction on `Ev n`.
    This requires us to prove two things, corresponding to the two
    ways in which `Ev n` could have been constructed. If it was
    constructed by `ev_0`, then `n=0` and the property must hold of
    `0`. If it was constructed by `ev_succ_succ`, then the evidence of `Ev n`
    is of the form `ev_succ_succ n' E'`, where `n = n' + 2` and `h'` is
    evidence for `Ev n'`. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for `n'`. -/

/- Let's try proving that lemma again: -/

theorem ev_Even : ∀ n, Ev n → Even n := by
  intro n h
  induction h
  /- h = ev_0 -/
  case ev_0 => exists 0  -- (`0 = double 0` is closed by `exists`'s final `rfl`)
  /- h = ev_succ_succ n' h',  with ih : Even n' -/
  case ev_succ_succ n' h' ih =>
    let ⟨k, hk⟩ := ih
    exists k + 1; rw [double_succ, hk]


/- FULL: Here, we can see that Lean produced an `ih` that corresponds
    to `h`, the single recursive occurrence of `Ev` in its own
    definition.  Since `h'` mentions `n'`, the induction hypothesis
    talks about `n'`, as opposed to `n` or some other number. -/

/- FULL -/
/- The equivalence between the second and third definitions of
    evenness now follows. -/

theorem ev_Even_iff : ∀ n, Ev n ↔ Even n := by
  intro n; apply Iff.intro
  . intro h; exact ev_Even _ h
  . intro ⟨k, hk⟩; rw [hk]; exact ev_double k


/- As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. -/

/- The following exercises provide simpler examples of this
    technique, to help you familiarize yourself with it. -/

/- EX2 (ev_sum) -/
theorem ev_sum : ∀ n m, Ev n → Ev m → Ev (n + m) := by
  /- ADMITTED -/
  intro n m hn hm
  induction hn
  case ev_0 => rw [Nat.zero_add]; exact hm
  case ev_succ_succ n' h' ih =>
    rw [Nat.add_comm, ←Nat.add_assoc, Nat.add_comm m]
    apply Ev.ev_succ_succ; exact ih
/- /ADMITTED -/
/- [] -/

/- EX3A! (ev_ev__ev) -/
theorem ev_ev__ev : ∀ n m, Ev (n + m) → Ev n → Ev m := by
  /- Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. -/
  /- ADMITTED -/
  intro n m hnm hn
  induction hn generalizing m
  case ev_0 => rw [Nat.zero_add] at hnm; exact hnm
  case ev_succ_succ n' h' ih =>
    apply ih; rw [Nat.add_comm, ←Nat.add_assoc, Nat.add_comm m] at hnm
    inversion hnm; assumption
/- /ADMITTED -/
/- [] -/

/- EX3? (ev_plus_plus) -/
/- This exercise can be completed without induction or case analysis.
    But, you will need a clever `have` and some tedious rewriting.
    Hint: Is `(n+m) + (n+p)` even? -/

theorem ev_plus_plus : ∀ n m p,
  Ev (n+m) → Ev (n+p) → Ev (m+p) := by
  /- ADMITTED -/
  intro n m p hnm hnp
  apply (ev_ev__ev (n+n))
  . have h : n + n + (m + p) = n + m + (n + p) := by
      rw [Nat.add_assoc, Nat.add_assoc]
      congr 1
      exact Nat.add_left_comm _ _ _
    rw [h]
    apply ev_sum
    . assumption
    . assumption
  . rw [←double_add]; exact ev_double n
/- /ADMITTED -/
/- [] -/

-- FULL
/-
  Another example of a proposition that can be characterized both recursively and
  inductively is the `In` predicate we defined in the Logic chapter. As a reminder,
  the recursive definition we saw looked like this:
-/
-- /FULL

-- TERSE
/-
  Recall the definition of `In` from last chapter:
-/
-- /TERSE

@[irreducible]
def In' {α : Type} (x : α) (xs : List α) : Prop :=
  match xs with
  | [] => False
  | x' :: xs' => x = x' ∨ In' x xs'

/-
  We can also write this definition inductively like so:
-/

inductive In_Inductive {α : Type} (a : α) : List α → Prop
  | head (as : List α) : In_Inductive a (a::as)
  | tail (b : α) {as : List α} : In_Inductive a as → In_Inductive a (b::as)

/- In fact, this is exactly how Lean defines this proposition, which it calls `Mem` and which
   is written `x ∈ l` (the Unicode symbol is written \in). A good exercise to test your understanding of induction on
   evidence is to prove the equivalence of these definitions: -/

/- EX2 (in_mem) -/
theorem in_mem α (x : α) (l : List α) : In x l ↔ x ∈ l := by
  /- ADMITTED -/
  constructor
  . intro h; induction l with
    | nil => rw [In_nil] at h; contradiction
    | cons hd tl ih =>
      rw [In_cons] at h
      obtain h | h := h
      . subst h; constructor
      . constructor; exact ih h
  . intro h; induction h with
    | head l' => rw [In_cons]; left; rfl
    | tail y h ih => rw [In_cons]; right; assumption
/- /ADMITTED -/
/- [] -/

/- The characterizing lemmas for `∈` are called `List.mem_nil_iff` and `List.mem_cons` -/

/- ####################################################### -/
/- ## Multiple Induction Hypotheses -/

/- Recall the definition of the reflexive, transitive, closure of a
    relation: -/

/- HIDEFROMHTML -/
namespace ClosReflTransRemainder
/- /HIDEFROMHTML -/
inductive ClosReflTrans {α: Type} (R: α → α → Prop) : α → α → Prop where
  | rt_step (x y : α) :
      R x y →
      ClosReflTrans R x y
  | rt_refl (x : α) :
      ClosReflTrans R x x
  | rt_trans (x y z : α) :
      ClosReflTrans R x y →
      ClosReflTrans R y z →
      ClosReflTrans R x z
/- HIDEFROMHTML -/
end ClosReflTransRemainder
/- /HIDEFROMHTML -/


/-Let's say that a relation on a type `α` is _diagonal_ if it
    refines the identity relation -- i.e., if `R x y` implies `x = y`. -/

/- HIDE: NDS 25: I originally wanted to do this with the empty
    relation, defined inductively, but this requires introducing the
    surprising behavior of unhabitated types, which I don't think have
    been covered (yet?). Maybe they should be?  BCP 25: This one seems good. -/

def isDiagonal {α : Type} (R: α → α → Prop) := ∀ x y, R x y → x = y

/- Now consider the following lemma about diagonal relations: -/

theorem closure_of_diagonal_is_diagonal : ∀ α (R: α → α → Prop),
  isDiagonal R →
  isDiagonal (ClosReflTrans R) := by

  intro α R hDiag x y h
  induction h
  /- The two first cases go as you'd expect... -/
  case rt_step x' y' hr =>
    rw [hDiag x' y' hr]
  case rt_refl => rfl
  /- ...  but something interesting happens here: there are two
       induction hypotheses, `ih` and `ih'`! If you think about it, it
       is not that weird: we are in the case `rt_trans`, which has
       two recursive components, `hxy`, relating `x` to `y` and `hyz`,
       relating `y` to `z`. Hence we may want (and will actually need)
       an induction hypothesis for `hxy` and one for `hyz` -- they are
       called `ihxy` and `ihyz` here. In general, Lean will always
       generate one induction hypothesis per recursive constructor of
       the type being inducted over. -/
  case rt_trans x' y' z' hxy hyz ihxy ihyz =>
    rw [ihxy, ihyz]


/- HIDE: NDS comparing the previous proof to the pen-and-paper version
   could be an idea to consider, as the way people tend to write it
   on paper differs a bit from the mechanized proof.  BCP 25: Yes. -/

/- HIDE -/
    /- LATER: BCP 25: This bit feels potentially confusing and also not
      needed -- people that are paying attention enough to wonder about
      this will notice it when it happens later... -/
    /- Note that having multiple induction hypotheses is not
        specific to evidence: any constructor of any inductive type with
        more than one recursive component will yield as many induction
        hypotheses as it has recursive components. -/
    /- HIDE: NDS we may want to either 1) link to IndPrinciples for such
      examples or 2) add such an example here, even though it is kind of
      out of the topic. -/
/- /HIDE -/

/- EX4A? (ev'_ev) -/
/- INSTRUCTORS: This is pretty hard, unless you know the trick that
   the sample proof uses!!  But at least it's marked as
   advanced and optional. :-) -/
/- In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for `Ev`: -/

inductive Ev' : Nat → Prop where
  | ev'_0 : Ev' 0
  | ev'_2 : Ev' 2
  | ev'_sum n m (Hn : Ev' n) (Hm : Ev' m) : Ev' (n + m)

/- Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the \CHAP{Logic}
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. -/

theorem ev'_ev : ∀ n, Ev' n ↔ Ev n := by
 /- ADMITTED -/
  intro n
  apply Iff.intro
  . /- → -/
    intro h; induction h
    . constructor
    . constructor; constructor
    . apply ev_sum; assumption; assumption
  . /- <- -/
    intro h; induction h
    . constructor
    . constructor; assumption; constructor
/- /ADMITTED -/
/- [] -/

/- We can do similar inductive proofs on the [Perm3] relation,
    which we defined earlier as follows: -/

namespace Perm3Reminder

inductive Perm3 {α : Type} : List α → List α → Prop where
  | perm3_swap12 (a b c : α) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : α) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l₁ l₂ l₃ : List α) :
      Perm3 l₁ l₂ → Perm3 l₂ l₃ → Perm3 l₁ l₃

end Perm3Reminder

theorem Perm3_symm : ∀ (α : Type) (l₁ l₂ : List α),
  Perm3 l₁ l₂ → Perm3 l₂ l₁ := by

  intro α l₁ l₂ h; induction h
  case perm3_swap12 => constructor
  case perm3_swap23 => constructor
  case perm3_trans _ _ _ _ _ ih₁2 ih₂3 =>
    exact Perm3.perm3_trans _ _ _ ih₂3 ih₁2


-- DEV
-- RAB & DHS: swap to Lean's `In` predicate (∈) rather than our own
-- Also, we might use this as a running example in Automation.
-- /DEV

/- EX2 (Perm3_In) -/
/- If you find yourself dealing with deeply nested `cases` in this proof,
   think back to `Logic` where you learned about the `obtain` tactic -/
theorem Perm3_In : ∀ (α : Type) (x : α) (l₁ l₂ : List α),
    Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂ := by
  /- ADMITTED -/
  intros α x l₁ l₂ hPerm hIn
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
/- HIDE: CH: The base cases are a bit stupid without [tauto] -/
/- /ADMITTED -/
/- [] -/

/- EX1? (Perm3_NotIn) -/
theorem Perm3_NotIn : ∀ (α : Type) (x : α) (l₁ l₂ : List α),
    Perm3 l₁ l₂ → ¬x ∈ l₁ → ¬x ∈ l₂ := by
  /- ADMITTED -/
  intros α x l₁ l₂ hPerm hIn hContra
  apply hIn; apply Perm3_In
  . apply Perm3_symm; exact hPerm
  . exact hContra
/- /ADMITTED -/
/- [] -/

/- EX2? (NotPerm3) -/
/- Proving that something is NOT a permutation is quite tricky. Some
    of the lemmas above, like [Perm3_In] can be useful for this. -/
example : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  /- ADMITTED -/
  intro h; apply (Perm3_In Nat 3) at h
  have h4 : ¬3 ∈ [1, 2, 4] := by
    rw [List.mem_cons, List.mem_cons, List.mem_cons]; intro h4
    obtain h | h | h | h := h4
    . contradiction
    . contradiction
    . contradiction
    . contradiction
  apply h4; apply h
  rw [List.mem_cons, List.mem_cons, List.mem_cons]
  right; right; left; rfl
/- /ADMITTED -/
/- [] -/
/- LATER: Optional / advanced exercise (or exam question???): Extend
   this definition to permutations on arbitrary-length lists.  Make
   sure that you can prove the following...
     - length-invariant
     - if we filter a Nat list and its permutation by equality to some
       number, we get the same length (indeed, this could be an
       alternate characterization, I guess)
-/
/- /FULL -/

/- FULL -/
/- ####################################################### -/
/- # Exercising with Inductive Relations -/

/- SOONER: CH: Bad flow + duplication needs fixing.
   Could move some of this to the top.
   In the terse version this whole section is useless,
   it only has a (mostly) duplicated definition.
   For now FULLED the whole thing, but better fix seems needed. -/

/- TERSE: Just as a single-argument proposition defines a _property_,
    a two-argument proposition defines a _relation_. -/
/- FULL: A proposition parameterized by a number (such as `Ev`)
    can be thought of as a _property_ -- i.e., it defines
    a subset of `Nat`, namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. -/

/- TERSE: HIDEFROMHTML -/
namespace Playground
/- TERSE: /HIDEFROMHTML -/

/- Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. -/

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat)                : Le n n
  | succ (n m : Nat) (H : Le n m) : Le n (m + 1)

/- FULL: (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) -/

/- FULL: Proofs of facts about `≤` using the constructors `Nat.le.refl` and
    `Nat.le.step` follow the same patterns as proofs about properties, like
    [ev] above. We can `apply` the constructors to prove `≤`
    goals (e.g., to show that `3≤3` or `3≤6`), and we can use
    tactics like `inversion` to extract information from `≤`
    hypotheses in the context (e.g., to prove that `(2 ≤ 1) → 2+2=5`.) -/

/- TERSE: *** -/
/- FULL: Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- `rw`, `dsimp` and
    `rfl` don't do the job, because the proofs aren't just a
    matter of simplifying computations.) -/
/- TERSE: Some sanity checks... -/

theorem test_le1 : 3 ≤ 3 := by
  /- WORKINCLASS -/
  apply Nat.le.refl
/- /WORKINCLASS -/

theorem test_le2 : 3 ≤ 6 := by
  /- WORKINCLASS -/
  apply Nat.le.step; apply Nat.le.step; apply Nat.le.step; apply Nat.le.refl
  /- /WORKINCLASS -/

theorem test_le3 : (2 ≤ 1) → 2 + 2 = 5 := by
  /- WORKINCLASS -/
  intros h
  inversion h
  case step h' => inversion h'
/- /WORKINCLASS -/

/- TERSE: *** -/
/- The "strictly less than" relation `n < m` can now be defined
    in terms of `Nat.le`. -/

def lt (n m : Nat) : Prop := Nat.le (n + 1) m

/- TERSE: *** -/
/- The `≥` operation is defined in terms of `≤`.
   Lean provides a theorem `ge_iff_le` allowing us to rewrite between them.
-/

def ge (m n : Nat) : Prop := Nat.le n m

example : ∀ (m n : Nat), m ≥ n → n ≤ m := by
  intro m n h
  rw [←ge_iff_le]; assumption

/- TERSE: HIDEFROMHTML -/
end Playground


/- TERSE: /HIDEFROMHTML -/

/- HIDE: PR: Added the following paragraph to try to help reduce
   random walks over the following exercises. -/
/- FULL: From the definition of `le`, we can sketch the behaviors of
    `cases` and `induction` on a hypothesis `h`
    providing evidence of the form [le e1 e2].  Doing `cases h`
    will generate two cases. In the first case, `e1 = e2`, and it
    will replace instances of `e2` with `e1` in the goal and context.
    In the second case, `e2 = n' + 1` for some `n'` for which `le e1 n'`
    holds, and it will replace instances of `e2` with `n' + 1`.
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing `induction h`
    will, in the second case, add the induction hypothesis that the
    goal holds when `e2` is replaced with `n'`. -/

/- Here are a number of facts about the `≤` and `<` relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. -/

/- EX3! (le_facts) -/
theorem le_trans : ∀ (m n o : Nat), m ≤ n → n ≤ o → m ≤ o := by
  /- ADMITTED -/
  intro n m o h₁  h₂
  induction  h₂
  case refl => assumption
  case step m' h' ih => constructor; exact ih
/- /ADMITTED -/
/- GRADE_THEOREM 0.5: le_trans -/

theorem zero_le_n : ∀ n, 0 ≤ n := by
  /- ADMITTED -/
  intro n; induction n
  case zero => constructor
  case succ n ih => constructor; assumption
  /- /ADMITTED -/
/- GRADE_THEOREM 0.5: zero_le_n -/

theorem n_le_m__succ_n_le_succ_m : ∀ n m,
  n ≤ m → n + 1 ≤ m + 1 := by
  /- ADMITTED -/
  intro n m h
  induction h
  case refl => constructor
  case step m' h ih =>
    rw [Nat.succ_add]
    constructor
    assumption
/- /ADMITTED -/
/- GRADE_THEOREM 0.5: n_le_m__Sn_le_Sm -/

theorem succ_n_le_succ_m__n_le_m : ∀ n m,
  n + 1 ≤ m + 1 → n ≤ m := by
  /- ADMITTED -/
  intro n m h
  inversion h
  case refl => constructor
  case step h' =>
    apply le_trans _ (n + 1) _
    . constructor; constructor
    . assumption
/- /ADMITTED -/
/- GRADE_THEOREM 1: Sn_le_Sm__n_le_m -/

theorem le_add_l : ∀ (a b : Nat), a ≤ a + b := by
  /- ADMITTED -/
  intros a b
  induction a
  case zero => rw [Nat.zero_add]; apply zero_le_n
  case succ a' ih =>
    rw [Nat.succ_add]
    apply n_le_m__succ_n_le_succ_m
    assumption
/- GRADE_THEOREM 0.5: le_add_l -/
/- [] -/

/- EX2! (plus_le_facts1) -/
theorem add_le : ∀ (n₁ n₂ m : Nat),
  n₁ + n₂ ≤ m →
  n₁ ≤ m ∧ n₂ ≤ m := by
 /- ADMITTED -/
  intros n₁ n₂ m h
  induction h
  case refl =>
    constructor
    . apply le_add_l
    . rw [Nat.add_comm]; apply le_add_l
  case step m' h' ih =>
    obtain ⟨h₁, h₂⟩ := ih
    constructor
    . apply le_trans (n := n₁ + n₂)
      . apply le_add_l
      . apply Nat.le.step; assumption
    . apply le_trans (n := n₁ + n₂)
      . rw [Nat.add_comm]; apply le_add_l
      . apply Nat.le.step; assumption
/- /ADMITTED -/
/- GRADE_THEOREM 1: add_le -/

theorem add_le_cases : ∀ (n m p q : Nat),
  n + m ≤ p + q → n ≤ p ∨ m ≤ q := by
  /- Hint: May be easiest to prove by induction on `n`. -/
/- ADMITTED -/
  intros n m p q h; induction n generalizing m p q
  case zero => left; apply zero_le_n
  case succ n' ih =>
    cases p
    case zero =>
      right; apply add_le at h
      obtain ⟨_, h⟩ := h
      rw [Nat.zero_add] at h; assumption
    case succ p' =>
      rw [Nat.succ_add, Nat.succ_add] at h
      apply succ_n_le_succ_m__n_le_m at h
      apply ih at h
      cases h
      . left; apply n_le_m__succ_n_le_succ_m; assumption
      . right; assumption
/- /ADMITTED -/
/- GRADE_THEOREM 1: add_le_cases -/
/- [] -/

/- EX2! (plus_le_facts2) -/
theorem add_le_compat_l : ∀ (n m p : Nat),
  n ≤ m →
  p + n ≤ p + m := by
  /- ADMITTED -/
  intros n m p h
  induction p
  case zero =>
    rw [Nat.zero_add, Nat.zero_add]; assumption
  case succ p' ih =>
    rw [Nat.succ_add, Nat.succ_add]
    apply n_le_m__succ_n_le_succ_m
    assumption
/- /ADMITTED -/
/- GRADE_THEOREM 0.5: add_le_compat_l -/

theorem plus_le_compat_r : ∀ (n m p : Nat),
  n ≤ m →
  n + p ≤ m + p := by
  /- ADMITTED -/
  intro n m p h
  rw [Nat.add_comm, Nat.add_comm m]
  apply add_le_compat_l
  assumption
/- /ADMITTED -/
/- GRADE_THEOREM 0.5: plus_le_compat_r -/

theorem le_plus_trans : ∀ (n m p : Nat),
  n ≤ m →
  n ≤ m + p := by
  /- ADMITTED -/
  intros n m p h
  induction p
  case zero => rw [Nat.add_zero]; assumption
  case succ p' ih =>
    rw [←Nat.add_assoc]; constructor; assumption
/- /ADMITTED -/
/- GRADE_THEOREM 1: le_plus_trans -/
/- [] -/

/- EX3? (lt_facts) -/
theorem lt_ge_cases : ∀ (n m : Nat),
  n < m ∨ n ≥ m := by
  /- ADMITTED -/
  intro n m; induction n generalizing m
  case zero =>
    cases m
    case zero => right; constructor
    case succ _ =>
      left;
      apply n_le_m__succ_n_le_succ_m;
      apply zero_le_n
  case succ n' ih =>
    cases m
    case zero =>
      rw [ge_iff_le]; right
      apply zero_le_n
    case succ m' =>
      obtain ih | ih := (ih m')
      . left
        apply n_le_m__succ_n_le_succ_m
        exact ih
      . right
        apply n_le_m__succ_n_le_succ_m
        exact ih
/- /ADMITTED -/
/- GRADE_THEOREM 1.5: lt_ge_cases -/

theorem n_lt_m__n_le_m : ∀ (n m : Nat),
  n < m →
  n ≤ m := by
  /- ADMITTED -/
  intro n m h
  apply succ_n_le_succ_m__n_le_m; constructor; assumption
/- /ADMITTED -/
/- GRADE_THEOREM 0.5: n_lt_m__n_le_m -/

theorem plus_lt : ∀ (n₁ n₂ m : Nat),
  n₁ + n₂ < m →
  n₁ < m ∧ n₂ < m := by
/- ADMITTED -/
  intro n₁ n₂ m h
  constructor
  . apply le_trans (n := (n₁ + n₂) + 1)
    . apply n_le_m__succ_n_le_succ_m
      apply le_add_l
    . exact h
  . apply le_trans (n := (n₂ + n₁) + 1)
    . apply n_le_m__succ_n_le_succ_m
      apply le_add_l
    . rw [Nat.add_comm n₂]; assumption
/- /ADMITTED -/
/- GRADE_THEOREM 1: plus_lt -/
/- [] -/

/- EX4? (ble_le) -/
theorem ble_complete : ∀ (n m : Nat),
  n ≤? m = true → n ≤ m := by
  /- ADMITTED -/
  intro n m h; induction n generalizing m
  case zero => apply zero_le_n
  case succ n' ih =>
    cases m
    case zero =>
      contradiction
    case succ m' =>
      dsimp [Nat.ble] at h
      apply n_le_m__succ_n_le_succ_m
      apply ih; apply h
/- /ADMITTED -/
/- GRADE_THEOREM 2: ble_complete -/

theorem ble_correct : ∀ n m,
  n ≤ m →
  n ≤? m = true := by
  /- ADMITTED -/
  intro n m h
  induction n generalizing m
  case zero => dsimp [Nat.ble]
  case succ n' ih =>
    cases m
    case zero => contradiction
    case succ m' =>
      dsimp [Nat.ble]
      apply succ_n_le_succ_m__n_le_m at h
      apply ih at h
      assumption
/- /ADMITTED -/
/- GRADE_THEOREM 2: ble_correct -/

/- Hint: The next two can easily be proved without using `induction`. -/

/- LATER: AC'21: To me what would be interesting for this last lemma `ble_iff`
   would be to show that the proofs of completeness and correctness can
   be carried out in a single induction. -/

theorem ble_iff : ∀ n m,
  n ≤? m = true ↔ n ≤ m := by
  /- ADMITTED -/
  intro n m; apply Iff.intro
  . apply ble_complete
  . apply ble_correct
/- /ADMITTED -/
/- GRADE_THEOREM 1: ble_iff -/

theorem ble_true_trans : ∀ n m o,
  n ≤? m = true → m ≤? o = true → n ≤? o = true := by
  /- ADMITTED -/
  intros n m o
  rw [ble_iff, ble_iff, ble_iff]
  apply le_trans
/- /ADMITTED -/
/- /HIDE -/
/- GRADE_THEOREM 1: ble_true_trans -/
/- [] -/


/- LATER: Another potential exercise:  m ≤ n -→ n = m+(n-m).
   See p. 188 in CoqArt. -/

namespace R

/- EX3M! (R_provability) -/
/- We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: -/

inductive R : Nat → Nat → Nat → Prop where
  | c1                                       : R 0     0     0
  | c2 m n o (h : R m     n     o        )   : R (m + 1) n     (o + 1)
  | c3 m n o (h : R m     n     o        )   : R m     (n + 1) (o + 1)
  | c4 m n o (h : R (m + 1) (n + 1) (o + 2)) : R m     n     o
  | c5 m n o (h : R m     n     o        )   : R n     m     o

/- HIDE: APT 21: Reformatted the above after a student with dyslexia
   complained. But the effect is still lost in the HTML.  He also
   noted that the kind of question that follows doesn't really require
   a high-arity relation.

   MRC 3/22: I believe that violates the OCaml Community Guidelines on
   indentation.

   https://ocaml.org/learn/tutorials/guidelines.html#Bad-indentation-of-pattern-matching-constructs

   Whether those are applicable here is a matter of debate. But
   torquing the entire textbook into this mode of alignment does not
   seem any more desirable to me than torquing an OCaml codebase.

   BCP 25: No, but for this specific problem it seems OK. Let's leave
   it like this. -/

/- - Which of the following propositions are provable?
      - `R 1 1 2`
      - `R 2 2 6`

    - If we dropped constructor `c5` from the definition of `R`,
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor `c4` from the definition of `R`,
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. -/

/- SOLUTION -/
/-
   - The first proposition is provable and the second is not.
     The proof term for the first is:
[[
       (c3 _ _ _ (c2 _ _ _ c1)).
]]
   - Dropping [c5] would not change the set of provable
     propositions.  [c4] and [c1] don't interact with [c5], since
     they're already symmetric in [m] and [n]; [c2] followed by
     [c5] is equivalent to [c3], and vice versa.

   - Dropping [c4] would not change the set of provable
     propositions. This constructor just "undoes" one application
     of [c2] and one application of [c3]. More precisely, the
     only way we can construct evidence for [R (S m) (S n) (S (S o))]
     is by applying [c2] and [c3] (in either order) to evidence for
     [R m n o], so the latter must already hold. (This can be proved
     by induction, although the proof is surprisingly tedious.) -/
/- /SOLUTION -/

/- HIDE -/
    /- Here is such a proof for posterity. -/

    /- inductive R' : Nat → Nat → Nat → Prop where
      | c1' : R' 0 0 0
      | c2' m n o (h : R' m n o) : R' (m + 1) n (o + 1)
      | c3' m n o (h : R' m n o) : R' m (n + 1) (o + 1)

    Ltac inv H := inversion H; subst; clear H.

    theorem c5_redundant: forall m n o, R' m n o → R' n m o.
    Proof.
      intros m n o H.
      induction H.
      - apply c1'.
      - apply c3'; auto.
      - apply c2'; auto.
    Qed.

    theorem c4_redundant: forall m n o, R' (S m) (S n) (S(S o)) → R' m n o.
    Proof.
      /- This one is nastier than one might expect. -/
      assert (Q1: forall m n o, R' (S m) n (S o) → R' m n o).
      { induction n; intros.
        - inv H.  apply h₃.
        - inv H.
          + apply h₃.
          + destruct o.
            * inv h₃.
            * apply c3'. apply IHn. apply h₃.
      }
      assert (Q2: forall m n o, R' m (S n) (S o) → R' m n o).
      { induction m; intros.
        - inv H. apply h₃.
        - inv H.
          + destruct o.
            * inv h₃.
            * apply c2'.  apply IHm. apply h₃.
          + apply h₃.
      }
      intros.
      inv H.
      - apply Q2; apply h₃.
      - apply Q1; apply h₃.
    Qed.

    theorem R_R': forall m n o, R m n o↔  R' m n o.
    Proof.
      split; intros.
      -  induction H.
        + apply c1'.
        + apply c2'; auto.
        + apply c3'; auto.
        + apply c4_redundant; auto.
        + apply c5_redundant; auto.
      - induction H.
        + apply c1.
        + apply c2; auto.
        + apply c3; auto.
    Qed. -/
/- /HIDE -/

/- GRADE_MANUAL 3: R_provability -/
/- [] -/

/- EX3? (R_fact) -/
/- The relation `R` above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Lean. -/
/- TODO (DHS): They really need to use (+) here, not Nat.add,
   or there's some typeclass nonsense in the proofs -/
def fR : Nat → Nat → Nat
  /- ADMITDEF -/ :=
  fun x y => x + y
/- /ADMITDEF -/

theorem R_equiv_fR : ∀ m n o, R m n o ↔ fR m n = o := by
/- ADMITTED -/
  intro m n o
  unfold fR
  apply Iff.intro
  . intro h; induction h
    case c1 => rfl
    case c2 m n o _ ih => rw [Nat.succ_add, ih]
    case c3 m n o _ ih => rw [Nat.add_succ, ih]
    case c4 m n o _ ih =>
      rw [Nat.succ_add, Nat.add_succ] at ih
      injections
    case c5 m n o _ ih => rw [Nat.add_comm]; exact ih
  . intro h; subst h
    have R0 : ∀ k, R 0 k k := by
      intro k; induction k
      case zero => exact .c1
      case succ k ih => exact .c3 _ _ _ ih
    induction m
    case zero => rw [Nat.zero_add]; exact R0 n
    case succ m ih => rw [Nat.succ_add]; exact .c2 _ _ _ ih
/- HIDE: And here's a somewhat nicer version using some automation,
   but we haven't covered that yet...

From Stdlib Require Import Lia.

theorem R_plus: forall m n o, R m n o↔  m + n = o.
Proof.
  intros m n o; split; intros.
  - induction H; try reflexivity; try lia.
  - generalize dependent n. generalize dependent m.
    induction o as [|o']; intros m n H.
    + destruct m; try inversion H.
      destruct n; try inversion H0.
      apply c1.
    + destruct m as [|m'].
      * destruct n; try inversion H. apply c3.
        apply IHo'. reflexivity.
      * apply c2. apply IHo'. lia.
Qed.
-/
/- /ADMITTED -/
/- [] -/

end R

/- EX4A (subsequence) -/
/- A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
[[
      [1,2,3]
]]
    is a subsequence of each of the lists
[[
      [1,2,3]
      [1,1,1,2,2,3]
      [1,2,7,3]
      [5,6,1,9,9,2,7,3,8]
]]
    but it is _not_ a subsequence of any of the lists
[[
      [1,2]
      [1,3]
      [5,6,2,1,7,3,8].
]]

    - Define an inductive proposition [subseq] on [list Nat] that
      captures what it means to be a subsequence.  There are a number
      of correct ways to do this. You should make sure that your
      definition behaves correctly on all the positive and negative
      examples above, but you do not need to prove this formally.

    - Prove `subseq_refl` that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove `subseq_app` that for any lists `l₁`, `l₂`, and `l₃`,
      if `l₁` is a subsequence of `l₂`, then `l₁` is also a subsequence
      of [l₂ ++ l₃].

    - (Harder) Prove [subseq_trans] that subsequence is transitive --
      that is, if `l₁` is a subsequence of `l₂` and `l₂` is a
      subsequence of `l₃`, then `l₁` is a subsequence of `l₃`. -/
/- HIDE -/
/- SOONER: (BCP'20) One of my students this semester pointed out
   that there is another definition that is intuitively perhaps just
   as reasonable and that makes these properties either easy or
   trivial: -/
inductive subseq' : List Nat → List Nat → Prop where
  | subseq'_0 (l: List Nat):
      subseq' l l
  | subseq'_inductive1 l (l₁ l₂ lx ly lz: List Nat)
      (h: subseq' l (l₁ ++ l₂)):
      subseq' l (lx ++ l₁ ++ ly ++ l₂ ++ lz)
  | subseq'_inductive2 (l₁ l₂ l₃: List Nat)
      (h₁: subseq' l₁ l₂)
      (h₂: subseq' l₂ l₃):
      subseq' l₁ l₃

/- SOONER: MRC 3/22: It's MUCH worse than that! a total relation
   suffices! (BCP 25: Really? It gets all the positive examples above,
   obviously, but not the negative ones... right?) Also this is
   another case where a [Fixpoint] would suffice instead of an
   inductively-defined proposition: [subseq] is definable as a
   structurally recursive function. -/
/- SOONER: FSR'25 - This definition of subseq also works, though it requires a
   lemma mirroring subseq_app that allows prepending an excess List.
   Notably, this only has two cases, in spite of the hint above.
   (BCP 25: Removed the hint.) -/
inductive subseq'' : List Nat → List Nat → Prop where
  | sub_nil'' (l: List Nat):
      subseq'' [] l
  | sub_cons'' (l l' l₀: List Nat) (x : Nat)
      (H: subseq'' l l'):
      subseq'' (x :: l) (l₀ ++ (x :: l'))
/- /HIDE -/
/- SOONER: AC'21: I think that it is more atomic to consider
   [sub_nil : subseq [] []]. The benefits is that it makes calls to
   [inversion] produce fewer goals. The downside is that one has to
   state as a lemma [sub_nil_l : forall l, subseq [] l], however it
   would be nice to have this as an exercise anyway, because otherwise
   students who go for the definition of [sub_seq [] []] are required
   to guess the need for [sub_nil_l].
   BCP: I agree this version could be nicer to suggest, and I agree that
   adding this lemma as a warm-up exercise is nice. -/
/- SOONER: Sainati 25: I am generally not against proofs that can be
   made much easier with smart inductive definitions (this is sort of the
   whole ball game in a way, isn't it?) but one way to make sure students
   can't trivialize the exercise is to just give them the definition we
   want them to use? We could also add a (maybe optional) question
   afterwards to provide a different definition that makes the proofs
   easier (and maybe prove them equivalent). -/

inductive subseq : List Nat → List Nat → Prop where
/- SOLUTION -/
  | sub_nil l : subseq [] l
  | sub_take x l₁ l₂ (h : subseq l₁ l₂) : subseq (x :: l₁) (x :: l₂)
  | sub_skip x l₁ l₂ (h : subseq l₁ l₂) : subseq l₁ (x :: l₂)
/- /SOLUTION -/


theorem subseq_refl : ∀ (l : List Nat), subseq l l := by
  /- ADMITTED -/
  intro l
  induction l
  case nil => constructor
  case cons hd tl ih =>
    constructor; assumption
/- /ADMITTED -/

theorem subseq_app : ∀ (l₁ l₂ l₃ : List Nat),
  subseq l₁ l₂ →
  subseq l₁ (l₂ ++ l₃) := by
  /- ADMITTED -/
  intro l₁ l₂ l₃ h
  induction h
  case sub_nil => constructor
  case sub_take => constructor; assumption
  case sub_skip => constructor; assumption
/- /ADMITTED -/

/- HIDE: AC'21: this exercise should probably be marked as more
   challenging.  In particular, it's not necessarily obvious at first
   sight that the induction should go on the second hypothesis, and
   with `l₁` generalized.  BCP 21: Made it 3 points instead of 2, and
   included a hint. CH'23: Made it 4 points, since there are 5 different
   choices here and the hint doesn't help with that. -/
theorem subseq_trans : ∀ (l₁ l₂ l₃ : List Nat),
  subseq l₁ l₂ →
  subseq l₂ l₃ →
  subseq l₁ l₃ := by
  /- Hint: be careful about what you are doing induction on and which
     other things need to be generalized... -/
  /- ADMITTED -/
  intro l₁ l₂ l₃ h₁2 h₂3
  induction h₂3 generalizing l₁
  case sub_nil => inversion h₁2; constructor
  case sub_take _ _ _ _ ih =>
    inversion h₁2; constructor
    . constructor; apply ih; assumption
    . constructor; apply ih; assumption
  case sub_skip _ _ _ _ ih =>
    constructor; apply ih; assumption;
/- /ADMITTED -/
/- GRADE_THEOREM 1: subseq_refl -/
/- GRADE_THEOREM 2: subseq_app -/
/- GRADE_THEOREM 3: subseq_trans -/
/- [] -/

/- EX2M? (R_provability2) -/
/- Suppose we give Lean the following definition:
[[
    inductive R : Nat → List Nat → Prop where
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (n + 1) (n :: l)
      | c3 n l (H: R (n + 1) l) : R n     l
]]
    Which of the following propositions are provable?

    - `R 2 [1,0]`
    - `R 1 [1,2,1,0]`
    - `R 6 [3,2,1,0]`  -/

/- LATER: APT: As in R_provability, above, would be good
   to get this formatting into the HTML version. -/

/- SOLUTION -/
/- The first two are provable, the third is not.

    In case this question puzzled you, one good way to understand
    definitions like this is to explore their implications with
    concrete examples, e.g.
[[
      R 0 []        by c1
      R 1 [0]       by c2 using R 0 []
      R 2 [1,0]     by c2 using R 1 [0]
      R 3 [2,1,0]   by c2 using R 2 [1,0]
      R 2 [2,1,0]   by c3 using R 3 [2,1,0]
      R 1 [2,1,0]   by c3 using R 2 [2,1,0]
      R 2 [1,2,1,0] by c2 using R 1 [2,1,0]
      R 1 [1,2,1,0] by c3 using R 2 [1,2,1,0]
      etc.
]]
    If you do a few more of these yourself, you should see the pattern
    emerging. -/
/- /SOLUTION -/
/- [] -/

/- HIDE -/
    /- Under construction... -/
    /- Definition partition {α : Type} (test : α → Bool) (l : List α) :=
      (filter test l, filter (fun x => negb (test x)) l) .

    /- LATER: Adjust inductive syntax -/
    inductive shuffle (α:Type) : List α → List α → List α → Prop :=
      | shuffle_nil_l : forall (l₂:List α), shuffle _ [] l₂ l₂
      | shuffle_nil_r : forall (l₁:List α), shuffle _ l₁ [] l₁
      | shuffle_cons_l : forall (x:α) (l₁ l₂ l12 : List α),
                          shuffle _ l₁ l₂ l12 →
                          shuffle _ (x::l₁) l₂ (x::l12)
      | shuffle_cons_r : forall (x:α) (l₁ l₂ l12: List α),
                          shuffle _ l₁ l₂ l12 →
                          shuffle _ l₁ (x::l₂) (x::l12).

    Arguments shuffle `α` _ _ _.

    /- HIDE: If they do this proof, they'll see some uses of [fix]... -/
    /- HIDE: M: I don't understand the above remark. This proof, though
      somewhat messy, can be done with everything they've seen so far.
      In any case, I attempt a proof, which is arguably the same as the
      old one. -/

    theorem partition_correct_1 : forall (α:Type) (l l₁ l₂: List α) (test:α → Bool),
      partition test l = (l₁,l₂) →
      shuffle l₁ l₂ l.
    Proof.
      intros α l l₁ l₂ test H. generalize dependent l₂. generalize dependent l₁.
      induction l as [| x l' ].
      - /- l = [] -/
        intros. inversion H. apply shuffle_nil_l.
      - /- l = x :: l' -/
        intros. destruct (test x) eqn:Heqb.
          + /- true = test x -/
            inversion H.
            rewrite Heqb in h₁. rewrite Heqb in h₂. rewrite  Heqb.
            simpl in h₂. simpl.
            apply shuffle_cons_l. apply IHl'. reflexivity.
          + /- false = test x -/
            inversion H.
            rewrite Heqb in h₁. rewrite Heqb in h₂. rewrite Heqb.
            simpl in h₂. simpl.
            apply shuffle_cons_r. apply IHl'. reflexivity.
    Qed.

    /- The old proof is longer (in number of lines), but I cheat.
      And the old proof uses more [destruct]s.
      Thus, the new proof above is better in at least two quantifiable
      ways, but I'm afraid its not entirely clean yet. -/

    /-  intros α l l₁ l₂ test H. generalize dependent l₂.
      generalize dependent l₁.
      induction l as [|x l'].
      - /- l = [] -/
        intros.
        unfold partition in H.
        unfold filter in H.
        inversion H.
        apply shuffle_nil_l.
      - /- l = x::l' -/
        intros.
        unfold partition in H. unfold filter in H.
        remember (test x) as h₁.
        destruct h₁.
          + /- true -/
            simpl in H.
            destruct l₁.
            * /- nil -/
              inversion H.
            * /- cons -/
              inversion H. subst.
              apply shuffle_cons_l.
              apply IHl'.
              unfold partition.
              unfold filter.
              reflexivity.
          + /- false -/
            simpl in H.
            destruct l₂.
            * /- nil -/
              inversion H.
            * /- cons -/
              inversion H. subst.
              apply shuffle_cons_r.
              apply IHl'.
              unfold partition.
              unfold filter.
              reflexivity.
    Qed. -/

    /- LATER: The proof needs to be polished. -/
    /- LATER: Also needs to talk about the two lists respecting the
      partitioning condition.  We'd really like to say all three
      parts of the spec together, but we don't have∧ yet! -/ -/
/- /HIDE -/

/- EX2? (total_relation) -/
/- Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. -/

inductive TotalRelation : Nat → Nat → Prop where
  /- SOLUTION -/
  | tot n m : TotalRelation n m
/- /SOLUTION -/


theorem total_relation_is_total : ∀ n m, TotalRelation n m := by
  /- ADMITTED -/
  intro _ _; constructor
/- /ADMITTED -/
/- GRADE_THEOREM 2: total_relation_is_total -/
/- [] -/

/- EX2? (empty_relation) -/
/- Define an inductive binary relation `empty_relation` (on numbers)
    that never holds. -/

/- LATER: MRC'20: this exercise feels unsolvable given what students
   already know.  I don't believe we've ever shown them that an
   inductive type can have zero constructors, or what the syntax for
   that would be.  (That will come when we show them how to define
   False in ProofObjects.) Should a hint be added?

   BCP 20: Maybe not needed since it's optional anyway? But also,
   can't it be done with a inductive definition with nonzero cases but
   no base case?

   APT 21: Yes, although arguably that is even less obvious.
   MRC 3/22: And also something I can't recall we've shown them.

   MRC 3/22: [unsolvable∧ optional → unsolvable]

   MTF 6/22: A solution that more than one of my students have submitted
   is using a "base" case with a built-in contradiction:
   [emp n m : 0 = 1 → empty_relation n m] or
   [emp n m : False → empty_relation n m].
   So, I do think that it is solvable given what students know.
 -/

inductive EmptyRelation : Nat → Nat → Prop where
  /- SOLUTION -/
/- /SOLUTION -/

-- TODO: @dsainati1 replace with inversion once https://github.com/plclub/sf-in-lean/issues/52 is fixed
theorem empty_relation_is_empty : ∀ n m, ¬ EmptyRelation n m := by
  /- ADMITTED -/
  intros n m contra; cases contra
/- /ADMITTED -/
/- GRADE_THEOREM 2: empty_relation_is_empty -/
/- [] -/

/- LATER:
     A nice exercise...
       - give them a datatype of binary trees
       - ask them to write a "size" function
       - make them write an inductively defined "balanced" property
       - maybe prove something about this property (this might be hard)?

    At some point, perhaps we can show them how propositions and data
    can get mixed together.  E.g., we can define a type of lists of
    numbers less than 10 (where each element carries a proof that it
    is less than 10).  Then we can go a step further and parameterize
    this definition over 10.  Similarly, we can define balanced binary
    trees of height exactly n. (See CoqArt p. 181.)  Show and discuss
    the induction principles for all of these.
-/
/- /FULL -/

/- FULL -/
/- ####################################################### -/
/- # Additional Exercises -/

/- EX3! (nostutter_defn) -/
/- Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence `[1, 4, 1]` has two occurrences of the element `1` but
    does not stutter.)  The property "`nostutter mylist`" means that
    `mylist` does not stutter.  Formulate an inductive definition for
    `nostutter`. -/

inductive NoStutter {α:Type} : List α → Prop where
 /- SOLUTION -/
  | nostutter0: NoStutter []
  | nostutter1 n : NoStutter (n::[])
  | nostutter2 a b r (hneq : a ≠ b) (h : NoStutter (b::r)) : NoStutter (a::b::r)
 /- /SOLUTION -/

/- Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  -/

example : NoStutter [3, 1, 4, 1, 5, 6] := by
/- ADMITTED -/
/- /ADMITTED -/
/- OPEN COMMENT WHEN HIDING SOLUTIONS -/
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor; intro contra; contradiction
  constructor
/- CLOSE COMMENT WHEN HIDING SOLUTIONS -/

example : NoStutter (@List.nil Nat) := by
/- ADMITTED -/
/- /ADMITTED -/
/- OPEN COMMENT WHEN HIDING SOLUTIONS -/
  constructor
/- CLOSE COMMENT WHEN HIDING SOLUTIONS -/

example :  NoStutter [5] := by
/- ADMITTED -/
/- /ADMITTED -/
/- OPEN COMMENT WHEN HIDING SOLUTIONS -/
  constructor
/- CLOSE COMMENT WHEN HIDING SOLUTIONS -/

/- LATER: AAA: The script below seems too fragile, we should probably
   change it to make it more robust. -/
example : ¬ (NoStutter [3, 1, 1, 4]) := by
/- ADMITTED -/
/- /ADMITTED -/
/- OPEN COMMENT WHEN HIDING SOLUTIONS -/
  intro contra; inversion contra with
  | nostutter2 _ contra =>
    inversion contra with
    | nostutter2 _ h _ =>
      apply h
      rfl
/- CLOSE COMMENT WHEN HIDING SOLUTIONS -/

/- GRADE_MANUAL 3: nostutter -/
/- [] -/

/- EX4A (filter_challenge) -/
/- Let's prove that our definition of `filter` from the `Poly`
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list `l` is an "in-order merge" of `l₁` and `l₂` if it contains
    all the same elements as `l₁` and `l₂`, in the same order as `l₁`
    and `l₂`, but possibly interleaved.  For example,
[[
    [1, 4, 6, 2, 3]
]]
    is an in-order merge of
[[
    [1, 6, 2]
]]
    and
[[
    [4, 3].
]]
    Now, suppose we have a set `α`, a function `test: α→bool`, and a
    list `l` of type `List α`.  Suppose further that `l` is an
    in-order merge of two lists, `l₁` and `l₂`, such that every item
    in `l₁` satisfies `test` and no item in `l₂` satisfies test.  Then
    `filter test l = l₁`.

    First define what it means for one list to be a merge of two
    others.  Do this with an `inductive` relation, not a `def`.  -/

inductive Merge {α:Type} : List α → List α → List α → Prop where
/- SOLUTION -/
  | merge_empty :
      Merge [] [] []
  | merge_left : ∀ l₁ l₂ l₃ x,
      Merge l₁ l₂ l₃ →
      Merge (x::l₁) l₂ (x::l₃)
  | merge_right : ∀ l₁ l₂ l₃ x,
      Merge l₁ l₂ l₃ →
      Merge l₁ (x::l₂) (x::l₃)
/- /SOLUTION -/


theorem merge_filter : ∀ (α : Type) (test: α→ Bool) (l l₁ l₂ : List α),
  Merge l₁ l₂ l →
  List.all l₁ (fun n => test n) →
  List.all l₂ (fun n => !test n) →
  List.filter test l = l₁ := by
  /- ADMITTED -/

  intro α test l l₁ l₂ hmerge h₁ h₂; induction hmerge
  case merge_empty => rfl
  case merge_left l₁' l₂' l₃ x h' ih =>
    rw [List.all_cons, Bool.and_eq_true] at h₁
    obtain ⟨htest, h₁⟩ := h₁
    rw [List.filter_cons, htest]; dsimp
    congr 1; apply ih
    . assumption
    . assumption
  case merge_right l₁' l₂' l₃ x h' ih =>
    rw [List.all_cons, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h₂
    obtain ⟨htest, h₂⟩ := h₂
    rw [List.filter_cons, htest]; dsimp
    congr 1; apply ih
    . assumption
    . assumption
/- /ADMITTED -/

/- HIDE -/
/- Another possible problem (perhaps for Basics.v): Write a Rocq function
   that generates the list of all in-order merges of two lists... However, the
   following isn't structurally recursive :-(
       Fixpoint all_merges {α : Type} (l₁ l₂ : List α) :=
         match (l₁,l₂) with
         | (l₁,[]) => `l₁`
         | ([],l₂) => `l₂`
         | (x1::rest1,x2::rest2) =>
              (map (fun l => cons x1 l) (all_merges rest1 l₂))
           ++ (map (fun l => cons x2 l) (all_merges l₁ rest2))
         end. -/
/- /HIDE -/

/- GRADE_THEOREM 6: merge_filter -/
/- [] -/

/- EX5A? (filter_challenge_2) -/
/- A different way to characterize the behavior of `filter` goes like
    this: Among all subsequences of `l` with the property that `test`
    evaluates to `true` on all their members, `filter test l` is the
    longest.  Formalize this claim and prove it. -/

/- SOLUTION -/
namespace Sol
/- We reproduce the definition of subseq here, in a module
    so it doesn't conflict. -/

inductive Subseq {α:Type} : List α → List α → Prop where
  | sub_nil  : ∀ l, Subseq [] l
  | sub_take : ∀ x l₁ l₂, Subseq l₁ l₂ → Subseq (x :: l₁) (x :: l₂)
  | sub_skip : ∀ x l₁ l₂, Subseq l₁ l₂ → Subseq l₁ (x :: l₂)


/- A few lemmas about subseq. -/
theorem subseq_drop_l : ∀ (α:Type) (x:α) (l₁ l₂ : List α),
  Subseq (x :: l₁) l₂ → Subseq l₁ l₂ := by

  intro α x l₁ l₂ hs; induction l₂ generalizing l₁
  case nil => inversion hs
  case cons h t ih =>
    inversion hs
    case sub_take hs =>
      constructor; assumption
    case sub_skip hs =>
      constructor; apply ih; assumption

theorem subseq_drop : ∀ (α:Type) (x:α) (l₁ l₂ : List α),
  Subseq (x :: l₁) (x :: l₂) → Subseq l₁ l₂ := by

  intro α x l₁ l₂ hs; inversion hs
  . assumption
  . apply subseq_drop_l; assumption

/- A list is _maximal_ with property `P` if it has the property, and
    every other list with the property is at most as long as it is. -/

def maximal {α:Type} (lmax : List α) (P : List α → Prop) :=
  P lmax ∧ ∀ l', P l' → l'.length ≤ lmax.length

/- A "good subsequence" for a given list `l` and a `test` is a
    subsequence of `l` all of whose members evaluate to `true` under
    the `test`. -/

def good_subseq {α:Type} (test : α → Bool) (l lsub : List α) :=
  Subseq lsub l ∧ List.all lsub test

/- Good subsequences can be extended with good elements. -/

theorem good_subseq_extend : ∀ (α:Type) (test : α → Bool)
                                  (l lsub : List α) (x : α),
  good_subseq test l lsub →
  test x →
  good_subseq test (x::l) (x::lsub) := by

  intro α test l lsub x ⟨hsub, hall⟩ hx; constructor
  . constructor; assumption
  . rw [List.all_cons, Bool.and_eq_true]; constructor
    . assumption
    . assumption

/- If `lmax` is a maximal good subsequence of `x :: l` and `x` is not good,
    then `lmax` is also a maximal good subsequence of `l`. -/
theorem maximal_strengthening : ∀ (α:Type) (x:α)
                                     (lmax l : List α)
                                     (test : α → Bool),
  maximal lmax (good_subseq test (x::l)) →
  !(test x) →
  maximal lmax (good_subseq test l) := by

  intro α x lmax l test ⟨⟨hsub, hall⟩, hlen⟩ hx; constructor; constructor
  . inversion hsub
    case sub_nil => constructor
    case sub_take l₁ hsub =>
      rw [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨ht, _⟩ := hall
      rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hx
      rw [hx] at ht; contradiction
    case sub_skip => assumption
  . assumption
  . intro l ⟨hsub', hall'⟩; apply hlen; constructor
    . constructor; assumption
    . assumption


/- Some easy lemmas about filter: its result is a good subsequence of
    the original list. -/

theorem filter_subseq : ∀ (α:Type) (l : List α) (test : α → Bool),
  Subseq (List.filter test l) l := by

  intros α l test; induction l
  case nil => rw [List.filter_nil]; constructor
  case cons hd tl ih =>
    rw [List.filter_cons]; cases (test hd)
    . dsimp [Bool.false_eq_true]
      constructor; assumption
    . dsimp; constructor; assumption

theorem filter_all : ∀ (α:Type) (l : List α) (test : α → Bool),
  List.all (List.filter test l) test := by

  intro α l test; induction l
  case nil => rfl
  case cons hd tl ih =>
    rw [List.filter_cons]; cases h : (test hd)
    . dsimp [Bool.false_eq_true]; assumption
    . dsimp; rw [Bool.and_eq_true]; constructor
      . assumption
      . assumption

/- And now for the main theorem: `lsub` is a maximal good subsequence
    of `l` if and only if `filter test l = lsub` -/
/- LATER: This could use a lot of cleanup... -/

theorem filter_spec2 : ∀ (α:Type) (l lsub:List α) (test : α → Bool),
  maximal lsub (good_subseq test l) ↔ List.filter test l = lsub := by

  intro α l lsub test; apply Iff.intro
  . induction l generalizing lsub
    case nil =>
      intro ⟨⟨hsub, hall⟩, hlen⟩
      inversion hsub
      rw [List.filter_nil]
    case cons hd tl ih =>
      rw [List.filter_cons]
      cases htest : test hd
      case false =>
        dsimp [Bool.false_eq_true]
        intro hmax; apply ih
        apply maximal_strengthening _ _ _ _ _ hmax
        rw [Bool.not_eq_eq_eq_not, Bool.not_true]
        assumption
      case true =>
        intro ⟨⟨hsub, hall⟩, hlen⟩; dsimp
        /- in this case, lsub must begin with hd, since otherwise it
        wouldn't be maximal. -/
        cases lsub
        case nil => -- lsub = [] (impossible: contradicts maximality of lsub)
          have contra : [hd].length ≤ ([] : List α).length := by
            apply hlen; constructor
            . constructor; constructor
            . rw [List.all_cons, List.all_nil, Bool.and_true]; assumption
          contradiction
        case cons hd' tl' =>
          have heq : hd = hd' := by -- because of maximality again
            inversion hsub
            case sub_take hsub => rfl
            case sub_skip hsub =>
            -- contradiction, since hd :: hd' :: tl' would be longer
              have contra : (hd :: hd' :: tl').length ≤ (hd' :: tl').length := by
                apply hlen; constructor
                . constructor; assumption
                . rw [List.all_cons, List.all_cons, Bool.and_eq_true, Bool.and_eq_true]
                  rw [List.all_cons, Bool.and_eq_true] at hall
                  constructor; assumption; assumption
              rw [List.length_cons, List.length_cons, Nat.add_le_add_iff_right] at contra
              apply Nat.not_add_one_le_self at contra
              contradiction
          subst heq; congr; apply ih; constructor; constructor
          . exact subseq_drop _ hd _ _ hsub
          . rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall; assumption
          . intro l' hgood; rw [List.length_cons] at hlen
            apply succ_n_le_succ_m__n_le_m
            apply hlen (hd :: l')
            exact good_subseq_extend _ _ _ _ _ hgood htest
  . intro hfilter; constructor; rw [←hfilter]; constructor
    . apply filter_subseq
    . apply filter_all
    . intro l' ⟨hsub, hall⟩; induction l generalizing l' lsub
      case nil =>
        inversion hsub; dsimp
        apply zero_le_n
      case cons hd tl ih =>
        rw [List.filter_cons] at hfilter
        cases htest : test hd
        case false =>
          rw [htest] at hfilter; dsimp [Bool.false_eq_true] at hfilter
          apply ih _ hfilter _ _ hall; inversion hsub
          case sub_nil => constructor
          case sub_take l hsub =>
            rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨ht, _⟩ := hall
            rw [ht] at htest
            contradiction
          case sub_skip hsub => assumption
        case true =>
          rw [←hfilter, htest]; dsimp; inversion hsub
          case sub_nil =>
            dsimp; apply zero_le_n
          case sub_take l hsub =>
            rw [List.length_cons]; apply n_le_m__succ_n_le_succ_m
            apply ih _ rfl _ hsub
            rw [List.all_cons, Bool.and_eq_true] at hall
            obtain ⟨_, _⟩ := hall
            assumption
          case sub_skip hsub =>
            apply Nat.le_succ_of_le
            exact ih _ rfl _ hsub hall
end Sol
/- /SOLUTION -/
/- [] -/

/- EX4? (palindromes) -/
/- A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition `Pal` on `List α` that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.

    - Prove (`pal_app_reverse`) that
[[
       ∀ l, pal (l ++ l.reverse).
]]
    - Prove (`pal_reverse` that)
[[
       ∀ l, pal l → l = l.reverse.
]]

    For extra credit, try proving the same theorems with an alternate
    definition with a _single_ constructor of this type:
[[
        ∀ l, l = l.reverse → pal l
]]
-/

/- HIDE: MTF 6/22: It isn't exactly clear why the single constructor approach
   "will not work very well".  It seems to work extremely well:

    inductive pal {α:Type} : List α → Prop :=
      | palc : forall l, l = rev l → pal l.

    theorem pal_app_reverse : forall (α:Type) (l : List α),
      pal (l ++ (rev l)).
    Proof.
      intros α l.
      apply palc.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      reflexivity.
    Qed.

    theorem pal_reverse : forall (α:Type) (l: List α) , pal l → l = rev l.
    Proof.
      intros α l H. destruct H. assumption.
    Qed.

    theorem palindrome_converse: forall {α: Type} (l: List α), l = rev l → pal l.
    Proof.
      intros α l H. apply palc. assumption.
    Qed.

      This seems to be yet another example of a property that can be expressed as a
      non-inductive proposition being artificially formulated as an inductive
      proposition.  Are there any other properties of the [palindrome] proposition
      that would be difficult to prove from its specification?

   BCP 25: Took away the "will not work very well" wording. -/

inductive Pal {α:Type} : List α → Prop where
/- SOLUTION -/
  | pal_nil : Pal []
  | pal_one : ∀ x, Pal [x]
  | pal_consnoc : ∀ x l, Pal l → Pal (x::(l++[x]))
/- /SOLUTION -/


/- LATER: APT21: a student noted that the pal_one case is easy to
   miss, since the theorems don't require it! BCP 25: We could fix
   that by adding some examples, e.g. [], [1], and [1,1]. -/

theorem pal_app_reverse : ∀ (α:Type) (l : List α),
  Pal (l ++ l.reverse) := by
  /- ADMITTED -/
  intro α l; induction l
  case nil => rw [List.reverse_nil, List.append_nil]; constructor
  case cons hd tl ih =>
    rw [List.reverse_cons, List.cons_append, ←List.append_assoc]
    constructor; assumption
/- /ADMITTED -/
/- GRADE_THEOREM 3: pal_app_reverse -/

/- LATER: Note that we're using some standard library stuff here...
   We should at least explicitly qualify them... -/
theorem pal_reverse : ∀ (α:Type) (l: List α) , Pal l → l = l.reverse := by


  /- ADMITTED -/
  intro α l hp; induction hp
  case pal_nil => rw [List.reverse_nil]
  case pal_one x =>
    rw [List.reverse_cons, List.reverse_nil, List.nil_append]
  case pal_consnoc x l hp ih =>
    rw [List.reverse_cons, List.reverse_append, ←List.cons_append, ←ih]
    congr
/- GRADE_THEOREM 3: pal_reverse -/
/- [] -/

/- TODO: (DHS) This one is super annoying without simp.
   I propose we move it to the simp chapter -/
/- EX5? (palindrome_converse) -/
/- Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of `Pal` from the
    previous exercise, prove that
[[
     ∀ l, l = l.reverse → Pal l.
]]
-/

/- QUIETSOLUTION -/
/- Proving the converse theorem is much harder, because a standard
    induction over the list `l` doesn't work.  The trick to the
    following proof, due to Nathan Collins, is to induct over _half
    the length_ of `l`.  We make heavy use of destruct and inversion
    to clear away the impossible cases. -/

theorem reverse_pal: ∀ {α: Type} (n: Nat) (l:List α ),
  l.length / 2 = n → l = l.reverse → Pal l := by

  intros α n l hlen hrev
  induction n generalizing l
  /- (length l) / 2 = 0 || l has length 0 or 1 -/
  case zero =>
    cases l
    case nil => constructor
    case cons _ l =>
      cases l
      case nil =>
        constructor
      case cons _ _ l' =>
        /- impossible : l has length > 1 -/
        rw [List.length_cons, List.length_cons] at hlen
        rw [Nat.div_eq_zero_iff] at hlen
        cases hlen; contradiction; contradiction
  /- (length l) / 2 >= 1  || l has length at least 2 -/
  case succ n ih =>
  cases l
  case nil => rw [List.length_nil, Nat.zero_div] at hlen; contradiction
  case cons x l =>
    rw [List.length_cons] at hlen
    rw [List.reverse_cons] at hrev
    cases heq : l.reverse
    case nil =>
      have h : l = [] := by
        cases l; rfl
        simp only [List.reverse_cons, List.append_eq_nil_iff] at heq
        obtain ⟨_, _⟩ := heq; contradiction
      rw [h]; constructor
    case cons y l' =>
      rw [heq] at hrev
      injections hrev heqtl; subst hrev
      rw [heqtl, List.append_eq]
      constructor; apply ih
      . rw [heqtl] at hlen
        rw [List.append_eq, List.length_append, List.length_cons,
          List.length_nil, Nat.zero_add] at hlen
        omega
      . rw [heqtl, List.append_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, List.nil_append] at heq
        injections _ _
        symm
        assumption


/- And here's another solution due (modulo some fixes by BCP/AAA to
   replace snoc with app) to Michael Schulman. It uses a few tactics
   that we haven't seen yet.

theorem eqrev_pal_gen (α : Type) : forall (l:List α) (p t:List α),
  l = p ++ t → p = rev p → pal p.
Proof.
 induction l as [| x l'].
 - /- l = nil -/
   destruct p.
   + /- p = nil -/
     destruct t as [| x t'].
        * /- t = nil -/
          intros; constructor.
        * /- t = cons -/
          intros H; inversion H.
   + /- p = cons -/
     intros t H.
     inversion H.
 - /- l = cons -/
   destruct p as [| y p'].
   + /- p = nil -/
     intros. constructor.
   + /- p = cons -/
     intros t H K.
     inversion H.
     simpl in K.
     destruct (rev p') as [| z p''] eqn:Heqrevp'.
     * /- rev p' = nil -/
       destruct p' as [| w q].
       { /- p' = nil -/ constructor. }
       { /- p' = cons -/
         assert (L : [] = w :: q).
         { rewrite <- rev_involutive. rewrite  Heqrevp'. reflexivity. }
         inversion L. }
     * /- rev p' = cons -/
       assert (M : rev (rev p') = (rev p'') ++ [z]).
       { rewrite Heqrevp'. reflexivity. }
       rewrite rev_involutive in M.
       rewrite M.
       inversion K.
       /- Now we finally get to do -/
       constructor.
       apply (IHl' _ (z :: t)).
       { /- l' = rev p'' ++ z :: t -/
         rewrite h₂. rewrite M. rewrite <- app_assoc. reflexivity. }
       { /- rev p'' = rev (rev p'') -/
         rewrite H4 in Heqrevp'. rewrite rev_app_distr in Heqrevp'.
         inversion Heqrevp'.
         rewrite rev_involutive.
         symmetry. apply H5. } Qed.

theorem eqrev_pal (α : Type) (l:List α) : (l = rev l) → pal l.
Proof.
  intros H.
  apply (eqrev_pal_gen _ l l []).
  rewrite app_nil_r. reflexivity.
  apply H.
Qed.

/- A final possibility is adding a natural number n and a hypothesis
   "length l ≤ n" and inducting on n.  The following solution by
   Mihir Mehta follows this strategy... -/

theorem palindrome_converse_lemma_1:
  forall {α: Type} (l: List α), length (rev l) = length l.
Proof. {
  intros α. induction l.
  { reflexivity. }
  { simpl. rewrite → app_length. rewrite → IHl. simpl.
    rewrite → add_comm. reflexivity. }
} Qed.

theorem palindrome_converse_lemma_2:
  forall {α: Type} (n: nat) (l: List α), (length l ≤ n) → l = rev l → pal l.
Proof. {
  intros α. induction n as [| n'].
  { /- n = 0 -/
    intros [| x l'] h₁ h₂.
    { /- l = [] -/ apply pal_nil. }
    { /- l = x :: l' -/ inversion h₁. }
  }
  { /- n = S n'-/
    intros [| x l'] h₃ H4.
    { /- l = [] -/ apply pal_nil. }
    { /- l = x :: l' -/
      simpl in H4.
      destruct (rev l') as [| x' l''] eqn:H5.
      { /- rev l = [] -/
        rewrite <- (rev_involutive α l'). rewrite → H5. simpl.
        apply pal_one. }
      { /- rev l = x' :: l'' -/
        inversion H4 as [[H6 H7]]. apply pal_consnoc. apply (IHn' l'').
        { /- proving: length l'' ≤ n' -/
          rewrite → H7 in h₃. simpl in h₃.
          rewrite → app_length in h₃. simpl in h₃.
          rewrite → add_comm in h₃. simpl in h₃.
          apply Sn_le_Sm__n_le_m, Sn_le_Sm__n_le_m.
          apply le_S. apply h₃.
        }
        { /- proving l'' = rev l'' -/
          rewrite → H7 in H5. rewrite → rev_app_distr in H5. simpl in H5.
          inversion H5 as [H8]. rewrite → H8, → H8. reflexivity.
        }
      }
    }
  }
} Qed. -/
/- /QUIETSOLUTION -/

theorem palindrome_converse: ∀ {α: Type} (l: List α),
    l = l.reverse → Pal l := by
  /- ADMITTED -/
  intros α l h
  exact reverse_pal _ _ rfl h
  /- /ADMITTED -/
/- [] -/

/- EX4A? (NoDup) -/

/- Use the `∈` property to define a proposition `disjoint α l₁ l₂`,
    which should be provable exactly when `l₁` and `l₂` are
    lists (with elements of type α) that have no elements in
    common. -/

/- SOLUTION -/
def disjoint {α:Type} (l₁ l₂: List α) :=
  ∀ (x:α), x ∈ l₁ → ¬ x ∈ l₂
/- /SOLUTION -/

/- Next, use `∈` to define an inductive proposition [NoDup α
    l], which should be provable exactly when `l` is a list (with
    elements of type `α`) where every member is different from every
    other.  For example, `NoDup Nat [1, 2, 3,  4]` and `NoDup Bool []`
    should be provable, while [NoDup Nat [1, 2, 1]] and
    `NoDup Bool [true, true]` should not be.  -/

/- SOLUTION -/
inductive NoDup {α:Type} : List α → Prop where
  | NoDup_nil : NoDup []
  | NoDup_cons : ∀ a l,
              ¬ a ∈ l →
              NoDup l →
              NoDup (a::l)
/- /SOLUTION -/

/- Finally, state and prove one or more interesting theorems relating
    `disjoint`, `NoDup` and `++` (list append).  -/

/- SOLUTION -/
/- Here are some possible answers: -/

theorem NoDup_append : ∀ (α:Type) (l₁ l₂: List α),
  NoDup l₁ → NoDup l₂ → disjoint l₁ l₂ →
  NoDup (l₁ ++ l₂) := by

  intros α l₁ l₂ h₁ h₂ hdis
  induction l₁ generalizing l₂
  case nil => rw [List.nil_append]; assumption
  case cons hd tl ih =>
    constructor
    . intro contra; rw [List.append_eq, List.mem_append] at contra
      rcases contra with contra | contra
      . inversion h₁
        case _ hdup hin =>
        apply hin; assumption
      . apply hdis hd _ contra
        rw [List.mem_cons]; left; rfl
    . apply ih _ _ h₂ _
      . inversion h₁; assumption
      . intros x hin
        apply hdis; rw [List.mem_cons]
        right; assumption

theorem NoDup_disjoint : ∀ (α:Type) (l₁ l₂: List α),
  NoDup (l₁++l₂) → disjoint l₁ l₂ := by

  intro α l₁ l₂ hdis x hin contra
  induction l₁ generalizing l₂ x
  case nil => rw [List.mem_nil_iff] at hin; contradiction
  case cons hd tl ih =>
    rw [List.mem_cons] at hin
    inversion hdis
    case NoDup_cons hdup hnotin =>
      rcases hin with hin | hin
      . subst hin; apply hnotin
        rw [List.append_eq, List.mem_append]; right; assumption
      . exact ih _ hdup _ hin contra

/- We can also show the following results about [NoDup] and [++]
   by themselves -/
theorem NoDup_left : ∀ (α:Type) (l₁ l₂: List α),
  NoDup (l₁++l₂) → NoDup l₁ := by

  intro α l₁ l₂ hdup
  induction l₁ generalizing l₂
  case nil => constructor
  case cons hd tl ih =>
    inversion hdup
    case _ hdup' hin =>
      constructor
      . intro contra; apply hin
        rw [List.append_eq, List.mem_append]; left; assumption
      . exact ih _ hdup'

theorem NoDup_right: ∀ (α:Type) (l₁ l₂: List α),
  NoDup (l₁++l₂) → NoDup l₂ := by

  intro α l₁ l₂ hdup
  induction l₁ generalizing l₂
  case nil => rw [List.nil_append] at hdup; assumption
  case cons hd tl ih =>
    inversion hdup
    apply ih; assumption

/- This theorem combines the various lemmas to give a complete
   characterization -/
theorem NoDup_disjoint_app : ∀ {α:Type} (l₁ l₂: List α),
  NoDup (l₁++l₂) ↔
  (NoDup l₁ ∧ NoDup l₂ ∧ disjoint l₁ l₂) := by

  intro α l₁ l₂; apply Iff.intro
  . intro hdup
    constructor; exact NoDup_left _ _ _ hdup
    constructor; exact NoDup_right _ _ _ hdup
    exact NoDup_disjoint _ _ _ hdup
  . intro ⟨h₁, ⟨h₂, h₃⟩⟩
    exact NoDup_append _ _ _ h₁ h₂ h₃
/- /SOLUTION -/

/- GRADE_MANUAL 6: NoDup_disjoint_etc -/
/- [] -/

/- EX5A? (pigeonhole_principle) -/
/- GRADE_THEOREM 2: in_split -/
/- GRADE_THEOREM 6: pigeonhole_principle -/
/- The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than `n` items into `n` pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... -/

/- First prove an easy and useful lemma. -/

theorem mem_split : ∀ (α:Type) (x:α) (l:List α),
  x ∈ l →
  ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  /- ADMITTED -/
  intro α x l hin
  induction l generalizing x
  case nil => rw [List.mem_nil_iff] at hin; contradiction
  case cons hd tl ih =>
    rw [List.mem_cons] at hin; rcases hin with hin | hin
    . subst hin; exists []; exists tl
    . have ⟨l₁', ⟨l₂', ih⟩⟩ := ih x hin
      subst ih
      exists hd :: l₁'; exists l₂'
/- /ADMITTED -/

/- Now define a property `repeats` such that `repeats α l` asserts
    that `l` contains at least one repeated element (of type `α`).  -/

inductive Repeats {α:Type} : List α → Prop where
  /- SOLUTION -/
  | rep_here : ∀ a l, a ∈ l → Repeats (a::l)
  | rep_later : ∀ a l, Repeats l → Repeats (a::l)
/- /SOLUTION -/


/- GRADE_MANUAL 2: check_repeats -/

/- Now, here's a way to formalize the pigeonhole principle.  Suppose
    list `l₂` represents a list of pigeonhole labels, and list `l₁`
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list `l₁` must contain repeats.

    This proof is much easier if you use the excluded middle
    to show that `∈` is decidable, i.e., `∀ x l, (x ∈ l) \/ ~ (x ∈ l)`.
    Remember the `by_cases` tactic from Logic! -/
/- HIDE: APT21: Apparently, this is really quite hard; even the strongest
   students couldn't do it this year. -/
theorem pigeonhole_principle:
  ∀ (α:Type) (l₁  l₂:List α),
  (∀ x, x ∈ l₁ → x ∈ l₂) →
  l₂.length < l₁.length →
  Repeats l₁ := by
  /- ADMITTED -/
  intros α l₁ l₂ hin hlen
  induction l₁ generalizing l₂
  case nil =>
    rw [List.length_nil] at hlen
    apply Nat.not_lt_zero at hlen
    contradiction
  case cons x l₁' ih =>
    by_cases h : x ∈ l₁'
    . constructor; assumption
    . apply Repeats.rep_later
      have h₂ : x ∈ l₂ := by
        apply hin; rw [List.mem_cons]; left; rfl
      have ⟨l₂a, ⟨l₂b, heq⟩⟩ := mem_split _ _ _ h₂
      have hin₂ : ∀ x' : α, x' ∈ l₁' -> x' ∈ (l₂a ++ l₂b) := by
        intro x₀ hin₀
        have hneq : x ≠ x₀ := by
          intro heq; subst heq; apply h; assumption
        have h₁ : x₀ ∈ l₂ := by
          apply hin; rw [List.mem_cons]; right; assumption
        rw [heq, List.mem_append] at h₁; rcases h₁ with h₁ | h₁
        . rw [List.mem_append]; left; assumption
        . rw [List.mem_append]; right;
          rw [List.mem_cons] at h₁; rcases h₁ with h₁ | h₁
          . subst h₁; contradiction
          . assumption
      have hlen₂ : (l₂a ++ l₂b).length < l₁'.length := by
        have hlen' : l₂.length = (l₂a ++ l₂b).length + 1 := by
          rw [heq, List.length_append, List.length_append, List.length_cons, Nat.add_assoc]
        rw [hlen', List.length_append, List.length_cons] at hlen
        rw [List.length_append]
        apply succ_n_le_succ_m__n_le_m
        exact hlen
      apply ih (l₂a ++ l₂b) hin₂ hlen₂
  /-.
      destruct (EM (In x l1')) as [H | H].
      + /- In x l1' -/
        apply rep_here. apply H.
      + /- ~ In x l1' -/
        apply rep_later.
        assert (INX: In x l₂).
        {  apply INC. left. reflexivity. }
        destruct (in_split _ _ _ INX) as [l2a [l2b EQ]].
        remember (l2a ++ l2b) as l2' eqn:Heql2'.
        assert (IN2: forall x0 : α, In x0 l1' → In x0 l2').
        { intros x0 AI.
          assert (H0: x <> x0).
          { intros Heq. apply H. rewrite  Heq. apply AI. }
          assert (h₁: In x0 l₂).
          { apply INC. simpl. right. apply AI. }
          rewrite EQ in h₁. apply In_app_iff in h₁.
          rewrite Heql2'. apply In_app_iff.
          simpl in h₁. destruct h₁ as [h₁ | [h₁ | h₁]].
          - left. apply h₁.
          - exfalso. apply H0. apply h₁.
          - right. apply h₁.  }
        assert (LEN2: length l2' < length l1').
        { assert (LS: length l₂ = S(length (l2a ++ l2b))).
          { rewrite EQ.
            rewrite app_length. rewrite app_length. rewrite add_comm.
            simpl. rewrite add_comm. reflexivity. }
          rewrite LS in NR. rewrite <- Heql2' in NR. simpl in NR.
          apply Sn_le_Sm__n_le_m.  apply NR.
        }
        apply (IHl1' l2' IN2 LEN2).
Qed. -/
/- /ADMITTED -/
/- LATER: A student came up with

Definition repeats {α} (xs: List α) : Prop :=
  exists x ps qs rs,  xs = ps ++ [x] ++ qs ++ [x] ++ rs.
Should check to see how much harder this makes things.
-/
/- [] -/

/- QUIETSOLUTION -/
/-
    /- Here's a clever alternative proof, based heavily on one by Daniel
        Schepler (<dschepler@gmail.com> Coq club mailing list on Wed, 02 Oct
        2013 02:02:12 -0700), that doesn't use decidability of [In], and hence
        doesn't need [excluded_middle]. -/

    /- First, some more auxiliary lemmas, some of which are a bit ad hoc. -/

    theorem in_repeats: forall {α:Type} (l₁ l₂:List α) (x:α),
      In x (l₁++l₂) →
      repeats (l₁++x::l₂).
    Proof.
      intros α l₁. induction l₁ as [|y l1' IHl1'].
      - /- l₁ = [] -/
        intros l₂ x AI. simpl in AI. simpl. apply rep_here. apply AI.
      - /- l₁ = y::l1' -/
        intros l₂ x AI. simpl in AI. simpl. destruct AI as [AI | AI].
        + apply rep_here. apply In_app_iff. right. left.
          rewrite AI. reflexivity.
        + apply rep_later. apply IHl1'. apply AI.
    Qed.

    theorem rep_insert: forall {α:Type} (l₁ l₂:List α) (x: α),
      repeats (l₁ ++ l₂) → repeats (l₁ ++ x::l₂).
    Proof.
      intros α l₁. induction l₁ as [| y l1' IHl1'].
      - /- l₁ = [] -/
        intros l₂ x H. simpl. simpl in H. apply rep_later.  apply H.
      - /- l₁ = y::l1' -/
        intros l₂ x H. simpl. simpl in H. inversion H.
        + /- rep_here -/
          apply rep_here. apply In_app_iff. apply In_app_iff in h₁.
          destruct h₁ as [h₁ | h₁].
          * left. apply h₁.
          * right. right. apply h₁.
        + /- rep_later -/
          apply rep_later. apply IHl1'. apply h₁.
    Qed.

    theorem repeats_app_comm : forall {α:Type} (l₁ l₂:List α),
      repeats (l₁++l₂) → repeats(l₂++l₁).
    Proof.
      intros α l₁. induction l₁ as [|x l1'].
      - /- l₁ = [] -/
        intros l₂ H.  rewrite app_nil_r. simpl in H. apply H.
      - /- l₁ = x::l1' -/
        intros l₂ H. simpl in H. inversion H.
        + /- rep_here -/
          apply in_repeats. apply In_app_iff.
          apply In_app_iff in h₁.
          destruct h₁ as [h₁ | h₁].
          * right. apply h₁.
          * left. apply h₁.
        + /- rep_later -/
          apply IHl1' in h₁. apply rep_insert. apply h₁.
    Qed.

    /- Now the main lemma: -/

    theorem pigeonhole_principle_aux: forall {α:Type} (l₁ l₂ ls: List α),
      (forall x:α, In x l₁ → In x (ls++l₂)) →
      length l₂ < length l₁ → repeats (ls++l₁).
    Proof.
      intros α l₁. induction l₁ as [|x l1' IHl1'].
      - /- l₁ = [] -/
        intros l₂ ls AI LT. inversion LT.
      - /- l₁ = x::l1' -/
        intros l₂ ls AI LT.
        assert (In x (ls++l₂)).
        { /- Proof of assertion -/
          apply AI. left. reflexivity. }
        assert (In x ls \/ In x l₂).
        { /- Proof of assertion -/
          apply In_app_iff. apply H. }
        destruct H0.
        + /- In x ls -/
          apply repeats_app_comm. simpl. apply rep_here.
          apply In_app_iff. right. apply H0.
        + /- In x l₂ -/
          apply in_split in H0.
          destruct H0 as [l2a [l2b P]]. rewrite P in *.
          assert (repeats ((x::ls) ++ l1')).
          * /- Proof of assertion -/
            apply (IHl1' (l2a++l2b) (x::ls)).
            { /- re-establish inclusion relation -/
              intros x0 AI'.
              assert (In x0 (ls ++ l2a ++ x::l2b)).
              { /- Proof of assertion -/
                apply AI. right. apply AI'. }
              apply In_app_iff in H0. inversion H0.
                apply In_app_iff.  left. right. apply h₁.
                apply In_app_iff in h₁. inversion h₁.
                  apply In_app_iff. right.
                    apply In_app_iff. left. apply h₂.
                  inversion h₂.
                    simpl. left. apply h₃.
                    apply In_app_iff. right.
                      apply In_app_iff. right. apply h₃. }
            rewrite app_length in LT.  rewrite app_length.
            simpl in LT. rewrite <- plus_n_Sm in LT.
            unfold lt. unfold lt in LT. apply le_S_n. apply LT.
          * simpl in H0. apply repeats_app_comm. simpl. inversion H0.
            { apply rep_here. apply In_app_iff.
              apply In_app_iff in h₂. inversion h₂.
              - right. apply H4.
              - left. apply H4. }
            apply rep_later. apply repeats_app_comm. apply h₂.
    Qed.

    theorem stronger_pigeonhole_principle: forall {α:Type} (l₁ l₂ : List α),
      (forall x : α, In x l₁ → In x l₂) →
      length l₂ < length l₁ →
      repeats l₁.
    Proof.
      intros α l₁ l₂ AI LT.
      assert (H: l₁ = nil ++ l₁). { reflexivity. }
      rewrite H. apply (pigeonhole_principle_aux l₁ l₂ nil).
      simpl. apply AI. apply LT.
    Qed.

    /- One key to how this proof works is that at the inductive step,
        when we re-establish the inclusion relation, the contents on the
        list on the right-hand side of the inclusion have not changed at
        all---they are merely re-arranged, so validity of the inclusion is
        trivial (modulo some messy book-keeping). Compare this to the
        equivalent step in the original proof, where we remove [x] from the
        list on the right-hand side of the inclusion; this is only valid when
        we know that [x] is not in the left-hand list [l1'] either---exactly
        the knowledge that we get from decidability of [In], and cannot get
        any other way. -/

    /- ------------------------ -/

    /- Finally, here is a much more elegant proof due to N. Raghavendra
        <raghu@hri.res.in>, based on Daniel's.  It uses the following
        sequence of observations:

          theorem app_ass :
          forall (α : Type) (l₁ l₂ l₃ : List α),
            (l₁ ++ l₂) ++ l₃ = l₁ ++ l₂ ++ l₃.

          theorem app_length :
          forall (α : Type) (l₁ l₂ : List α),
            length (l₁ ++ l₂) = length l₁ + length l₂.

          theorem In_app_iff_split :
          forall (α : Type) (x : α) (l : List α),
            In x l →
            exists (l₁ l₂ : List α), l = l₁ ++ x :: l₂.

          theorem In_both_impl_repeats_app :
          forall (α : Type) (x : α) (l₁ l₂ : List α),
            In x l₁ → In x l₂ → repeats (l₁ ++ l₂).

          theorem In_app_iff_midswap :
          forall (α : Type) (x : α) (l₁ l₂ l₃ l4 : List α),
            In x (l₁ ++ l₂ ++ l₃ ++ l4) →
            In x (l₁ ++ l₃ ++ l₂ ++ l4).

          theorem pigeonhole_principle_aux :
          forall (α : Type) (l₁ l₂ u : List α),
            (forall x : α, In x l₁ → In x (u ++ l₂)) →
            length l₂ < length l₁ → repeats (u ++ l₁).

          theorem pigeonhole_principle :
          forall (α : Type) (l₁ l₂ : List α),
            (forall x : α, In x l₁ → In x l₂) →
            length l₂ < length l₁ → repeats l₁.
    -/

    /- HIDE: Some of these are already proved elsewhere. Also, this
      vertical style is hard to read. -/

    Module Pigeon.

    inductive repeats {α : Type} : List α → Prop :=
      | repeats_1 (x : α) (l : List α)
                  (H : In x l) : repeats (x :: l)
      | repeats_2 (x : α) (l : List α)
                  (H : repeats l) : repeats (x :: l).

    Definition pigeonhole_principle_prop (α : Type) : Prop :=
      forall l₁ l₂ : List α,
        (forall x : α, In x l₁ → In x l₂) →
        length l₂ < length l₁ → repeats l₁.

    theorem app_ass :
      forall (α : Type) (l₁ l₂ l₃ : List α),
        (l₁ ++ l₂) ++ l₃ = l₁ ++ l₂ ++ l₃.

    Proof.
      intros α l₁ l₂ l₃.
      induction l₁ as [ | h t IH].
      {
        - /- l₁ = nil -/
        reflexivity.
      }
      {
        - /- l₁ = h :: t -/
        simpl.
        rewrite → IH.
        reflexivity.
      }
    Qed.

    theorem app_length :
      forall (α : Type) (l₁ l₂ : List α),
        length (l₁ ++ l₂) = length l₁ + length l₂.

    Proof.
      intros α l₁ l₂.
      induction l₁ as [ | h t IH].
      {
        - /- l₁ = nil -/
        reflexivity.
      }
      {
        - /- l₁ = h :: t -/
        simpl.
        rewrite → IH.
        reflexivity.
      }
    Qed.

    theorem In_both_impl_repeats_app :
      forall (α : Type) (x : α) (l₁ l₂ : List α),
        In x l₁ → In x l₂ → repeats (l₁ ++ l₂).

    Proof.
      intros α x l₁.
      induction l₁ as [ | h₁ t1 IH].
      {
        - /- l₁ = nil -/
        intros l₂ h₁ h₂.
        inversion h₁.
      }
      {
        - /- l₁ = h₁ :: t1 -/
        intros l₂ h₁ h₂. simpl in h₁.
        destruct h₁ as [h₃ | h₃].
        {
          +
          simpl.
          apply repeats_1.
          apply In_app_iff.
          right.
          rewrite h₃.
          apply h₂.
        }
        {
          + /- h₁ = ai_later z u h₃ -/
          simpl.
          apply repeats_2.
          apply IH.
          {
            apply h₃.
          }
          {
            apply h₂.
          }
        }
      }
    Qed.

    theorem In_app_iff_midswap :
      forall (α : Type) (x : α) (l₁ l₂ l₃ l4 : List α),
        In x (l₁ ++ l₂ ++ l₃ ++ l4) → In x (l₁ ++ l₃ ++ l₂ ++ l4).

    Proof.
      intros α x l₁ l₂ l₃ l4 H.
      apply In_app_iff in H.
      destruct H as [h₁ | h₁r].
      {
        - /- In x l₁ -/
        apply In_app_iff.
        left.
        apply h₁.
      }
      {
        - /- In x (l₂ ++ l₃ ++ l4) -/
        apply In_app_iff in h₁r.
        destruct h₁r as [h₂ | h₂r].
        {
          + /- In x l₁ -/
          apply In_app_iff.
          right.
          apply In_app_iff.
          right.
          apply In_app_iff.
          left.
          apply h₂.
        }
        {
          + /- In x (l₃ ++ l4) -/
          apply In_app_iff in h₂r.
          destruct h₂r as [h₃ | h₃r].
          {
            * /- In x l₃ -/
            apply In_app_iff.
            right.
            apply In_app_iff.
            left.
            apply h₃.
          }
          {
            * /- In x l4 -/
            apply In_app_iff.
            right.
            apply In_app_iff.
            right.
            apply In_app_iff.
            right.
            apply h₃r.
          }
        }
      }
    Qed.

    theorem pigeonhole_principle_aux :
      forall (α : Type) (l₁ l₂ u : List α),
        (forall x : α, In x l₁ → In x (u ++ l₂)) →
        length l₂ < length l₁ → repeats (u ++ l₁).

    Proof.
      intros α l₁.
      induction l₁ as [ | h₁ t1 IH].
      {
        - /- l₁ = nil -/
        intros l₂ u h₁ h₂.
        inversion h₂.
      }
      {
        - /- l₁ = h₁ :: t1 -/
        intros l₂ u h₁ h₂.
        assert (h₃ : In h₁ (u ++ l₂)).
        {
          + /- Proof of h₃ -/
          apply h₁.
          left. reflexivity.
        }
        apply In_app_iff in h₃.
        destruct h₃ as [h₃l | h₃r].
        {
          + /- In h₁ u -/
          apply (In_both_impl_repeats_app _ h₁).
          {
            apply h₃l.
          }
          {
            left. reflexivity.
          }
        }
        {
          + /- In h₁ l₂ -/
          apply in_split in h₃r.
          destruct h₃r as [v2 H4].
          destruct H4 as [w2 H5].
          assert (H6 : u ++ h₁ :: t1 = (u ++ [h₁]) ++ t1).
          {
            * /- Proof of H6 -/
            rewrite → app_ass.
            reflexivity.
          }
          rewrite → H6.
          apply (IH (v2 ++ w2)).
          {
            * /- Proof of first condition of IH -/
            intros x H7.
            rewrite → app_ass.
            apply In_app_iff_midswap.
            simpl.
            rewrite <- H5.
            apply h₁.
            right.
            apply H7.
          }
          {
            * /- Proof of second condition of IH -/
            unfold lt.
            assert (H8 : length l₂ = S (length (v2 ++ w2))).
            {
              rewrite → H5.
              rewrite → app_length.
              rewrite → app_length.
              simpl.
              rewrite <- plus_n_Sm.
              reflexivity.
            }
            rewrite <- H8.
            apply Sn_le_Sm__n_le_m.
            unfold lt in h₂.
            simpl in h₂.
            apply h₂.
          }
        }
      }
    Qed.

    theorem pigeonhole_principle :
      forall α : Type,
        pigeonhole_principle_prop α.

    Proof.
      intros α.
      unfold pigeonhole_principle_prop.
      intros l₁ l₂ h₁ h₂.
      assert (H: l₁ = nil ++ l₁). { reflexivity. }
      rewrite H.
      apply (pigeonhole_principle_aux _ _ l₂).
      {
        intros x h₃.
        simpl.
        apply h₁.
        apply h₃.
      }
      {
        apply h₂.
      }
    Qed.

    End Pigeon.
-/
/- /QUIETSOLUTION -/
/- /FULL -/
