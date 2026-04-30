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
       convincing students that the standard Rocq inductive definition
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
import Logic
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

/- TODO: (OA) How do we do failed definitions? -/
namespace Failed

/--
error: fail to show termination for
  Failed.reaches1_in
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

end Failed

/- Indeed, this isn't just a pointless limitation: functions in Lean
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

namespace Failed

/--
error: fail to show termination for
  Failed.CollatzHoldsFor
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    CollatzHoldsFor (div2 n)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n x✝ : Nat
h✝ : even n = true
⊢ div2 n < x✝
-/
#guard_msgs in
def CollatzHoldsFor (n : Nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then CollatzHoldsFor (div2 n)
                   else CollatzHoldsFor ((3 * n) + 1)

end Failed

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

theorem collatz : ∀ n, n ≠ 0 → CollatzHoldsFor n := by sorry

/- If you succeed in proving this conjecture, you've got a bright
   future as a number theorist!  But don't spend too long on it --
   it's been open since 1937. -/

/- HIDE: CH: We may want to add an exercise later proving false if
   one assumes Collatz' conjecture without the `n ≠ 0` assumption.
   We had that mistake in the script for years and no one noticed,
   wow! -/

-- ##############################################
-- ** Example: Binary relation for comparing numbers

/- A binary _relation_ on a set `X` has Lean type `X → X → Prop`.
   This is a family of propositions parameterized by two elements
   of `X` -- i.e., a proposition about pairs of elements of `X`. -/

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
