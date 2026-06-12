-- RAB: chapter covers:
-- inductive nats
-- nat notation
-- structural recursion
-- binary numerals

-- Main thought point: decide how much to get into and use the
-- specific features of Lean `Nat`.
-- In my opinion, the answer is "all the way."

-- Specifically:
-- Start early with the built-in `Nat` type, and use it for all examples and exercises.
-- Talk about notation, typeclasses, and the (n + 1) notation for succ.
-- We should use these builtins liberally and teach them as the norm, since they are.
-- We can start by comparing to Countdown, and then quickly move to the
-- built-in `Nat` and use it for all examples and exercises.
-- There should be a section on tactics and how much automation students can use.



-- Things ported:

-- TOFIX: prose. The same numeral and the same `+` work at two
-- different types. Typeclasses are the dispatch mechanism.
#check (3 : Nat)
#check (3 : NatPlayground.Nat)

#print Add

#check (inferInstance : Add Nat)
#check (inferInstance : Add NatPlayground.Nat)

-- TOFIX: prose. Two proofs of "the same" fact, one per instance.
section
open NatPlayground.Nat
example : (2 + 2 : NatPlayground.Nat) = 4 := by
  rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_succ, add_zero]
  rfl
end

example : (2 + 2 : Nat) = 4 := by rfl

-- TOFIX: prose. Why rules instead of brute simplification: code written
-- against an interface cannot unfold any implementation. Only the laws
-- are available.
example (α : Type) [Add α] (x y : α)
    (comm : ∀ a b : α, a + b = b + a) :
    x + y = y + x := by
  fail_if_success rfl
  rw [comm]

-- TOFIX: closing prose. The general flow of Lean is to state rewrite rules
-- for a type, prove lemmas from the rules, rewrite with the lemmas, and
-- let dsimp/simp/calc carry out the routine steps.


/-
  ######################################################################
  # Automated rewriting: `simp` and simp annotations
-/

-- TOFIX: prose. simp = rewrite with a whole set of rules, repeatedly.
example (n : Nat) : ((n + 0) + 0) + 0 = n := by
  simp

-- TOFIX: prose. simp also works with our own rules, given explicitly...
section
open NatPlayground.Nat
example (n : NatPlayground.Nat) : (n + 0) + 0 = n := by
  simp [add_zero]
end

-- TOFIX: prose. ...or registered once with the @[simp] annotation.
def double' (n : Nat) : Nat := n + n

@[simp] theorem double'_def (n : Nat) : double' n = n + n := rfl

example (n : Nat) : double' (n + 0) = n + n := by
  simp



@[irreducible]
def sub (n m : Nat) : Nat :=
  match n, m with
  | zero, _ => zero
  | succ _, zero => n
  | succ n', succ m' => sub n' m'

instance instSub : Sub Nat where sub := sub

-- RULES
unseal sub in
theorem sub_zero : ∀ n : Nat, 0 - n = 0 := by
  intro n
  rfl

-- RULES
unseal sub in
theorem succ_sub_zero : ∀ n : Nat, succ n - 0 = succ n := by
  intro n
  rfl

-- RULES
unseal sub in
theorem succ_sub_succ : ∀ n m : Nat, succ n - succ m = n - m := by
  intro n m
  rfl

@[irreducible]
def pow (base power : Nat) : Nat :=
  match power with
  | zero => 1
  | succ p => mul base (pow base p)

instance instPow : Pow Nat Nat where pow := pow

macro_rules | `($x ^ $y) => `(HPow.hPow ($x : Nat) ($y : Nat))

-- RULES
unseal pow in
theorem pow_zero : ∀ n : Nat, n ^ 0 = 1 := by
  intro n
  rfl

-- RULES
unseal pow in
theorem pow_succ : ∀ n m : Nat, n ^ succ m = n * n ^ m := by
  intro n m
  rfl

-- FULL
-- EX1 (factorial)
/-
  Recall the standard mathematical factorial function:
         factorial(0)  =  1
         factorial(n)  =  n * factorial(n-1)     (if n>0)
  Translate this into Lean.
-/

@[irreducible]
def factorial (n : Nat) : Nat
  -- ADMITDEF
  := match n with
  | zero => 1
  | succ n' => mul (succ n') (factorial n')
  -- /ADMITDEF

/- test_factorial1 -/
unseal factorial mul add in
example : factorial 3 = 6 := by rfl  -- ADMITTED
/- test_factorial2 -/
unseal factorial mul add in
example : factorial 5 = mul 10 (add 10 2) := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: factorial_test2
-- []
-- /FULL

-- TERSE: /- *** -/

-- JC: Overriding the `+` is an immense headache for technical reasons,
-- so we leave that alone, since our definition is the same anyway.
-- In contrast, our `sub` definition _is_ slightly different,
-- so we _do_ want to override the notation instance for it.
-- The `mul` and `pow` definitions are the same as the stdlib,
-- but we can also override notation for it.

-- JC: In the infoview, hover over the operators
-- to check out their associativity --
-- `+`, `-`, and `*` all left-associative,
-- but `^` is right-associative.

#check (0 + 1 + 1 : Nat)
#check (4 - 3 - 2 : Nat)
#check (2 * 3 * 4 : Nat)
#check (1 ^ 2 ^ 2 : Nat)


-- End ported
-- Scratch

@[irreducible]
def leb (n m : Nat) : Bool :=
  match n with
  | zero => true
  | succ n' =>
      match m with
      | zero => false
      | succ m' => leb n' m'

unseal leb in theorem leb_zero : ∀ n : Nat, leb 0 n = true := by
  intro n
  rfl

unseal leb in
theorem leb_succ_zero : ∀ n : Nat, leb (succ n) 0 = false := by
  intro n
  rfl

unseal leb in
theorem leb_succ_succ : ∀ n m : Nat, leb (succ n) (succ m) = leb n m := by
  intro n m
  rfl


/- test_leb1 -/

example : leb 2 2 = true  := by
  rewrite [two_eq_succ_one, one_eq_succ_zero]
  rewrite [leb_succ_succ, leb_succ_succ, leb_zero]
  rfl
/- test_leb2 -/
example : leb 2 4 = true  := by
  rewrite [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  rewrite [leb_succ_succ, leb_succ_succ, leb_zero]
  rfl
/- test_leb3 -/
example : leb 4 2 = false := by
  rewrite [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  rewrite [leb_succ_succ, leb_succ_succ, leb_succ_zero]
  rfl


-- TERSE: /- *** -/
/-
  We'll be using these (especially `beq`) a lot, so let's give
  them infix notations.
-/

-- JC: Lean's stdlib has `==` notation for `beq`,
-- but not for `Nat.ble`...

instance : BEq Nat where
  beq := beq

infix:65 "<=?" => leb

/-
  test_leb3'
-/
example : 4 <=? 2 = false := by
  rewrite [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  rewrite [leb_succ_succ, leb_succ_succ, leb_succ_zero]
  rfl

-- HERE we should introduce decidability.

-- FULL
/-
  We now have two symbols that both look like equality: `=`
  and `=?`.  We'll have much more to say about their differences and
  similarities later. For now, the main thing to notice is that
  `x = y` is a logical _claim_ -- a "proposition" -- that we can try to
  prove, while `x =? y` is a boolean _expression_ whose value (either
  `true` or `false`) we can compute.
-/
-- /FULL

-- FULL
-- EX1 (ltb)
/-
  Define a less-than function in terms of `leb`.
-/
@[irreducible]
def ltb (n m : Nat) : Bool
  -- ADMITDEF
  := leb (succ n) m
  -- /ADMITDEF

infix:65 "<?" => ltb

-- Walk them through rules or
/-
  ######################################################################
  # Proof by Simplification
-/

-- FULL
/-
   Now that we've looked at a few datatypes and functions, let's turn to stating
  and proving properties of their behavior.
-/
-- /FULL

-- TERSE: /- A specific fact about natural numbers: -/
/-
  plus_1_1
-/
example : (1 + 1 : Nat) = 2 := by
  rewrite [two_eq_succ_one, one_eq_succ_zero, add_succ, add_zero]
  rfl
-- TERSE: /- Another specific fact about natural numbers: -/
theorem add_zero_one : (1 : Nat) = 0 + 1 := by
   rewrite [one_eq_succ_zero, add_succ, add_zero]
   rfl -- FULL
/-
  We can begin to establish more interesting properties.  For example, the
  fact that `0` is a "neutral element" for `+` on the left can be
  proved just by observing that `0 + n` reduces to `n` no matter
  what `n` is.
-/
-- /FULL

-- TERSE: /- A general property of natural numbers: -/


theorem beq_succ : ∀ n m : Nat, (succ n == succ m) = (n == m) := by
  intro n m; rfl

/- Note: The semicolon `;` separates
  multiple steps of tactics; they can also be separated by putting them on
  separate lines. -/


/-
  ######################################################################
  ## Numbers
-/

-- FULL
/-
  We put this section in a namespace so that our own definition of
  natural numbers does not interfere with the one from the
  standard library.  In the rest of the book, we'll want to use
  the standard library's.
-/
-- /FULL



namespace NatPlayground

-- FULL
/-
  All the types we have defined so far -- both "enumerated
  types" such as `Day`, `Bool`, and `Bit` and tuple types such as
  `Nybble` built from them -- are finite.  The natural numbers, on
  the other hand, are an infinite set, so we'll need to use a
  slightly richer form of type declaration to represent them.
-/

-- RAB: I moved over the notes from the Rocq book here, as I find they
-- very nicely motivate unary for someone who has not seen it before.

/-
  There are many representations of numbers to choose from. You are
  certainly familiar with decimal notation (base 10), using the
  digits 0 through 9, for example, to form the number 123. You may
  very likely also have encountered hexadecimal notation (base 16),
  in which the same number is represented as 7B, or octal (base 8),
  where it is 173, or binary (base 2), where it is 1111011. Using an
  enumerated type to represent digits, we could use any of these as
  our representation natural numbers. Indeed, there are
  circumstances where each of these choices would be useful.
-/

/-
  The binary representation is valuable in computer hardware because
  the digits can be represented with just two distinct voltage
  levels, resulting in simple circuitry. Analogously, we wish here
  to choose a representation that makes _proofs_ simpler.
-/

/-
  In fact, there is a representation of numbers that is even simpler
  than binary, namely unary (base 1), in which only a single digit
  is used -- as our forebears might have done to count days by
  making scratches on the walls of their caves. To represent unary
  numbers with a Lean datatype, we use two constructors. The
  [zero] constructor represents zero. The [succ] constructor can be
  applied to the representation of the natural number [n], yielding
  the representation of [n+1], where [succ] stands for "successor."
   Here is the complete datatype definition: *)
-/

-- /FULL

-- TERSE: /- For simplicity in proofs, we choose unary representation. -/

@
inductive Nat : Type where
  | zero
  | succ (n : Nat)

namespace Nat

/-
  With this definition, 0 is represented by `zero`, 1 by `succ zero`,
  2 by `succ (succ zero)`, and so on.
-/

-- TERSE: /- *** -/
/-
  Critical point: this just defines a _representation_ of
  numbers -- a unary notation for writing them down.
-/

inductive OtherNat : Type where
  | stop
  | tick (foo : OtherNat)

/-
  This is the same _representation_ of numbers as `Nat`, but with different
  (sillier!) constructor names.
-/

/-
  The _interpretation_ of these representations arises from how we use them to
  compute.
-/

def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'


-- TERSE: /- *** -/

/-
  Because natural numbers are such a pervasive kind of data,
  Lean provides built-in support for them: ordinary decimal
  numerals can be used as a shorthand, and Lean's `Nat` type uses
  the constructors `Nat.zero` and `Nat.succ`.
-/

-- TODO: change this to not talk about numerals yet, instead define our own.
-- TODO: document this

def one : Nat := succ zero
def two : Nat := succ one
def three : Nat := succ two
def four : Nat := succ three
def five : Nat := succ four

-- RAB: Hovering over succ points out that "Using Nat.succ n should usually be
-- avoided in favor of n + 1, which is the simp normal form." How quickly should
-- we break away from succ style and go straight to n + 1 style? More broadly,
-- how much do we want to adhere to conventions like simp normal form? In my
-- view, following standard Lean style wherever possible is a good thing to be
-- doing, in no small part because proof view displays terms in Lean style, e.g. (n +
-- 1) instead of `succ n`.

example : succ (succ (succ (succ .zero))) = four := by rfl

def minustwo (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ (zero) => zero
  | succ (succ n') => n'

#eval minustwo four
/- ===> 2 -/

-- FULL
#check Nat.succ  -- Nat → Nat
#check Nat.pred  -- Nat → Nat
#check minustwo  -- Nat → Nat

/-
  These are all things that can be applied to a number to yield a
  number.  However, there is a fundamental difference between `Nat.succ`
  and the other two: functions like `Nat.pred` and `minustwo` are
  defined by giving _computation rules_ -- e.g., the definition of
  `Nat.pred` says that `Nat.pred 2` can be simplified to `1` -- while the
  definition of `Nat.succ` has no such behavior attached.  Although it is
  _like_ a function in the sense that it can be applied to an
  argument, it does not _do_ anything at all!  It is just a way of
  writing down numbers.
-/
-- /FULL

-- TERSE: /- *** -/
-- TERSE: /- Recursive functions: -/

def even (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ (zero) => false
  | succ (succ n') => even n'

-- TERSE: /- *** -/
/-
  We could define `odd` by a similar recursive declaration, but
  here is a simpler way:
-/

def odd (n : Nat) : Bool :=
  not (even n)

/- test_odd1 -/
example : odd 1 = true  := by rfl
/- test_odd2 -/
example : odd 4 = false := by rfl

-- TERSE: /- *** -/
-- TERSE: /- A multi-argument recursive function. -/

@[irreducible]
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | 0 => n
  | .succ m' => .succ (add n m')

unseal add in
theorem add_zero : ∀ n, add n 0 = n := by
  intro n
  rfl

unseal add in
theorem add_succ : ∀ n m, add n (.succ m) = .succ (add n m) := by
  intro n


-- FULL
/-
  Adding three to two gives us five (whew!):
-/
-- /FULL

#eval add 3 2
/- ===> 5 -/

-- FULL
/-
  The steps of simplification that Lean performs here can be
  visualized as follows:

       `add 3 2`
    i.e. `add (succ (succ (succ 0))) (succ (succ 0))`
-/
/-    ==> `succ (add (succ (succ (succ 0))) (succ 0))` -/
/-
           by the second clause of the `match`
-/
/-    ==> `succ (succ (add (succ (succ (succ 0))) 0))` -/
/-
           by the second clause of the `match`
-/
/-    ==> `succ (succ (succ (add (succ 0))))` -/
/-
           by the first clause of the `match`
    i.e. `5`
-/
-- /FULL

-- TERSE: /- *** -/

-- FULL
/-
  Now that we know how addition is defined, we can use Lean's builtin
  definition and notation to write it more concisely.
  The `+` operator is already defined for `Nat` in the standard library.
-/
-- /FULL

def mul (n m : Nat) : Nat :=
  match m with
  | 0 => 0
  | .succ m' => (mul n m') + n

/- test_mult1 -/
example : mul 3 3 = 9 := by rfl

-- TERSE: /- *** -/
/-
  We can pattern-match two values at the same time:
-/

def sub (n m : Nat) : Nat :=
  match n, m with
  | 0,        _        => 0
  | .succ _,  0        => n
  | .succ n', .succ m' => sub n' m'

/-
  Now that we've seen how natural numbers are built from `Nat.zero`
  and `Nat.succ`, we can take further advantage of Lean's notation: the
  pattern `n + 1` is syntactic sugar for `Nat.succ n`, `n + 2` is
  syntactic sugar for `Nat.succ (Nat.succ n)`, and so on.
  We'll use this more concise style from now on.
-/

def pow (base power : Nat) : Nat :=
  match power with
  | 0 => 1
  | p + 1 => mul base (pow base p)

-- FULL
-- EX1 (factorial)
/-
  Recall the standard mathematical factorial function:
         factorial(0)  =  1
         factorial(n)  =  n * factorial(n-1)     (if n>0)
  Translate this into Lean.
-/

def factorial (n : Nat) : Nat
  -- ADMITDEF
  := match n with
  | 0 => 1
  | n' + 1 => n * factorial n'
  -- /ADMITDEF

/- test_factorial1 -/
example : factorial 3 = 6         := by rfl  -- ADMITTED
/- test_factorial2 -/
example : factorial 5 = 10 * 12   := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: factorial_test2
-- []
-- /FULL

-- TERSE: /- *** -/
/-
  Lean already provides `+`, `-`, `*` for `Nat`, so we don't need to
  define our own notation.
-/


-- JC: Overriding the `+` is an immense headache for technical reasons,
-- so we leave that alone, since our definition is the same anyway.
-- In contrast, our `sub` definition _is_ slightly different,
-- so we _do_ want to override the notation instance for it.
-- The `mul` and `pow` definitions are the same as the stdlib,
-- but we can also override notation for it.

instance instSub : Sub Nat where sub := sub
instance instMul : Mul Nat where mul := mul
instance instPow : Pow Nat Nat where pow := pow

-- JC: In the infoview, hover over the operators
-- to check out their associativity --
-- `+`, `-`, and `*` all left-associative,
-- but `^` is right-associative.

#check (0 + 1 + 1 : Nat)
#check (4 - 3 - 2 : Nat)
#check (2 * 3 * 4 : Nat)
#check (1 ^ 2 ^ 2 : Nat)

-- TERSE: /- *** -/
/-
  When we say that Lean comes with almost nothing built-in, we really
  mean it: even testing equality is a user-defined operation!

  Here is a function `beq` that tests natural numbers for
  equality, yielding a boolean.
-/

def beq (n m : Nat) : Bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | _ + 1 => false
  | n' + 1 => match m with
              | 0 => false
              | m' + 1 => beq n' m'

-- TERSE: /- *** -/
/-
  Similarly, the `leb` function tests whether its first argument is
  less than or equal to its second argument, yielding a boolean.
-/

def leb (n m : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
      match m with
      | 0 => false
      | m' + 1 => leb n' m'

/- test_leb1 -/
example : leb 2 2 = true  := by rfl
/- test_leb2 -/
example : leb 2 4 = true  := by rfl
/- test_leb3 -/
example : leb 4 2 = false := by rfl

-- TERSE: /- *** -/
/-
  We'll be using these (especially `beq`) a lot, so let's give
  them infix notations.
-/

-- JC: Lean's stdlib has `==` notation for `beq`,
-- but not for `Nat.ble`...

instance : BEq Nat where
  beq := beq

infix:65 "<=?" => leb

/-
  test_leb3'
-/
example : 4 <=? 2 = false := by rfl

-- FULL
/-
  We now have two symbols that both look like equality: `=`
  and `=?`.  We'll have much more to say about their differences and
  similarities later. For now, the main thing to notice is that
  `x = y` is a logical _claim_ -- a "proposition" -- that we can try to
  prove, while `x =? y` is a boolean _expression_ whose value (either
  `true` or `false`) we can compute.
-/
-- /FULL

-- FULL
-- EX1 (ltb)
/-
  Define a less-than function in terms of `leb`.
-/

def ltb (n m : Nat) : Bool
  -- ADMITDEF
  := leb (n + 1) m
  -- /ADMITDEF

infix:65 "<?" => ltb

/- test_ltb1 -/
example : 2 <? 2 = false := by rfl  -- ADMITTED
/- test_ltb2 -/
example : 2 <? 4 = true  := by rfl  -- ADMITTED
/- test_ltb3 -/
example : 4 <? 2 = false := by rfl  -- ADMITTED
-- GRADE_THEOREM 1: ltb_test3
-- []
-- /FULL

/-
  ######################################################################
  # Proof by Simplification
-/

-- FULL
/-
  Now that we've looked at a few datatypes and functions,
  let's turn to stating and proving properties of their behavior.

  Actually, we've already started doing this: each `example` in the
  previous sections made a precise claim about the behavior of some
  function on some particular inputs.  The proofs of these claims
  were always the same: use `rfl` to check that both sides of the
  equation evaluate to identical values.
-/
-- /FULL

-- TERSE: /- A specific fact about natural numbers: -/
/-
  plus_1_1
-/
example : 1 + 1 = 2 := by rfl

-- TERSE: /- Another specific fact about natural numbers: -/
-- JC: Keep the name for this one, it gets used later.
theorem add_zero_one : 1 = 0 + 1 := by rfl

-- FULL
/-
  The same sort of "proof by simplification" can also be used to
  establish more interesting properties.  For example, the
  fact that `0` is a "neutral element" for `+` on the left can be
  proved just by observing that `0 + n` reduces to `n` no matter
  what `n` is.
-/
-- /FULL

-- TERSE: /- A general property of natural numbers: -/

/-
  Note: Because Lean's addition recurses on the second argument,
  `n + 0` reduces to `n` by definition.
  `n + 0` reduces to `n` by definition.
-/

theorem add_zero : ∀ n : Nat, n + 0 = n := by
  intro n; rfl

-- FULL
/-
  The keywords `intro` and `rfl` are examples of _tactics_.
  A tactic is a command that is used between `by` and the end of the
  proof to guide the process of checking some claim we are making.
  The semicolon `;` separates multiple steps of tactics;
  they can also be separated by putting them on separate lines.
  We will see several more tactics in the rest of this chapter and
  many more in future chapters.
-/
-- /FULL

-- TERSE: /- *** -/

-- FULL
/-
  Even these trivial examples provide opportunities to _step through_ the proof,
  using the cursor. Moving the cursor over the `by` and stepping through the
  tactics will show the state of the proof at each step in the right-hand
  Lean InfoView Panel.
-/
-- /FULL

theorem add_succ : ∀ n m : Nat, n + (m + 1) = (n + m) + 1 := by
  intro n m; rfl

theorem mul_zero : ∀ n : Nat, n * 0 = 0 := by
  intro n; rfl

theorem mul_succ : ∀ n m : Nat, n * (m + 1) = n * m + n := by
  intro n m; rfl

-- JC: Dumping the rest of the properties here.
-- They're needed because the notations prevent reducing from left to right
-- by just `dsimp [sub]` or `dsimp [pow]`.
-- I don't think these properties are actually used by us,
-- so maybe they can just be exercises.

#check Nat.sub_zero

theorem sub_zero n : 0 - n = 0 := by rfl
theorem succ_sub_zero n : (n + 1) - 0 = n + 1 := by rfl
theorem succ_sub_succ n m : (n + 1) - (m + 1) = n - m := by rfl

theorem pow_zero n : n ^ 0 = 1 := by rfl
theorem pow_succ (n m : Nat) : n ^ (m + 1) = n * (n ^ m) := by rfl

-- JC: And another one, which we _do_ use later.

theorem beq_succ : ∀ n m : Nat, (n + 1 == m + 1) = (n == m) := by
  intro n m; rfl
/-
  ######################################################################
  # Proof by Rewriting
-/

-- TERSE: /- A (slightly) more interesting theorem: -/

theorem plus_id_example : ∀ n m : Nat,
    n = m →
    n + n = m + m := by
  -- FULL
  /-
    Instead of making a universal claim about all numbers `n` and `m`,
    this talks about a more specialized property that only holds when
    `n = m`.  The arrow symbol is pronounced "implies."

    The tactic that tells Lean to perform replacement is called `rewrite`.
  -/
  -- /FULL
  intro n m
  intro h
  rewrite [h]
  rfl

-- TERSE: /- The `intro` tactic names the hypotheses as they are moved to the context.  The `rewrite` tactic rewrites using an equality. -/

-- FULL
/-
  By default, `rewrite` rewrites left-to-right. To rewrite from right
  to left, use `rewrite [← h]`, where `←` is typed as `\l` or `\<-`.
-/
-- /FULL


-- FULL
-- EX1 (plus_id_exercise)
/-
  Remove `sorry` and fill in the proof.
-/

theorem plus_id_exercise : ∀ n m o : Nat,
    n = m → m = o → n + m = m + o := by
  -- ADMITTED
  intro n m o h1 h2
  rewrite [h1, h2]
  rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: plus_id_exercise
-- []
-- /FULL

-- FULL
/-
  The `sorry` keyword tells Lean that we want to skip trying
  to prove this theorem and just accept it as a given.  This is
  often useful for developing longer proofs.

  Be careful, though: every time you say `sorry` you are leaving
  a door open for total nonsense to enter Lean's safe, formally
  checked world!
-/
-- /FULL

-- TERSE: /- *** -/

/-
  The `#check` command can also be used to examine the statements of
  previously declared lemmas and theorems.
-/

#check mul_zero  -- ∀ (n : Nat), n * 0 = 0
#check mul_succ  -- ∀ (n m : Nat), n * Nat.succ m = n + n * m

-- TERSE: /- *** -/
/-
  We can use the `rewrite` tactic with a previously proved theorem
  instead of a hypothesis from the context.
-/

theorem add_mul_zero : ∀ p q : Nat,
    (p * 0) + (q * 0) = 0 := by
  intro p q
  rewrite [mul_zero, mul_zero, add_zero]
  rfl

/-
  ######################################################################
  # Proof by Case Analysis
-/

-- FULL
/-
  Of course, not everything can be proved by simple
  calculation and rewriting: In general, unknown, hypothetical
  values (arbitrary numbers, booleans, lists, etc.) can block
  simplification.
-/
-- /FULL

-- TERSE: /- Sometimes simple calculation and rewriting are not enough... -/
example : ∀ n : Nat,
    (n + 1 == 0) = false := by
  intro n
  /-
    `rfl` doesn't work here because `n` is unknown
  -/
  sorry

-- FULL
/-
  The tactic that tells Lean to consider separate cases is called
  `cases`.
-/
-- /FULL

-- TERSE: /- We can use `cases` to perform case analysis: -/

theorem add_one_neb_zero : ∀ n : Nat,
    (n + 1 == 0) = false := by
  intro n
  cases n
  case zero => rfl
  case succ n' => rfl


-- FULL
/-
  ######################################################################
  ## More on Notation (Optional)
-/

/-
  Lean has a very flexible notation system.  Operators like `+` and `*`
  are defined with specified precedence and associativity.  For example,
  `+` has precedence 65 and is left-associative, while `*` has
  precedence 70 and is also left-associative.  This means that `1+2*3*4`
  is parsed as `1+((2*3)*4)`.

  You can define custom notation using the `notation`, `infixl`,
  `infixr`, `prefix`, and `postfix` commands.

  Lean handles notation scoping through namespaces and
  type classes rather than notation scopes.  The numeric literal `3`
  can be interpreted as `Nat`, `Int`, `Float`, etc., depending on the
  expected type, thanks to Lean's `OfNat` type class.
-/
-- /FULL

-- FULL
/-
  ######################################################################
  ## Structural Recursion (Optional)
-/

/-
  Here is a copy of the definition of addition:
-/

def plus' (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0 => m
  | n' + 1 => (plus' n' m) + 1

/-
  When Lean checks this definition, it verifies that the recursion
  terminates.  Specifically, it checks that one of the arguments
  is _structurally decreasing_.  This implies that all calls to
  `plus'` will eventually terminate.

  This requirement is a fundamental feature of Lean's design: In
  particular, it guarantees that every function that can be defined
  in Lean will terminate on all inputs.  However, because Lean's
  termination analysis is not always able to figure things out
  automatically, it is sometimes necessary to provide hints or
  write functions in slightly different ways.

  Lean also supports more flexible termination proofs using
  `termination_by` and `decreasing_by` clauses, as well as `partial`
  functions that are not required to terminate.
-/

-- EX2? (decreasing)
/-
  To get a concrete sense of this, find a way to write a sensible
  recursive definition (of a simple function on numbers, say) that
  _does_ terminate on all inputs, but that Lean will reject because
  it cannot automatically prove termination.
-/

--  SOLUTION
/-
  def factorial_bad (n : Nat) : Nat :=
    if n == 0 then 1
    else n * factorial_bad (n - 1)
  This fails because Lean can't see that `n - 1` is structurally smaller.

-/
-- /SOLUTION
-- []
-- /FULL

end Nat

/-
  ######################################################################
  ## Binary Numerals
-/

-- EX3 (binary)
/-
  We can generalize our unary representation of natural numbers to
  the more efficient binary representation by treating a binary
  number as a sequence of constructors `b0` and `b1` (representing 0s
  and 1s), terminated by a `z`.

  For example:

  | decimal |            binary     |                                                unary         |
  |:-------:| ---------------------:| ------------------------------------------------------------:|
  |    0    | `               z   ` | `                                               zero       ` |
  |    1    | `            b1 z   ` | `                                          succ zero       ` |
  |    2    | `        b0 (b1 z)  ` | `                                    succ (succ zero)      ` |
  |    3    | `        b1 (b1 z)  ` | `                              succ (succ (succ zero))     ` |
  |    4    | `    b0 (b0 (b1 z)) ` | `                        succ (succ (succ (succ zero)))    ` |
  |    5    | `    b1 (b0 (b1 z)) ` | `                  succ (succ (succ (succ (succ zero))))   ` |
  |    6    | `    b0 (b1 (b1 z)) ` | `            succ (succ (succ (succ (succ (succ zero)))))  ` |
  |    7    | `    b1 (b1 (b1 z)) ` | `      succ (succ (succ (succ (succ (succ (succ zero)))))) ` |
  |    8    | `b0 (b0 (b0 (b1 z)))` | `succ (succ (succ (succ (succ (succ (succ (succ zero)))))))` |

  Note that the low-order bit is on the left and the high-order bit
  is on the right -- the opposite of the way binary numbers are
  usually written.  This choice makes them easier to manipulate.

  (Comprehension check: What unary numeral does `b0 z` represent?)
-/

inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

def incr (m : Bin) : Bin
  -- ADMITDEF
  := match m with
  | .z => .b1 .z
  | .b0 m' => .b1 m'
  | .b1 m' => .b0 (incr m')
  -- /ADMITDEF

def binToNat (m : Bin) : Nat
  -- ADMITDEF
  := match m with
  | .z => 0
  | .b0 m' => binToNat m' * 2
  | .b1 m' => binToNat m' * 2 + 1
  -- /ADMITDEF

/- test_bin_incr1 -/
example : incr (.b1 .z) = .b0 (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr2 -/
example : incr (.b0 (.b1 .z)) = .b1 (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr3 -/
example : incr (.b1 (.b1 .z)) = .b0 (.b0 (.b1 .z)) := by rfl  -- ADMITTED
/- test_bin_incr4 -/
example : binToNat (.b0 (.b1 .z)) = 2 := by rfl  -- ADMITTED
/- test_bin_incr5 -/
example : binToNat (incr (.b1 .z)) = 1 + binToNat (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr6 -/
example : binToNat (incr (incr (.b1 .z))) = 2 + binToNat (.b1 .z) := by rfl  -- ADMITTED
/- test_bin_incr7 -/
example : binToNat (.b0 (.b0 (.b0 (.b1 .z)))) = 8 := by rfl  -- ADMITTED

-- GRADE_THEOREM 0.5: incr_test1
-- GRADE_THEOREM 0.5: incr_test2
-- GRADE_THEOREM 0.5: incr_test3
-- GRADE_THEOREM 0.5: binToNat_test1
-- GRADE_THEOREM 0.5: binToNat_test2
-- GRADE_THEOREM 0.5: binToNat_test3
-- []

-- FULL
/-
  ######################################################################
  ## Course Late Policies, Formalized
-/

/-
  Suppose that a course has a grading policy based on late days,
  where a student's final letter grade is lowered if they submit too
  many homework assignments late.
-/

namespace LateDays

/-
  First, we inroduce a datatype for modeling the "letter" component
  of a grade.
-/
inductive Letter : Type where
  | A | B | C | D | F

/-
  Then we define the modifiers -- a `natural` `a` is just a "plain"
  grade of `a`.
-/
inductive Modifier : Type where
  | plus | natural | minus

/-
  A full `Grade`, then, is just a `letter` and a `modifier`.
  In Lean, a combination of several values is called a _structure_.  The `structure`
  keyword is used to define a new structure type.
-/

structure Grade where
  letter : Letter
  modifier : Modifier

/-
  We will want to be able to say when one grade is "better" than
  another.  In other words, we need a way to compare two grades.  As
  with natural numbers, we could define `bool`-valued functions
  `grade_eqb`, `grade_ltb`, etc., and that would work fine.
  However, we can also define a slightly more informative type for
  comparing two values, as shown below.  This datatype has three
  constructors that can be used to indicate whether two values are
  "equal", "less than", or "greater than" one another.
-/
inductive Comparison : Type where
  | eq   -- "equal"
  | lt   -- "less than"
  | gt   -- "greater than"

/-
  Since we're in a namespace, we can open the relevant types to
  avoid having to write `Letter.A`, etc.
-/
open Letter Modifier Comparison

/-
  Using pattern matching, it is not difficult to define the
  comparison operation for two letters `l1` and `l2` (see below).
  This definition uses a feature of `match` patterns: we can match
  against _two_ values simultaneously by separating them and the
  corresponding patterns with comma `,`.
  This is simply a convenient abbreviation for nested pattern
  matching.
-/
def letterComparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | A, A => eq
  | A, _ => gt
  | B, A => lt
  | B, B => eq
  | B, _ => gt
  | C, A => lt
  | C, B => lt
  | C, C => eq
  | C, _ => gt
  | D, F => gt
  | D, D => eq
  | D, _ => lt
  | F, F => eq
  | F, _ => lt

example : letterComparison B A = lt := by rfl
example : letterComparison D D = eq := by rfl
example : letterComparison B F = gt := by rfl

-- EX1 (letter_comparison)
theorem letterComparison_Eq : ∀ l : Letter,
    letterComparison l l = eq := by
  -- ADMITTED
  intro l; cases l <;> rfl
  -- /ADMITTED
-- GRADE_THEOREM 1: letterComparison_Eq
-- []

def modifierComparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | plus, plus => eq
  | plus, _ => gt
  | natural, plus => lt
  | natural, natural => eq
  | natural, _ => gt
  | minus, minus => eq
  | minus, _ => lt

-- EX2 (grade_comparison)

/-
  Here, we will need to access the fields of the `Grade` structure.
  The field names are `letter` and `modifier`, so for a grade `g`,
  we can write `g.letter` and `g.modifier` to access these fields.
-/

def gradeComparison (g1 g2 : Grade) : Comparison
  -- ADMITDEF
  := match letterComparison g1.letter g2.letter with
  | lt => lt
  | eq => modifierComparison g1.modifier g2.modifier
  | gt => gt
  -- /ADMITDEF

/- test_grade_comparison1 -/
example : gradeComparison ⟨A, minus⟩ ⟨B, plus⟩ = gt := by rfl  -- ADMITTED
/- test_grade_comparison2 -/
example : gradeComparison ⟨A, minus⟩ ⟨A, plus⟩ = lt := by rfl  -- ADMITTED
/- test_grade_comparison3 -/
example : gradeComparison ⟨F, plus⟩ ⟨F, plus⟩ = eq := by rfl  -- ADMITTED
/- test_grade_comparison4 -/
example : gradeComparison ⟨B, minus⟩ ⟨C, plus⟩ = gt := by rfl  -- ADMITTED
-- GRADE_THEOREM 0.5: gradeComparison_test1
-- GRADE_THEOREM 0.5: gradeComparison_test2
-- GRADE_THEOREM 0.5: gradeComparison_test3
-- GRADE_THEOREM 0.5: gradeComparison_test4
-- []

def lowerLetter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  -- Can't go lower than F!

/-
  This theorem is not provable because of the edge case of F!
  theorem lowerLetter_lowers_bad : ∀ (l : Letter),
    letterComparison (lowerLetter l) l = lt := by ...
-/

theorem lowerLetter_F_is_F : lowerLetter F = F := by rfl

-- EX2 (lower_letter_lowers)
theorem lowerLetter_lowers : ∀ l : Letter,
    letterComparison F l = lt →
    letterComparison (lowerLetter l) l = lt := by
  -- ADMITTED
  intro l h
  cases l with
  | A => rfl
  | B => rfl
  | C => rfl
  | D => rfl
  | F => exact h
  -- /ADMITTED
-- GRADE_THEOREM 2: lowerLetter_lowers
-- []

-- EX2 (lower_grade)
/-
  In addition to the dot notation for accessing structure fields, we can also
  use pattern matching to access these fields.
  For example, if `g` is a grade, then we can write
  `match g with ⟨l, m⟩ => ...` to access the letter and modifier components
  of `g` as `l` and `m`, respectively.
  Note: The angle brackets `⟨` and `⟩` are typed as `\<` and `\>`.
-/
def lowerGrade (g : Grade) : Grade
  -- ADMITDEF
  := match g with
  | ⟨l, plus⟩ => ⟨l, natural⟩
  | ⟨l, natural⟩ => ⟨l, minus⟩
  | ⟨F, minus⟩ => ⟨F, minus⟩
  | ⟨l, minus⟩ => ⟨lowerLetter l, plus⟩
  -- /ADMITDEF

/-
  lower_grade_A_Plus
-/
example : lowerGrade ⟨A, plus⟩ = ⟨A, natural⟩ := by rfl  -- ADMITTED
/-
  lower_grade_A_Natural
-/
example : lowerGrade ⟨A, natural⟩ = ⟨A, minus⟩ := by rfl  -- ADMITTED
/-
  lower_grade_A_Minus
-/
example : lowerGrade ⟨A, minus⟩ = ⟨B, plus⟩ := by rfl  -- ADMITTED
/-
  lower_grade_B_Plus
-/
example : lowerGrade ⟨B, plus⟩ = ⟨B, natural⟩ := by rfl  -- ADMITTED
/-
  lower_grade_F_Natural
-/
example : lowerGrade ⟨F, natural⟩ = ⟨F, minus⟩ := by rfl  -- ADMITTED
/-
  lower_grade_twice
-/
example : lowerGrade (lowerGrade ⟨B, minus⟩) = ⟨C, natural⟩ := by rfl  -- ADMITTED
/-
  lower_grade_thrice
-/
example : lowerGrade (lowerGrade (lowerGrade ⟨B, minus⟩)) = ⟨C, minus⟩ := by rfl  -- ADMITTED

theorem lowerGrade_F_Minus : lowerGrade ⟨F, minus⟩ = ⟨F, minus⟩ := by rfl  -- ADMITTED

-- GRADE_THEOREM 0.25: lowerGrade_A_Plus
/-
  ...
-/
-- GRADE_THEOREM 0.25: lowerGrade_F_Minus
-- []

-- EX3 (lower_grade_lowers)
/- For our solution we use:
  * Working on multiple match cases with `| _ ... | _ => ...`;
  * Working on all remaining goals with `all_goals`.
  * These are not expected of students at this point.
   -/
theorem lowerGrade_lowers : ∀ g : Grade,
    gradeComparison ⟨F, minus⟩ g = lt →
    gradeComparison (lowerGrade g) g = lt := by
  -- ADMITTED
  intro g h
  match g with
  | ⟨l, plus⟩
  | ⟨l, natural⟩ =>
    dsimp [lowerGrade, gradeComparison]
    rewrite [letterComparison_Eq]
    dsimp [modifierComparison]
  | ⟨l, minus⟩ =>
    cases l
    case F => rewrite [lowerGrade_F_Minus]; exact h
    all_goals rfl
  -- /ADMITTED
-- GRADE_THEOREM 3: lowerGrade_lowers
-- []


def applyLatePolicy (lateDays : NatPlayground.Nat) (g : Grade) : Grade :=
  if lateDays <? 9 then g
  else if lateDays <? 17 then lowerGrade g
  else if lateDays <? 21 then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

theorem applyLatePolicy_unfold : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    applyLatePolicy lateDays g
    =
    (if lateDays <? 9 then g
     else if lateDays <? 17 then lowerGrade g
     else if lateDays <? 21 then lowerGrade (lowerGrade g)
     else lowerGrade (lowerGrade (lowerGrade g))) := by
  intro _ _; rfl

-- EX2 (no_penalty_for_mostly_on_time)
theorem no_penalty_for_mostly_on_time : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    (lateDays <? 9 = true) →
    applyLatePolicy lateDays g = g := by
  -- ADMITTED
  intro lateDays g h
  dsimp [applyLatePolicy]
  rewrite [h]; rfl
  -- /ADMITTED
-- GRADE_THEOREM 2: no_penalty_for_mostly_on_time
-- []

-- EX2 (grade_lowered_once)
theorem grade_lowered_once : ∀ (lateDays : NatPlayground.Nat) (g : Grade),
    (lateDays <? 9 = false) →
    (lateDays <? 17 = true) →
    applyLatePolicy lateDays g = lowerGrade g := by
  -- ADMITTED
  intro lateDays g h9 h17
  dsimp [applyLatePolicy]
  rewrite [h9, h17]; rfl
  -- /ADMITTED
-- GRADE_THEOREM 2: grade_lowered_once
-- []

end LateDays
-- /FULL

-- TODO put this somewhere

/-
   Lean does have an automatic evaluator, which we will introduce in
   just a few chapters. But Lean professionals prefer to use a mix of
   the evaluator and the rules, since not all functions in Lean can be
   evaluated (!). In future chapters, we will show how to derive
   simplification rules for functions automatically.
-/

-- needed or not?

-- FULL
/-
  The steps of simplification that Lean performs here can be
  visualized as follows:

       `add 3 2`
    i.e. `add (succ (succ (succ 0))) (succ (succ 0))`
-/
/-    ==> `succ (add (succ (succ (succ 0))) (succ 0))` -/
/-
           by the second clause of the `match`
-/
/-    ==> `succ (succ (add (succ (succ (succ 0))) 0))` -/
/-
           by the second clause of the `match`
-/
/-    ==> `succ (succ (succ (add (succ 0))))` -/
/-
           by the first clause of the `match`
    i.e. `5`
-/
-- /FULL
/-
  Now that we've seen how natural numbers are built from `Nat.zero`
  and `Nat.succ`, we can take further advantage of Lean's notation: the
  pattern `n + 1` is syntactic sugar for `Nat.succ n`, `n + 2` is
  syntactic sugar for `Nat.succ (Nat.succ n)`, and so on.
  We'll use this more concise style from now on.
-/

/- Lean's builtin
  definition and notation to write it more concisely.
  The `+` operator is already defined for `Nat` in the standard library. -

/-
  ** New Tactics: `dsimp`, and `exact`.

  Some more tactics will be useful for the exercises ahead.

  The `dsimp` tactic ("definitionally simplify") applies known facts
  and definitions to simplify the goal.  You can give it hints in
  square brackets: `dsimp [f]` tells it to unfold the definition
  of `f`.  You can also simplify a hypothesis `h` in the context
  by writing `dsimp [...] at h`. `dsimp` will also close goals by
  `rfl` when possible.

  The `exact` tactic closes a goal by providing an exact proof
  term.  For example, if `h : P` is in the context and the goal
  is `P`, then `exact h` closes the goal.  You can also
  transform `h` slightly — for instance, `exact h.symm` uses
  the symmetry of equality.
-/
