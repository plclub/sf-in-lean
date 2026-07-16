/- Poly: Polymorphism and Higher-Order Functions -/

/- INSTRUCTORS: To get through this plus Tactics.lean in two 80-minute
      lectures is a bit tight -- if that's your plan, don't dawdle on
      this chapter. -/

import LF.Induction
import LF.UsingLean
/- TERSE: /HIDEFROMHTML -/

/- HIDEFROMADVANCED
   FULL
   ######################################################################
   # Polymorphism -/

/- In this chapter we continue our development of basic
   concepts of functional programming. The critical new ideas are
   _polymorphism_ (abstracting functions over the types of the data
   they manipulate) and _higher-order functions_ (treating functions
   as data). We begin with polymorphism. -/

/- /FULL
   ######################################################################
   ## Polymorphic Lists -/

/- FULL: In the last chapter, we worked with lists containing just
   numbers. Obviously, interesting programs also need to be able to
   manipulate lists with elements from other types -- lists of
   booleans, lists of lists, etc. We _could_ just define a new
   inductive datatype for each of these, for example... -/

/- TERSE: Instead of defining new lists for each type, like
       this... -/

inductive BoolList : Type where
  | bool_nil
  | bool_cons (b : Bool) (l : BoolList)

/- FULL: ... but this would quickly become tedious: not only would we
   have to make up different constructor names for each datatype, but --
   even worse -- we would also need to define new versions of all
   the list manipulating functions (`length`, `++`, `reverse`,
   etc.) and all their properties (`rev_length`, `app_assoc`, etc.)
   for each new definition. -/

/- TERSE: *** -/

/- FULL: To avoid all this repetition, Lean supports _polymorphic_
   inductive type definitions. For example, here is a _polymorphic
   list_ datatype.
   /HIDEFROMADVANCED
   TERSE: ... Lean lets us give a _polymorphic_ definition that allows
   list elements of any type: -/

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (x : α) (l : MyList α) : MyList α

/- FULL: This is exactly like the definition of `Natlist` from the
   previous chapter, except that the `Nat` argument to the `cons`
   constructor has been replaced by an arbitrary type `α`, a binding
   for `α` has been added to the header on the first line,
   and the occurrences of `Natlist` in the types of the constructors
   have been replaced by `MyList α`. We can now write `MyList Nat`
   instead of a dedicated nat-list type.

   What sort of thing is `MyList` itself?  A good way to think about it
   is that the definition of `MyList` is a _function_ from `Type`s to
   `Type`s. For any particular type `α`,
   the type `MyList α` is the inductively defined set of lists whose
   elements are of type `α`.
   TERSE: We can now write `MyList Nat` in place of a dedicated
   nat-list type. -/

/- TERSE: *** -/

/- TERSE: What is `MyList` itself?

   It is a _function_ from types to types. -/

#check (MyList : Type → Type)

/- TERSE: *** -/

/- FULL: The `α` in the definition of `MyList` automatically becomes a
   parameter to the constructors `nil` and `cons` -- that is, `nil`
   and `cons` are now polymorphic constructors. In Lean, the type
   parameter is _implicit_ by default: Lean will infer it from context.
   For example, `MyList.nil` is the empty list, and Lean figures out
   the element type from how it is used. -/

/- TERSE: The `α` in the definition of `MyList` becomes an implicit
   parameter to the list constructors `nil` and `cons`. -/

#check (MyList.nil : MyList Nat)

/- FULL: Similarly, `MyList.cons` adds an element of type `Nat` to a
   list of type `MyList Nat`. Here is an example of forming a list
   containing just the natural number 3. -/

#check (MyList.cons 3 MyList.nil : MyList Nat)

/- SOONER: Unclear - Reword -/
/- FULL: What might the type of `MyList.nil` be?  We can read off the
   type `MyList α` from the definition, but this omits the binding for `α`
    which is the parameter to `MyList`. `Type -> MyList α` does not
    explain the meaning of `α`. `(α : Type) -> List α` comes
    closer. For constructors, however, the type argument is implicit; we
    don't need to supply it manually.
    Lean's notation for this situation is `{α : Type} -> List α` -/

#check (@MyList.nil : {α : Type} → MyList α)

/- FULL: Similarly, the type of `MyList.cons` includes the implicit
   type parameter: -/

#check (@MyList.cons : {α : Type} → α → MyList α → MyList α)

-- TODO: (DHS) Does this still apply?
-- TODO: (JC) We should never write `forall` in place of `∀`,
--       but somewhere in `Basics` we ought to tell people
--       that you can find out how to type a symbol by hovering over it.
/- FULL: (A side note on notations: In .v files, the "forall"
    quantifier is spelled out in letters. In the corresponding HTML
    files (and in the way some IDEs show .v files, depending on the
    settings of their display controls), [forall] is usually typeset
    as the standard mathematical "upside down A," though you'll still
    see the spelled-out "forall" in a few places. This is just a
    quirk of typesetting -- there is no difference in meaning.) -/
/- TERSE: Side note: In .v files, the "forall" quantifier is spelled
    out in letters. In the corresponding HTML files, it is usually
    typeset as the standard mathematical "upside down A." -/

/- LATER: Maybe explain better?  (Maybe NOT using the "forall is a
   funny kind of function type" intuition.) -/

/- HIDEFROMADVANCED
   FULL: Having to supply a type argument for every single use of a
   list constructor would be rather burdensome; we will soon see ways
    of reducing this annotation burden. -/

/- FULL: We can now go back and make polymorphic versions of all the
   list-processing functions that we wrote before. Here is `myRepeat`,
   for example: -/

/- /HIDEFROMADVANCED -/

-- TERSE: ***
-- TERSE: We can now define polymorphic versions of the functions
-- we've already seen...

@[irreducible]
def myRepeat (α : Type) (x : α) (count : Nat) : MyList α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat α x count')

-- Some simple facts about list lengths
unseal myRepeat in
theorem repeat_zero α v : myRepeat α v 0 = MyList.nil := rfl

unseal myRepeat in
theorem repeat_succ α v count : myRepeat α v (count + 1) = MyList.cons v (myRepeat α v count) := rfl

/- HIDEFROMADVANCED -/

/- FULL: As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to an element of this type (and a number): -/

/- test_repeat1 -/
unseal myRepeat in
example : myRepeat Nat 4 2 = .cons 4 (.cons 4 .nil) := by rfl

/- FULL: To use `myRepeat` to build other kinds of lists, we simply
   pass an element of the appropriate type: -/

/- test_repeat2 -/
unseal myRepeat in
example : myRepeat Bool false 1 = .cons false .nil := by rfl

/- QUIZ
   What is the type of `MyList.cons true (MyList.cons 3 MyList.nil)`?

   (A) `MyList Nat`

   (B) `{α : Type} → α → MyList α → MyList α`

   (C) `MyList Bool`

   (D) `MyList (Nat × Bool)`

   (E) Ill-typed
   /QUIZ -/

/- QUIZ
   What is the type of `myRepeat`?

   (A) `Nat → Nat → MyList Nat`

   (B) `{α : Type} → α → Nat → MyList α`

   (C) `{α : Type} → {β : Type} → α → Nat → MyList β`

   (D) Ill-typed
   /QUIZ -/

/- QUIZ
   What is the type of `myRepeat 1 2`?

   (A) `MyList Nat`

   (B) `{α : Type} → α → Nat → MyList α`

   (C) `MyList Bool`

   (D) Ill-typed
   /QUIZ -/

/- /HIDEFROMADVANCED -/

/- FULL: From now on, we'll use Lean's built-in `List` type and its
   associated notation. The built-in `List` is defined just like
   our `MyList` above, but with notation `[]` for `List.nil`,
   `::` for `List.cons`, and `[1, 2, 3]` for list literals.
   The `++` operator is list append. All type arguments are implicit. -/

/- TERSE: *** From now on we'll use Lean's built-in `List α` type
   with notation `[]`, `::`, `[1, 2, 3]`, and `++`. -/

/- FULL: Using Lean's built-in list notation, we can now write lists
   in the natural way:
   TERSE: Using Lean's notation, we can write lists naturally: -/

def list123 : List Nat := [1, 2, 3]

/- ######################################################
   ### Type Annotation Inference -/

/- TODO: (DHS) I copied this over mostly verbatim from Poly.v,
   but I think the point doesn't work in Lean. The definition of `repeat'`
   below doesn't typecheck, I think Lean does less inference than Rocq here.
   Should we just delete this? -/
/- TODO: (JC) Lean can still infer the types of arguments that are used dependently,
   so I've adapted the text below to only omit `α`. The question of what Lean infers
   as its type is still tricky to present, since `#check repeat'` alone will show
   that `α` is universe-polymorphic as well, which I suppose we want to avoid
   explaining at this moment? -/

/- Let's write the definition of `repeat` again, but this time we won't specify
    the type of the parameter `α`. Will Lean still accept it? -/

@[irreducible]
def repeat' α (x : α) (count : Nat) : List α :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (repeat' α x count')

/- Indeed it will. We can see that `α` has the type `Type`, as expected. -/

#check (repeat' : ∀ (α : Type), α → Nat → List α)

/- TERSE: Lean has used _type inference_ to deduce a type for `α`. -/
/- FULL: Lean was able to use _type inference_ to decude what the type of `α`
    must be, based on how it is used. Since `α` is an argument to `List`,
    it must be a `Type`, since `List` expects a `Type` as its argument.

    This facility means we don't always have to write explicit type annotations
    everywhere, although explicit type annotations can still be quite useful
    as documentation, so we will continue to use them much of the time. -/

-- HIDE
/-
(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments. Will Rocq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** TERSE: *** *)
(** Indeed it will. Let's see what type Rocq has assigned to [repeat']... *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** TERSE: Rocq has used _type inference_ to deduce the proper types
    for [X], [x], and [count]. *)
(** FULL: It has exactly the same type as [repeat]. Rocq was able to
    use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used. For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations can still be quite useful as documentation and sanity
    checks, so we will continue to use them much of the time. *)
(* HIDE: (BCP '19) Deleted, for streamlining: "You should try to find
    a balance in your own code between too many type
    annotations (which can clutter and distract) and too few (which
    can sometimes require readers to perform complex type inference in
    their heads in order to understand your code)."
     -/

-- /HIDE

/- ######################################################
   ### Type Argument Synthesis -/

/- FULL: To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments. For example, the
    recursive call in the body of the `myRepeat` function above must
    pass along the type `α`. But since the second argument to
    `myRepeat` is an element of `α`, it seems entirely obvious that the
    first argument can only be `α` -- why should we have to write it
    explicitly?

    Fortunately, Lean permits us to avoid this kind of redundancy. In
    place of any type argument we can write a "hole" `_`, which can be
    read as "Please try to figure out for yourself what belongs here."
    More precisely, when Lean encounters a `_`, it will attempt to
    _unify_ all locally available information -- the type of the
    function being applied, the types of the other arguments, and the
    type expected by the context in which the application appears --
    to determine what concrete type should replace the `_`.

    Using holes, the [repeat] function can be written like this: -/
/- TERSE: Supplying every type _argument_ is also boring, but Lean
    can usually infer them: -/

def myRepeat'' (α : Type) (x : α) (count : Nat) : List α :=
  match count with
  | 0        => []
  | count' + 1 => x :: myRepeat'' _ x count'

/- FULL: Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parentheses. For example: -/
/- TERSE: Alternatively, we can declare arguments implicit by
    surrounding them with curly braces instead of parens: -/

def myRepeat''' {α : Type} (x : α) (count : Nat) : List α :=
  match count with
  | 0        => []
  | count' + 1 => x :: myRepeat''' x count'

-- FULL
/- (Note that we didn't even have to provide a type argument to the
    recursive call to myRepeat'''. Indeed, it would be invalid to
    provide one, because Lean is not expecting it.) -/
-- /FULL

/- ######################################################
   ### Supplying Type Arguments Explicitly -/

/- FULL: One small problem with implicit arguments is that, once in a
   while, Lean does not have enough local information to determine
   a type argument; in such cases, we need to tell Lean the type
   explicitly. For example: -/

/- TERSE: In general, it's fine to just let Lean infer all type
   arguments. But occasionally this can lead to problems: -/

/- This fails because Lean can't figure out the type of the empty list:
   `def mynil := []` -- error: type not known
   We can fix this with an explicit type annotation: -/

/- We can use the `@` prefix to supply the type
   argument explicitly. The `@` makes all implicit arguments
   of a function explicit: -/

-- TODO: (JC) Didn't we alredy use this feature back on lines 121/126?

#check (@List.nil : {α : Type} → List α)

def mynil' := @List.nil Nat

/- TERSE: *** -/

/- HIDEFROMADVANCED
   TERSE: HIDEFROMHTML -/

/- TERSE
   QUIZ
   Which type does Lean assign to the following expression?
   HIDEFROMHTML
   (The square brackets in this quiz and the following ones are list
   brackets.)
   /HIDEFROMHTML
[[
       [1, 2, 3]
]]

   (A) `List Nat`

   (B) `List Bool`

   (C) `Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (A) -/

/- QUIZ
   What about this one?
[[
       [3 + 4] ++ []
]]

   (A) `List Nat`

   (B) `List Bool`

   (C) `Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (A) -/

/- QUIZ
   What about this one?
[[
       (true && false) :: []
]]

   (A) `List Nat`

   (B) `List Bool`

   (C) `Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (B) -/

/- QUIZ
   What about this one?
[[
       [1, []]
]]

   (A) `List Nat`

   (B) `List (List Nat)`

   (C) `List Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (D) -/

/- QUIZ
   What about this one?
[[
       [[1], []]
]]

   (A) `List Nat`

   (B) `List (List Nat)`

   (C) `List Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (B) -/

/- QUIZ
   And what about this one?
[[
       [1] :: [[]]
]]

   (A) `List Nat`

   (B) `List (List Nat)`

   (C) `List Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (B) -/

/- QUIZ
   This one?
[[
       @List.nil Bool
]]

   (A) `List Nat`

   (B) `List (List Nat)`

   (C) `List Bool`

   (D) No type can be assigned
   /QUIZ
   INSTRUCTORS: (C) -/

/- /TERSE -/

/- TERSE: /HIDEFROMHTML -/

/- FULL -/

/- EX2M? (mumble_grumble) -/
/- Consider the following two inductively defined types. -/

namespace MumbleGrumble

inductive Mumble : Type where
  | a : Mumble
  | b (x : Mumble) (y : Nat) : Mumble
  | c : Mumble

inductive Grumble (X: Type) : Type where
  | d (m : Mumble) : Grumble X
  | e (x : X) : Grumble X

/- Which of the following are well-typed elements of `Grumble X` for
    some type `X`?  (Add YES or NO to each line.)
      - [Grumble.d (Grumble.b Grumble.a 5)]
      - [@Grumble.d Mumble (Mumble.b Mumble.a 5)]
      - [@Grumble.d Bool (Mumble.b Mumble.a 5)]
      - [@Grumble.e Bool true]
      - [@Grumble.e Mumble (Mumble.b Mumble.c 0)]
      - [@Grumble.e Bool (Mumble.b Mumble.c 0)]
      - [Mumble.c]  -/
-- SOLUTION
/-    YES - [Grumble.d (Grumble.b Grumble.a 5)]
      YES - [@Grumble.d Mumble (Mumble.b Mumble.a 5)]
      YES - [@Grumble.d Bool (Mumble.b Mumble.a 5)]
      YES - [@Grumble.e Bool true]
      YES - [@Grumble.e Mumble (Mumble.b Mumble.c 0)]
      NO  - [@Grumble.e Bool (Mumble.b Mumble.c 0)]
      NO  - [Mumble.c] -/
-- /SOLUTION
end MumbleGrumble
/- [] -/
/- /FULL -/

/- ######################################################
   ### Exercises -/

seal List.append
seal List.length

@[irreducible]
def List.rev {α:Type} (l:List α) : List α :=
  match l with
  | .nil => .nil
  | .cons h t => rev t ++ (.cons h .nil)

unseal List.rev in
theorem rev_nil α : ([] : List α).rev = [] := by rfl

unseal List.rev in
theorem rev_cons α h (t : List α) : (h :: t).rev = t.rev ++ [h] := by rfl

/- TERSE: HIDEFROMHTML -/

/- EX2 (poly_exercises)
   Here are a few simple exercises, just like ones in the `Lists`
   chapter, for practice with polymorphism. Complete the proofs below.
   You will likely find useful the following lemmas about append and length
   from Lean's standard library:

      `List.nil_append {α} (as : List α) : [] ++ as = as`
      `List.cons_append {α} {a : α} {as bs : List α} : a :: as ++ bs = a :: (as ++ bs)`
   -/

/- INSTRUCTORS: There's a little inconsistency between this definition
   and the standard library one: in the library, the type argument is
   implicit. :-( I (BCP) have chosen to leave things inconsistent to
   avoid having to explain about implicit arguments to theorems, which
   wouldn't make sense at this point. -/

/- app_nil_r -/
theorem app_nil_r {α : Type} : ∀ (l : List α),
    l ++ [] = l := by
  /- ADMITTED -/
  intro l; induction l
  case nil => rw [List.nil_append]
  case cons h t ih =>
   rw [List.cons_append, ih]
/- /ADMITTED -/

/- app_assoc -/
theorem app_assoc {α : Type} : ∀ (l m n : List α),
    l ++ m ++ n = l ++ (m ++ n) := by
  /- ADMITTED -/
  intro l m n; induction l
  case nil => rw [List.nil_append, List.nil_append]
  case cons h t ih =>
   dsimp [List.cons_append]
   rw [ih]
/- /ADMITTED -/

/- app_length -/
theorem app_length {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).length = l1.length + l2.length := by
  /- ADMITTED -/
  intro l1 l2; induction l1
  case nil => dsimp [List.nil_append, app_nil_r]; rw [Nat.zero_add]
  case cons h t ih =>
   dsimp [List.cons_append, List.length_cons]
   rw [Nat.succ_add, ih]
/- /ADMITTED -/
/-
   GRADE_THEOREM 0.5: app_nil_r
   GRADE_THEOREM 1: app_assoc
   GRADE_THEOREM 0.5: app_length
   [] -/

/- EX2 (more_poly_exercises)
   Here are some slightly more interesting ones... -/

/- rev_app_distr -/
theorem rev_app_distr {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  /- ADMITTED -/
  intro l1 l2; induction l1
  case nil =>
   dsimp [List.nil_append]
   rw [rev_nil, app_nil_r]
  case cons h t ih =>
   dsimp [List.cons_append]
   rw [rev_cons, rev_cons, ih, app_assoc]
/- /ADMITTED -/

/- rev_involutive -/
theorem rev_involutive {α : Type} : ∀ (l : List α),
    l.rev.rev = l := by
  /- ADMITTED -/
  intro l; induction l
  case nil =>
   rw [rev_nil, rev_nil]
  case cons h t ih =>
   rw [rev_cons, rev_app_distr, ih, rev_cons, rev_nil]
   dsimp only [List.nil_append, List.cons_append]
/- /ADMITTED -/
/-
   GRADE_THEOREM 1: rev_app_distr
   GRADE_THEOREM 1: rev_involutive
   []
   /HIDEFROMADVANCED
   HIDEFROMADVANCED
   TERSE: /HIDEFROMHTML
   /HIDEFROMADVANCED -/

/- ######################################################################
   ## Polymorphic Pairs -/

/- Like `inductive`s, `structure`s can also be made polymorphic.
   If we generalize the definition `NatProd` of pairs of natural numbers from last chapter,
   we get polymorphic pairs, often called _products_: -/

structure MyProd (α β : Type) where
  fst : α
  snd : β

/- Lean's built-in product type `Prod` provides a `Prod.mk` constructor,
   and `fst` and `snd` functions for accessing the first and second components
   of the pair. It also has special syntax for creating products: -/

#check (1, true)  /- (1, true) : Nat × Bool -/
#check (1, true).fst  /- access first component -/
#check (1, true).snd  /- access second component -/

/- You can also use `.1` instead of `.fst` and `.2` instead of `.snd` -/

#check (1, true).1  /- access first component -/
#check (1, true).2  /- access second component -/

/- fst_example -/
example : (3, 5).1 = 3 := by rfl
/- snd_example -/
example : (3, 5).2 = 5 := by rfl

/- The notation `α × β` is syntactic sugar for `Prod α β`. -/

/- FULL:
    It is easy at first to get `(x, y)` and `α × β` confused.
    Remember that `(x, y)` is a _value_ built from two other values,
    while `α × β` is a _type_ built from two other types. If `x` has
    type `α` and `y` has type `β`, then `(x, y)` has type `α × β`.
-/

/- TERSE: Be careful not to get `(x, y)` and `α × β` confused!
   TERSE: *** -/

/- FULL: The following function takes two lists and combines them
   into a list of pairs.
   TERSE: ***
   TERSE: What does this function do? -/

@[irreducible]
def zip {α : Type} {β : Type} (lx : List α) (ly : List β) : List (α × β) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: zip tx ty

unseal zip in
theorem zip_nil_r α β ly : zip [] ly = ([] : List (α × β)) := by rfl

unseal zip in
theorem zip_nil_l α β lx : zip lx [] = ([] : List (α × β)) := by
   cases lx
   . rfl
   . rfl

unseal zip in
theorem zip_cons α β lx ly (x : α) (y : β) :
   zip (x :: lx) (y :: ly) = (x, y) :: zip lx ly := by rfl

/- FULL
   EX1M? (zip_checks)
   Try answering the following questions on paper and
   checking your answers in Lean:
   - What is the type of `zip` (i.e., what does `#check @zip`
     print?)
   - What does
[[
         #eval zip [1, 2] [false, false, true, true]
]]
     print?
   [] -/

/- EX2! (split)
   The function `unzip` is the right inverse of `zip`: it takes a
   list of pairs and returns a pair of lists.

   Fill in the definition of `unzip` below. Make sure it passes the
   given unit test, and you can prove the simplification lemmas about it -/

@[irreducible]
def unzip {α : Type} {β : Type} (l : List (α × β)) : List α × List β :=
  /- ADMITDEF -/
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    let (lx, ly) := unzip t
    (x :: lx, y :: ly)
  /- /ADMITDEF -/


unseal unzip in
theorem unzip_nil α β : unzip [] = (([], []) : List α × List β) := by rfl /- ADMITTED -/

unseal unzip in
theorem unzip_cons_fst α β l (x : α) (y : β) :
   (unzip ((x, y) :: l)).fst = x :: (unzip l).fst := by dsimp [unzip] /- ADMITTED -/

unseal unzip in
theorem unzip_cons_snd α β l (x : α) (y : β) :
   (unzip ((x, y) :: l)).snd = y :: (unzip l).snd := by dsimp [unzip] /- ADMITTED -/

/- test_split -/
unseal unzip in
example : unzip [(1, false), (2, false)] = ([1, 2], [false, false]) := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 1: split
   GRADE_THEOREM 1: test_split
   []
   /FULL -/

/- ######################################################################
   ## Polymorphic Options -/

/- FULL: Our last polymorphic type for now is _polymorphic options_.
   Lean's standard library provides `Option α`, with constructors
   `none` and `some x`. (We already saw `Option Nat` in the
   previous chapter.)  Let's briefly look at the definition:

   inductive Option (α : Type) : Type where
      | none : Option α
      | some (x : α) : Option α

-/
/- TERSE: ***
   FULL: We can now rewrite the `nth_error` function so that it works
   with any type of list. -/

@[irreducible]
def nthError {α : Type} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | a :: l' => match n with
    | 0 => some a
    | n' + 1 => nthError l' n'

/- HIDEFROMADVANCED
   test_nth_error1 -/
unseal nthError
example : nthError [4, 5, 6, 7] 0 = some 4 := by rfl
/- test_nth_error2 -/
example : nthError [[1], [2]] 1 = some [2] := by rfl
/- test_nth_error3 -/
example : nthError [true] 2 = none := by rfl
seal nthError

/- /HIDEFROMADVANCED
   FULL
   EX1? (hd_error_poly)
   Complete the definition of a polymorphic version of the
   `hd_error` function from the last chapter. Be sure that it
   passes the unit tests below. -/

@[irreducible]
def hdError {α : Type} (l : List α) : Option α :=
  /- ADMITDEF -/
  match l with
  | [] => none
  | a :: _ => some a
  /- /ADMITDEF -/

#check hdError  /- hdError : {α : Type} → List α → Option α -/

unseal hdError in
theorem hd_error_nil α : hdError ([] : List α) = none := by rfl -- ADMITTED

unseal hdError in
theorem hd_error_cons α (h : α) t : hdError (h :: t) = some h := by rfl -- ADMITTED

/- test_hd_error1 -/
unseal hdError in
example : hdError [1, 2] = some 1 := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 0.5: test_hd_error1
   test_hd_error2 -/
unseal hdError in
example : hdError [[1], [2]] = some [1] := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 0.5: test_hd_error2
   []
   /FULL -/

/- ######################################################################
   # Functions as Data -/

/- HIDEFROMADVANCED
   FULL: Like most modern programming languages -- especially other
   "functional" languages, including OCaml, Haskell, Racket, Scala,
   Clojure, etc. -- Lean treats functions as first-class citizens,
   allowing them to be passed as arguments to other functions,
   returned as results, stored in data structures, etc. -/

/- HIDE: Robert Rand: The terse version could really use words
   here. (Or drop the section break and rename this one to
   "Higher-Order Functions" -/
/- /HIDEFROMADVANCED -/

/- ######################################################################
   ## Higher-Order Functions -/

/- HIDEFROMADVANCED
   FULL: Functions that manipulate other functions are often called
   _higher-order_ functions. Here's a simple one:
   TERSE: Functions in Lean are _first class_. -/

abbrev doit3times {α : Type} (f : α → α) (n : α) : α :=
  f (f (f n))

/- FULL: The argument `f` here is itself a function (from `α` to
   `α`); the body of `doit3times` applies `f` three times to some
   value `n`. -/

#check @doit3times  /- @doit3times : {α : Type} → (α → α) → α → α -/

/- test_doit3times -/
example : doit3times minustwo 9 = 3 := by rfl

/- test_doit3times' -/
example : doit3times not true = false := by rfl

/- ######################################################################
   ## Filter -/

/- INSTRUCTORS: We've tried to be careful with terminology in the rest
   of the notes: "(boolean) predicate" for boolean functions and
   "property" for propositions indexed by one parameter. -/

/- /HIDEFROMADVANCED
   FULL: Here is a more useful higher-order function, taking a list
   of `α`s and a _predicate_ on `α` (a function from `α` to `Bool`)
   and "filtering" the list to yield a new list containing just
   those elements for which the predicate returns `true`. -/

@[irreducible]
def filter {α : Type} (test : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t =>
    bif test h then h :: filter test t
    else filter test t

/- FULL: For example, if we apply `filter` to the predicate `Nat.even`
   and a list of numbers, it returns a list containing just the
   even members. -/

/- test_filter1 -/
unseal filter in
example : filter even [1, 2, 3, 4] = [2, 4] := by rfl

/- TERSE: *** -/
abbrev lengthIs1 {α : Type} (l : List α) : Bool :=
  l.length == 1

/- test_filter2 -/
unseal filter in
example : filter lengthIs1
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by dsimp [filter, lengthIs1]

unseal filter in
theorem filter_nil {α : Type} {test : α → Bool} : filter test [] = [] := by rfl

unseal filter in
theorem filter_cons_success {α : Type} {test : α → Bool} h t :
   test h -> filter test (h :: t) = h :: filter test t := by
   intro htest
   dsimp [filter]
   rw [htest]
   dsimp

unseal filter in
theorem filter_cons_fail {α : Type} {test : α → Bool} h t :
   test h = false -> filter test (h :: t) = filter test t := by
   intro htest
   dsimp [filter]
   rw [htest]
   dsimp


-- TERSE: ***
/- LATER: This material would sink in better if it were made clearer
   why map and filter and such were useful in the real world. Talk
   about map/reduce, collection-oriented programming, etc. Esp in the
   terse version. -/
/- TERSE: The `filter` function (especially when combined with some
    other functions we'll see later) enables a powerful
    _wholemeal_ (or _collection-oriented_) programming style. -/
/- FULL: We can use `filter` to give a concise version of the
    `countoddmembers` function from the `Lists` chapter. -/

abbrev countoddmembers' (l : List Nat) : Nat :=
  (filter odd l).length

/- test_countoddmembers'1 -/
unseal filter
unseal List.length
example : countoddmembers' [1, 0, 3, 1, 4, 5] = 4 := by rfl
/- test_countoddmembers'2 -/
example : countoddmembers' [0, 2, 4] = 0 := by rfl
/- test_countoddmembers'3 -/
example : countoddmembers' [] = 0 := by rfl
seal filter
seal List.length

/- /HIDEFROMADVANCED -/

/- ######################################################################
   ## Anonymous Functions -/

/- HIDE: Why not show them [fix] here?  It's not that complicated and
   it fills out the story. At least as a little optional section.
   BAY: I'm not convinced it's "not that complicated" for people who
   have never seen much functional programming before. I think adding
   a discussion of fix could easily take 20 minutes of class time.
   BCP: Yes, this doesn't belong in lecture, probably. But it might
   still be useful as an optional section for people to read.
   (2013: Now that we've created the idea of "advanced" sections, this
   seems like a nice candidate.) -/

/- FULL: It is arguably a little sad, in the example just above, to
   be forced to define the function `lengthIs1` and give it a name
   just to be able to pass it as an argument to `filter`, since we
   will probably never use it again. Indeed, when using higher-order
   functions, we _often_ want to pass as arguments "one-off"
   functions that we will never use again; having to give each of
   these functions a name would be tedious.

   Fortunately, there is a better way. We can construct a function
   "on the fly" without declaring it at the top level or giving it a
   name. Lean provides two syntaxes for anonymous functions:

   - `fun n => n * n` -- traditional lambda syntax
   - `(· * ·)` -- "term with holes" syntax, where `·` marks arguments
   TERSE: Functions can be constructed "on the fly" without giving
   them names.
   HIDEFROMADVANCED -/

/- test_anon_fun' -/
example : doit3times (fun n => n * n) 2 = 256 := by rfl

/- The expression `fun n => n * n` can be read as "the function
   that, given a number `n`, yields `n * n`."

   Lean also supports a shorter notation using `·` as a placeholder
   for the argument: -/

/- test_anon_fun'' -/
example : doit3times (· + 1) 0 = 3 := by rfl

/- /HIDEFROMADVANCED
   FULL: Here is the `filter` example, rewritten to use an anonymous
   function. -/

/- test_filter2' -/
unseal filter
unseal List.length
example : filter (fun l => l.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl

example : filter (·.length == 1)
    [[1, 2], [3], [4], [5, 6, 7], [], [8]]
  = [[3], [4], [8]] := by rfl
seal filter
seal List.length

/- FULL
   EX2 (filter_even_gt7)
   Use `filter` (instead of a recursive `def`) to write a Lean function
   `filterEvenGt7` that takes a list of natural numbers as input
   and returns a list of just those that are even and greater than 7. -/

abbrev filterEvenGt7 (l : List Nat) : List Nat :=
  /- ADMITDEF -/
  filter (fun n => even n && n > 7) l
  /- /ADMITDEF -/

/- test_filter_even_gt7_1 -/
unseal filter
unseal List.length
example : filterEvenGt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := by rfl  /- ADMITTED -/

/- test_filter_even_gt7_2 -/
example : filterEvenGt7 [5, 2, 6, 19, 129] = [] := by rfl  /- ADMITTED -/
seal filter
seal List.length
/- GRADE_THEOREM 1: test_filter_even_gt7_1
   GRADE_THEOREM 1: test_filter_even_gt7_2
   [] -/


/- EX3 (partition)
   Use `filter` to write a Lean function `partition` that, given a
   type `α`, a predicate of type `α → Bool` and a `List α`, should
   return a pair of lists. The first member of the pair is the sublist
   of the original list containing the elements that satisfy the test,
   and the second is the sublist containing those that fail the test.
   The order of elements in the two sublists should be the same as
   their order in the original list. -/

abbrev partition {α : Type} (test : α → Bool) (l : List α) : List α × List α :=
  /- ADMITDEF -/
  (filter test l, filter (!test ·) l)
  /- /ADMITDEF -/

unseal filter
unseal List.length
/- test_partition1 -/
example : partition (· % 2 != 0) [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) := by rfl  /- ADMITTED -/
/- test_partition2 -/
example : partition (fun _ => false) [5, 9, 0] = ([], [5, 9, 0]) := by rfl  /- ADMITTED -/
seal filter
seal List.length
/- GRADE_THEOREM 1: partition
   GRADE_THEOREM 1: test_partition1
   GRADE_THEOREM 1: test_partition2
   []
   /FULL -/

/- ######################################################################
   ## Map -/

/- FULL: Another handy higher-order function is called `map`. -/

@[irreducible]
def map {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  match l with
  | [] => []
  | h :: t => f h :: map f t

/- FULL: It takes a function `f` and a list `l = [n1, n2, n3, ...]`
   and returns the list `[f n1, f n2, f n3, ...]`, where `f` has
   been applied to each element of `l` in turn. For example: -/

/- test_map1 -/
unseal map in
example : map (· + 3) [2, 0, 2] = [5, 3, 5] := by rfl

/- HIDEFROMADVANCED
   FULL: The element types of the input and output lists need not be
   the same, since `map` takes _two_ type arguments, `α` and `β`; it
   can thus be applied to a list of numbers and a function from
   numbers to booleans to yield a list of booleans: -/

/- test_map2 -/
unseal map in
example : map odd [2, 1, 2, 5] = [false, true, false, true] := by rfl

/- FULL: It can even be applied to a list of numbers and
   a function from numbers to _lists_ of booleans to
   yield a _list of lists_ of booleans: -/

/- test_map3 -/
unseal map in
example : map (fun n => [even n, odd n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by rfl

/- TERSE
   QUIZ
   Recall the definition of `map`:
[[
       def map (f : α → β) (l : List α) : List β :=
         match l with
         | [] => []
         | h :: t => f h :: map f t
]]
   What is the type of `@map`?

   (A) `{α β : Type} → α → β → List α → List β`

   (B) `α → β → List α → List β`

   (C) `{α β : Type} → (α → β) → List α → List β`

   (D) `{α : Type} → (α → α) → List α → List α`
   /QUIZ -/

/- /TERSE -/

/- TERSE: ***
   FULL: *** Exercises -/

unseal map in
theorem map_nil {α : Type} {β : Type} (f : α → β) : map f [] = [] := by rfl

unseal map in
theorem map_cons {α : Type} {β : Type} (f : α → β) h t : map f (h :: t) = f h :: map f t := by rfl

/- FULL
   EX3 (map_rev)
   Show that `map` and `reverse` commute. (Hint: You may need to
   define an auxiliary lemma.)
   QUIETSOLUTION -/

theorem map_app {α : Type} {β : Type} : ∀ (f : α → β) (l l' : List α),
    map f (l ++ l') = map f l ++ map f l' := by
  intro f l l'
  induction l
  case nil => rw [map_nil, List.nil_append, List.nil_append]
  case cons h t ih =>
   rw [List.cons_append, map_cons, map_cons, ih, List.cons_append]

/- /QUIETSOLUTION -/

/- map_rev -/
theorem map_rev {α : Type} {β : Type} : ∀ (f : α → β) (l : List α),
    map f l.rev = (map f l).rev := by
  /- ADMITTED -/
  intro f l
  induction l
  case nil =>
   rw [rev_nil, map_nil, rev_nil]
  case cons h t ih =>
   rw [rev_cons, map_cons, map_app, rev_cons, ih, map_cons, map_nil]
/- /ADMITTED -/
/-
   GRADE_THEOREM 3: map_rev
   [] -/

/- EX2! (flat_map)
   The function `map` maps a `List α` to a `List β` using a function
   of type `α → β`. We can define a similar function, `flatMap`,
   which maps a `List α` to a `List β` using a function `f` of type
   `α → List β`. Your definition should work by 'flattening' the
   results of `f`, like so:
[[
       flatMap (fun n => [n, n + 1, n + 2]) [1, 5, 10]
         = [1, 2, 3, 5, 6, 7, 10, 11, 12]
]] -/

@[irreducible]
def flatMap {α : Type} {β : Type} (f : α → List β) (l : List α) : List β :=
  /- ADMITDEF -/
  match l with
  | [] => []
  | h :: t => f h ++ flatMap f t
  /- /ADMITDEF -/

/- test_flat_map1 -/
unseal flatMap in
unseal List.append in
example : flatMap (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 1: flatMap
   GRADE_THEOREM 1: test_flat_map1
   [] -/

unseal flatMap in
theorem flatMap_nil {α : Type} {β : Type} (f : α → List β) : flatMap f [] = [] :=
   by rfl -- ADMITTED

unseal flatMap in
theorem flatMap_cons {α : Type} {β : Type} (f : α → List β) h t :
   flatMap f (h :: t) = f h ++ flatMap f t := by rfl -- ADMITTED
/- /FULL
   HIDEFROMADVANCED -/

/- Lists are not the only inductive type for which `map` makes sense.
   Here is a `map` for the `Option` type: -/

@[irreducible]
def optionMap {α : Type} {β : Type} (f : α → β) (x? : Option α) : Option β :=
  match x? with
  | none => none
  | some x => some (f x)

/- /HIDEFROMADVANCED
   FULL
   EX2? (implicit_args)
   The definitions and uses of `filter` and `map` use implicit
   arguments in many places. Replace the curly braces around the
   implicit arguments with explicit parentheses, and then fill in
   explicit type parameters where necessary and use Lean to check that
   you've done so correctly. (This exercise is not to be turned in;
   it is probably easiest to do it on a _copy_ of this file that you
   can throw away afterwards.)
   []
   /FULL
   /HIDEFROMADVANCED -/

/- ######################################################################
   ## Fold -/

/- FULL: An even more powerful higher-order function is called
   `fold`. This function is the inspiration for the "reduce"
   operation that lies at the heart of Google's map/reduce
   distributed programming framework. -/

@[irreducible]
def fold {α : Type} {β : Type} (f : α → β → β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

/- TERSE: This is the "reduce" in map/reduce... -/

/- HIDEFROMADVANCED
   TERSE: *** -/

/- FULL: Intuitively, the behavior of the `fold` operation is to
   insert a given binary operator `f` between every pair of elements
   in a given list. For example, `fold (· + ·) [1, 2, 3, 4]`
   intuitively means `1 + 2 + 3 + 4`. To make this precise, we also
   need a "starting element" that serves as the initial second input
   to `f`. So, for example,
[[
       fold (· + ·) [1, 2, 3, 4] 0
]]
   yields
[[
       1 + (2 + (3 + (4 + 0))).
]] -/

/- fold_example1 -/
unseal fold
example : fold (· && ·) [true, true, false, true] true = false := by rfl

/- fold_example2 -/
example : fold (· * ·) [1, 2, 3, 4] 1 = 24 := by rfl

/- fold_example3 -/
unseal List.append in
example : fold (· ++ ·) [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4] := by rfl

/- fold_example4 -/
unseal List.length in
example : fold (fun l n => l.length + n) [[1], [], [2, 3, 2], [4]] 0 = 5 := by rfl
seal fold

unseal fold in
theorem fold_nil {α : Type} {β : Type} (f : α → β → β) (b : β) : fold f [] b = b := by rfl

unseal fold in
theorem fold_cons {α : Type} {β : Type} (f : α → β → β) h t (b : β) :
   fold f (h :: t) b = f h (fold f t b) := by rfl

/- TERSE
   QUIZ
   Here is the definition of `fold` again:
[[
       def fold (f : α → β → β) (l : List α) (b : β) : β :=
         match l with
         | [] => b
         | h :: t => f h (fold f t b)
]]
   What is the type of `@fold`?

   (A) `{α β : Type} → (α → β → β) → List α → β → β`

   (B) `α → β → (α → β → β) → List α → β → β`

   (C) `{α β : Type} → α → β → β → List α → β → β`

   (D) `α → β → α → β → β → List α → β → β`
   /QUIZ -/

/- QUIZ
   What does `fold (· + ·) [1, 2, 3, 4] 0` simplify to?

   (A) `[1, 2, 3, 4]`

   (B) `0`

   (C) `10`

   (D) `[3, 7, 0]`
   /QUIZ
   /TERSE
   /HIDEFROMADVANCED -/

/- FULL
   EX1M? (fold_types_different)
   Observe that the type of `fold` is parameterized by _two_ type
   variables, `α` and `β`, and the parameter `f` is a binary operator
   that takes an `α` and a `β` and returns a `β`. Example
   `fold_example4` above shows one instance where it is useful for `α`
   and `β` to be different. Can you think of any others? -/

/- SOLUTION
   There are many. For example, we could use `fold` to count the
   number of `true` elements in a list of booleans. Here `α` would
   be `Bool` and `β` would be `Nat`.
   /SOLUTION
   []
   /FULL -/

/- HIDEFROMADVANCED
   ######################################################################
   ## Functions That Construct Functions -/

/- FULL: Most of the higher-order functions we have talked about so
   far take functions as arguments. Let's look at some examples that
   involve _returning_ functions as the results of other functions.
   To begin, here is a function that takes a value `x` (drawn from
   some type `α`) and returns a function from `Nat` to `α` that
   yields `x` whenever it is called, ignoring its `Nat` argument.
   TERSE: Here are two functions that _return_ functions as results. -/

abbrev constfun {α : Type} (x : α) : Nat → α :=
  fun _ => x

abbrev ftrue := constfun true

/- constfun_example1 -/
example : ftrue 0 = true := by rfl

/- constfun_example2 -/
example : constfun 5 99 = 5 := by rfl

/- FULL: In fact, the multiple-argument functions we have already
   seen are also examples of passing functions as data. To see why,
   recall the type of addition:
   TERSE: ***
   TERSE: A two-argument function in Lean is actually a function that
   returns a function! -/

#check (Nat.add : Nat → Nat → Nat)

abbrev plus3 := Nat.add 3
#check (plus3 : Nat → Nat)

/- test_plus3 -/
example : plus3 4 = 7 := by rfl
/- test_plus3' -/
example : doit3times plus3 0 = 9 := by rfl
/- test_plus3'' -/
example : doit3times (Nat.add 3) 0 = 9 := by rfl

/- Similarly, we can write: -/
abbrev fold_plus : List Nat → Nat → Nat :=
  fold (· + ·)

#check (fold_plus : List Nat → Nat → Nat)

/- FULL: What's happening here is called _partial application_. In
   Lean, the type constructor `→` is right-associative, meaning a
   function type like `α → β → γ` is parsed like `α → (β → γ)`,
   or "a function from `α` to a function from `β` to `γ`."

   We can think of `fold` not as a three-argument function, but as a
   one-argument function that:

   1. Takes an argument `f` of type `α → β → β`
   2. Returns a function of type `List α → β → β` that "remembers" `f`

   When we write `fold (· + ·)`, we're giving `fold` its first argument,
   `(· + ·)`, and getting back a specialized function that can sum up
   the elements of any list of numbers. This new function still expects
   two more arguments: a list and a starting value. -/

/- FULL
   ######################################################################
   # Additional Exercises -/

namespace Exercises

/- EX2 (fold_length)
   Many common functions on lists can be implemented in terms of
   `fold`. For example, here is an alternative definition of `length`: -/

abbrev foldLength {α : Type} (l : List α) : Nat :=
  fold (fun _ n => n + 1) l 0

/- test_fold_length1 -/
unseal fold in
unseal List.length in
example : foldLength [4, 7, 0] = 3 := by rfl

/- Prove the correctness of `foldLength`.

   Hint: It may help to use `dsimp [foldLength, fold]` to unfold
   the definition. -/

/- fold_length_correct -/
theorem fold_length_correct {α : Type} (l : List α) :
    foldLength l = l.length := by
  /- ADMITTED -/
  induction l
  case nil =>
   dsimp only [foldLength]
   rw [fold_nil, List.length_nil]
  case cons h t ih =>
    dsimp only [foldLength] at *
    rw [List.length_cons, fold_cons, ih]
/- /ADMITTED -/
/-
   GRADE_THEOREM 2: Exercises.fold_length_correct
   [] -/

/- EX3M (fold_map)
   We can also define `map` in terms of `fold`. Finish `foldMap`
   below. -/

abbrev foldMap {α : Type} {β : Type} (f : α → β) (l : List α) : List β :=
  /- ADMITDEF -/
  fold (fun x l' => f x :: l') l []
  /- /ADMITDEF -/

/- Write down a theorem `fold_map_correct` stating that `foldMap` is
   correct, and prove it in Lean. -/

/- SOLUTION -/
/- fold_map_correct -/
theorem fold_map_correct {α : Type} {β : Type} (f : α → β) (l : List α) :
    foldMap f l = map f l := by
  induction l
  case nil => dsimp only [foldMap]; rw [fold_nil, map_nil]
  case cons h t ih =>
    dsimp only [foldMap] at *
    rw [fold_cons, map_cons, ih]
/- /SOLUTION -/

/- GRADE_MANUAL 3: fold_map
   [] -/

/- EX2A (currying)
   The type `α → β → γ` can be read as describing functions that
   take two arguments, one of type `α` and another of type `β`, and
   return an output of type `γ`. Recall from our discussion
   of partial application that this type is written `α → (β → γ)`
   when fully parenthesized. That is, if we have `f : α → β → γ`,
   and we give `f` an input of type `α`, it will give us as output
   a function of type `β → γ`. If we then give that function an
   input of type `β`, it will return an output of type `γ`. That
   is, every function in Lean takes only one input, but some
   functions return a function as output. This is precisely
   what enables partial application, as we saw above with `plus3`.

   By contrast, functions of type `α × β → γ` -- which when fully
   parenthesized is written `(α × β) → γ` -- require their single
   input to be a pair. Both arguments must be given at once; there
   is no possibility of partial application.

   It is possible to convert a function between these two types.
   Converting from `α × β → γ` to `α → β → γ` is called
   _currying_, in honor of the logician Haskell Curry. Converting
   from `α → β → γ` to `α × β → γ` is called _uncurrying_. -/

/- We can define currying as follows: -/

abbrev prodCurry {α β γ : Type} (f : α × β → γ) (x : α) (y : β) : γ := f (x, y)

/- As an exercise, define its inverse, `prodUncurry`. Then prove
   the theorems below to show that the two are really inverses. -/

abbrev prodUncurry {α β γ : Type} (f : α → β → γ) (p : α × β) : γ :=
  /- ADMITDEF -/
  f p.fst p.snd
  /- /ADMITDEF -/

/- As a (trivial) example of the usefulness of currying, we can use it
   to shorten one of the examples that we saw above: -/

/- test_map1' -/
unseal map in
example : map (Nat.add 3) [2, 0, 2] = [5, 3, 5] := by rfl

/- Thought exercise: before running the following commands, can you
   calculate the types of `prodCurry` and `prodUncurry`? -/

#check @prodCurry
#check @prodUncurry

/- HIDE: Maybe this is a good place to introduce the lack of
   functional extensionality? Here, at the latest, the reader may have
   started to wonder why the next two theorems, rather than claiming
   the equality of functions, claim equalities for their values...
   BCP 9/16: On reflection, I think this is not the place. It's an
   advanced exercise, so not everybody will see it, and we do come
   back to it in detail in a couple chapters. -/

/- uncurry_curry -/
theorem uncurry_curry {α β γ : Type} (f : α → β → γ) (x : α) (y : β) :
    prodCurry (prodUncurry f) x y = f x y := by
  /- ADMITTED -/
  rfl
/- /ADMITTED -/

/- curry_uncurry -/
theorem curry_uncurry {α β γ : Type} (f : α × β → γ) (p : α × β) :
    prodUncurry (prodCurry f) p = f p := by
  /- ADMITTED -/
  rfl
/- /ADMITTED -/
/- GRADE_THEOREM 1: Exercises.uncurry_curry
   GRADE_THEOREM 1: Exercises.curry_uncurry
   [] -/

/- SOONER: This isn't quite the definition given above. (And the one
   above is VASTLY easier to work with for the proof!)  We should
   really fix this! -/

/- EX2AM? (nth_error_informal)
   Recall the definition of the `nthError` function:
[[
       def nthError (l : List α) (n : Nat) : Option α :=
         match l with
         | [] => none
         | a :: l' => match n with
           | 0 => some a
           | n' + 1 => nthError l' n'
]]
   Write a careful informal proof of the following theorem:
[[
       ∀ (l : List α) (n : Nat), l.length = n → nthError l n = none
]]
   Make sure to state the induction hypothesis _explicitly_. -/

/- SOLUTION
   Theorem: For all types `α`, lists `l`, and natural numbers `n`,
   if `l.length = n` then `nthError l n = none`.

   Proof: By induction on `l`. There are two cases to consider:

   - If `l = []`, we must show `nthError [] n = none`. This follows
     immediately from the definition of `nthError`.

   - Otherwise, `l = x :: l'` for some `x` and `l'`, and the
     induction hypothesis tells us that
     `l'.length = n' → nthError l' n' = none`, for any `n'`.

     Let `n` be the length of `l`. We must show that
     `nthError (x :: l') n = none`.

     But we know that `n = l.length = (x :: l').length = l'.length + 1`.
     So it's enough to show `nthError l' l'.length = none`, which
     follows directly from the induction hypothesis, picking `l'.length`
     for `n'`.
   /SOLUTION -/

/- GRADE_MANUAL 2: informal_proof
   [] -/

/- ## Church Numerals (Advanced) -/

/- The following exercises explore an alternative way of defining
   natural numbers using the _Church numerals_, which are named after
   their inventor, the mathematician Alonzo Church. We can represent
   a natural number `n` as a function that takes a function `f` as a
   parameter and returns `f` iterated `n` times. -/

namespace Church

def CNat := (α : Type) → (α → α) → α → α

/- Let's see how to write some numbers with this notation. Iterating
   a function once should be the same as just applying it. Thus: -/

def one : CNat :=
  fun (X : Type) (f : X → X) (x : X) => f x

/- Similarly, `two` should apply `f` twice to its argument: -/

def two : CNat :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)

/- Defining `zero` is somewhat trickier: how can we "apply a function
   zero times"?  The answer is actually simple: just return the
   argument untouched. -/

def zero : CNat :=
  fun (X : Type) (_ : X → X) (x : X) => x

/- More generally, a number `n` can be written as
   `fun X f x => f (f ... (f x) ...)`, with `n` occurrences of `f`.
   Let's informally notate that as `fun X f x => f^n x`, with the
   convention that `f^0 x` is just `x`. Note how the `doit3times`
   function we've defined previously is actually just the Church
   representation of 3. -/

def three : CNat := @doit3times

/- So `n X f x` represents "do it `n` times", where `n` is a Church
   numeral and "it" means applying `f` starting with `x`.

   Another way to think about the Church representation is that
   function `f` represents the successor operation on `α`, and value
   `x` represents the zero element of `α`. We could even rewrite
   with those names to make it clearer: -/

def zero' : CNat :=
  fun (X : Type) (_ : X → X) (zero : X) => zero
def one' : CNat :=
  fun (X : Type) (succ : X → X) (zero : X) => succ zero
def two' : CNat :=
  fun (X : Type) (succ : X → X) (zero : X) => succ (succ zero)

/- If we passed in `Nat.succ` as `succ` and `0` as `zero`, we'd
   even get the Peano naturals as a result: -/

/- zero_church_peano -/
example : zero Nat Nat.succ 0 = 0 := by rfl
/- one_church_peano -/
example : one Nat Nat.succ 0 = 1 := by rfl
/- two_church_peano -/
example : two Nat Nat.succ 0 = 2 := by rfl

/- One very interesting implication of the Church numerals is that we
   don't strictly need the natural numbers to be built-in to a
   functional programming language, or even to be definable with an
   inductive data type. It's possible to represent them purely (if
   not efficiently) with functions.

   Of course, it's not enough just to "represent" numerals; we need
   to be able to do arithmetic with the representation. Show that we
   can by completing the definitions of the following functions. Make
   sure that the corresponding unit tests pass by proving them with
   `rfl`. -/

/- EX2A (church_scc) -/

/- Define a function that computes the successor of a Church numeral.
   Given a Church numeral `n`, its successor `scc n` should iterate
   its function argument once more than `n`. That is, given
   `fun X f x => f^n x` as input, `scc` should produce
   `fun X f x => f^(n+1) x` as output.
   In other words, do it `n` times, then do it once more. -/

def scc (n : CNat) : CNat :=
  /- ADMITDEF -/
  fun (X : Type) (f : X → X) (x : X) => f (n X f x)
  /- /ADMITDEF -/

/- scc_1 -/
example : scc zero = one := by rfl  /- ADMITTED -/
/- scc_2 -/
example : scc one = two := by rfl  /- ADMITTED -/
/- scc_3 -/
example : scc two = three := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 1: Exercises.Church.scc_2
   GRADE_THEOREM 1: Exercises.Church.scc_3
   [] -/

/- EX3A (church_plus) -/

/- Define a function that computes the addition of two Church
   numerals. Given `fun X f x => f^n x` and `fun X f x => f^m x`
   as input, `plus` should produce `fun X f x => f^(n + m) x` as
   output. In other words, do it `n` times, then do it `m` more times.

   Hint: the "zero" argument to a Church numeral need not be just `x`. -/

def plus (n m : CNat) : CNat :=
  /- ADMITDEF -/
  fun (X : Type) (f : X → X) (x : X) => n X f (m X f x)
  /- /ADMITDEF -/

/- plus_1 -/
example : plus zero one = one := by rfl  /- ADMITTED -/
/- plus_2 -/
example : plus two three = plus three two := by rfl  /- ADMITTED -/
/- plus_3 -/
example : plus (plus two two) three = plus one (plus three three) := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 1: Exercises.Church.plus_1
   GRADE_THEOREM 1: Exercises.Church.plus_2
   GRADE_THEOREM 1: Exercises.Church.plus_3
   [] -/

/- EX3A (church_mult) -/

/- Define a function that computes the multiplication of two Church
   numerals.

   Hint: the "successor" argument to a Church numeral need not be
   just `f`.

   Warning: Lean will not let you pass `CNat` itself as the type `X`
    argument to a Church numeral; you will get a "sort mismatch"
    error between `Type 1` and `Type 2`. Don't worry too much
    about what this means right now, but know that
    this is Lean's way of preventing a paradox in
    which a type contains itself. So leave the type argument
    unchanged. -/

def mult (n m : CNat) : CNat :=
  /- ADMITDEF -/
  fun (X : Type) (f : X → X) (x : X) => n X (m X f) x
  /- /ADMITDEF -/

/- mult_1 -/
example : mult one one = one := by rfl  /- ADMITTED -/
/- mult_2 -/
example : mult zero (plus three three) = zero := by rfl  /- ADMITTED -/
/- mult_3 -/
example : mult two three = plus three three := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 1: Exercises.Church.mult_1
   GRADE_THEOREM 1: Exercises.Church.mult_2
   GRADE_THEOREM 1: Exercises.Church.mult_3
   [] -/

/- EX3A (church_exp) -/

/- Exponentiation: -/

/- Define a function that computes the exponentiation of two Church
   numerals.

   Hint: the type argument to a Church numeral need not just be `α`.
   Finding the right type can be tricky. -/

def exp (n m : CNat) : CNat :=
  /- ADMITDEF -/
  fun (X : Type) (f : X → X) (x : X) => m (X → X) (n X) f x
  /- /ADMITDEF -/

/- exp_1 -/
example : exp two two = plus two two := by rfl  /- ADMITTED -/
/- exp_2 -/
example : exp three zero = one := by rfl  /- ADMITTED -/
/- exp_3 -/
example : exp three two = plus (mult two (mult two two)) one := by rfl  /- ADMITTED -/
/- GRADE_THEOREM 1: Exercises.Church.exp_1
   GRADE_THEOREM 1: Exercises.Church.exp_2
   GRADE_THEOREM 1: Exercises.Church.exp_3
   [] -/

end Church
end Exercises

/- /HIDEFROMADVANCED
   /FULL -/
