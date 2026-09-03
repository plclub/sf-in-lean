<!-- This file is AI-generated (Claude). -->

# Content questions — `LF/Lists.lean`

Raised during the round-1 proofreading pass over **`LF/Lists.lean`**
(2026-09-03, commit `2b085d6`). Deliberately kept out of the round: each
needs an authorial decision, not a comma.

---

## 1. Informal-proof list structure (highest priority — renders wrong)

In both the `append_assoc` informal proof and the
`length_append` / `length_reverse` pair, continuation lines are indented
inconsistently. Some sit inside the bullet:

```
  which follows directly from the definitions of `length`,
  `++`, and `+`.
```

and others sit at column 0, which drops them out of the list entirely:

```
We must show
```

```
By the definition of `append`, this follows from
```

The result is a broken bullet list in the rendered book. Fixing it means
settling on one indentation for every continuation paragraph and the
`display` blocks between them — a structural edit, so it was left alone.

## 2. `.succ l.length` in the compressed proof

[`LF/Lists.lean:1521`](Lists.lean#L1521) (as of `2b085d6`) states

> `(l ++ [n]).length = .succ l.length`

but the lemma actually proved, `append_length_succ`, states
`(l ++ [n]).length = l.length + 1`. The `.succ` spelling appears nowhere
else in the chapter. Probably should be `l.length + 1`.

## 3. Stale Rocq references in the `AndrewTolmach` dev note

The note on the `count_append` exercise says:

* "how hard it is to prove (in terms of **Rocq** mechanics)" — carried over
  from the Rocq source; the chapter is Lean.
* "the proof in the exercise above for **`count_removeOne`**" — there is no
  `count_removeOne` in this chapter. Presumably
  `remove_does_not_increase_count`.

## 4. The "And some examples:" block is inert

[`LF/Lists.lean:538`](Lists.lean#L538) is a plain ``` fence inside `:::full`:

```
example : head 0 [1, 2, 3] = 1 := by rw [head_cons]
example : head 0 [] = 0 := by rw [head_nil]
example : [1, 2, 3].tail = [2, 3] := by rw [tail_cons]
```

Because the fence carries no language tag, these three examples are never
elaborated, so they can drift out of date silently. Was a ` ```lean ` block
intended? (They do currently typecheck.)

## 5. `typeclass` vs `type class`

The "Type Classes and Overloading Notation" section mixes both spellings
within four lines — "instances of that **typeclass** inherit the notation"
against "**type class**" everywhere around it. There is already a
`:::dev "Benjamin Pierce (bcpierce00)"` note at the top of that section
asking "One word, or two?", so this is an open authorial question rather
than a slip; whichever is chosen should then be applied consistently.
