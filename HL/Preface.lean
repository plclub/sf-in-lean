-- This file was largely proposed by Claude, drawing on the SFL LF Preface and
-- the Rocq PLF Preface.

import SFLMeta
import Credits

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Preface" =>
%%%
tag := "Preface"
htmlSplit := .never
file := "Preface"
%%%

# Welcome

This is {volumeName}[], volume {volumeNumber}[] of _Software Foundations in
Lean_.  It develops formal techniques for reasoning about what programs do.
For example, with the techniques we present, one can prove that an algorithm
sorts an array or that a compiler optimization does not incorrectly change
the behavior of the program it optimizes. This volume complements {volumeName "ts"}[],
which develops techniques for establishing properties of _all_ programs written
in a given language; the two volumes can be read in either order, and both build
on the material in {volumeName "lf"}[].

# Overview

To reason about a program, we first need a way of representing it as a
mathematical object, so that we can talk about it precisely, together with a
way of describing its behavior in terms of a mathematical function or
relation. Our main tool for this is _operational semantics_ in
"big step" style, which is a method of specifying the meaning of a programming
language by writing an abstract interpreter for it.

The programming language we consider throughout this volume is _Imp_, a
toy language capturing the core features of conventional imperative
programming: variables, assignment, conditionals, and loops. Imp's
arithmetic and boolean expressions are developed as their own simple sublangage,
called Slang.

We study two different ways of reasoning about the behavior of Imp programs.

First, we consider what it means to say that two Imp programs are
_equivalent_, in the sense that they produce the same behavior when started
in the same initial state. This notion of equivalence becomes a criterion for
judging the correctness of program transformations, such as those used in
compilers and optimizers. We build some simple optimizers for Imp and prove that
they preserve the behavior of the programs they transform.

Second, we develop a methodology for proving that a given Imp program
satisfies a formal specification of its behavior. We introduce _Hoare
triples_ — Imp programs annotated with pre- and post-conditions describing
what they expect to be true of their starting state and what they promise
to be true of their ending state, if they terminate — and the
reasoning principles of _Hoare Logic_, a domain-specific logic for
compositional reasoning about imperative programs. We then develop
_decorated programs_, a practical notation for writing out Hoare Logic
proofs alongside the code they verify.

The techniques this volume presents are relatively simple, but they
nevertheless underpin many of today's real-world software and hardware verification
efforts.

# Practicalities

This volume assumes you already have Lean and VS Code set up as described in
the {volumeName "lf"}[] Preface, and that you are comfortable with the basic
mechanics of working through an SFL chapter. The exercises here have the
same "advanced"/"optional" markings, and star ratings.

Briefly (see the {volumeName "lf"}[] Preface for detail), to get started:

If you are using this book as part of a class, your instructor will have
created a "student" release for you; download and unzip it, open the
resulting directory in VS Code, and open a `.lean` file (e.g., `HL/Slang.lean`)
to get started.

If you are reading on your own, clone the
[SF-in-Lean](https://github.com/plclub/sf-in-lean) repository and run `make
hl-student` from the root directory to build the student version of this
volume; it is written to `_out/hl/student/`, with an `html/` directory and a
`lean/` directory, exactly as described for {volumeName "lf"}[]. Run `make
student` instead if you want all three volumes built together.

## Building on Your Own Copy of Logical Foundations

This project includes a copy of the {volumeName "lf"}[] files that
chapters in this volme depends on, in their own `LF/` directory, so you do
not need a separate {volumeName "lf"}[] download to build or read this volume.
If you have already worked through {volumeName "lf"}[] and would rather this
volume build on your own work, copy the whole `LF/` directory from your
{volumeName "lf"}[] download over this project's `LF/` directory, then
rebuild.

Exercises in this volume use the same star ratings, and the same
"advanced"/"optional" markings, described in the {volumeName "lf"}[]
Preface.

## Citation Format

If you want to refer to this volume in your own writing, please
do so as follows:

:::citation
:::

# For Potential Contributors

If you find things you'd like to help add or improve, your
contributions are welcome!  To get started, clone the
[SF-in-Lean git repo](https://github.com/plclub/sf-in-lean) and
have a look at `ALPHA-TESTERS.md`.

{include 2 Credits}
