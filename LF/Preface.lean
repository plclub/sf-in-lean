import SFLMeta
open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Preface" =>
%%%
tag := "Preface"
htmlSplit := .never
file := some "Preface"
%%%

# Welcome

This is the entry point to a series of electronic textbooks on various
aspects of _Software Foundations_, the mathematical underpinnings of
reliable software.  Topics in the series include basic concepts of
logic, functional programming, computer-assisted theorem proving,
operational semantics, logics and techniques for reasoning about
programs, static type systems, property-based random testing, and
verification of practical C code.  The exposition is intended for a
broad range of readers, from advanced undergraduates to PhD students
and researchers.  No specific background in logic or programming
languages is assumed, though a degree of mathematical maturity will be
helpful.

The principal novelty of the series is that it is one hundred percent
formalized and machine-checked: each text is literally a script for
Lean.  The books are intended to be read alongside (or inside) an
interactive session with Lean.  All the details in the text are fully
formalized in Lean, and almost all of the exercises are designed to be
worked using Lean.

This book, _Logical Foundations in Lean_, lays groundwork for the
others, introducing the reader to the basic ideas of functional
programming, formal logic, and Lean itself.

# Overview

Building reliable software is hard -- really hard.  The scale and
complexity of modern systems, the number of people involved, and
the range of demands placed on them make it challenging to build
software that is even more-or-less correct, much less 100%
correct.  At the same time, the increasing degree to which
information processing is woven into every aspect of society
greatly amplifies the cost of bugs and insecurities.

Computer scientists and software engineers have responded to these
challenges with a host of techniques for improving software
reliability, ranging from recommendations about managing software
projects teams (e.g., extreme programming) to design philosophies for
libraries (e.g., model-view-controller, publish-subscribe, etc.) and
whole programming languages (e.g., object-oriented programming,
functional programming, ...) to mathematical techniques for specifying
and reasoning about properties of software and tools for helping
validate these properties.  The _Software Foundations_ books are focused
on this last set of tools.

The present volume weaves together three conceptual threads:

  - basic tools from _logic_ for making and justifying precise
    claims about programs;

  - the use of _provers_ (or _proof assistants_) to construct
    rigorous logical arguments;

  - _functional programming_, both as a programming method that
    simplifies reasoning about programs and as a bridge between
    programming and logic.

## Logic

Logic is the field of study whose subject matter is _proofs_ --
unassailable arguments for the truth of particular propositions.
Volumes have been written about the central role of logic in
computer science.  Manna and Waldinger called it "the calculus of
computer science,"{citet Bib.manna1971}[] while Halpern et al.'s paper _On the Unusual
Effectiveness of Logic in Computer Science_{citet Bib.halpern2001}[] catalogs scores of
ways in which logic offers critical tools and insights.  Indeed,
they observe that, "As a matter of fact, logic has turned out to
be significantly more effective in computer science than it has
been in mathematics. This is quite remarkable, especially since
much of the impetus for the development of logic during the past
one hundred years came from mathematics."

In particular, the fundamental tools of _inductive proof_ are
ubiquitous across computer science.  You have surely seen them before,
perhaps in a course on discrete math or analysis of algorithms, but in
this book we will examine them more deeply than you have probably done
so far.

## Proof Assistants

The flow of ideas between logic and computer science over the years
has run in both directions, with CS also making contributions to
logic. One of these has been the development of software tools for
helping construct and validate proofs of logical statements.  These
tools fall into two broad categories:

   - _Automated theorem provers_ provide "push-button" operation: you
     give them a proposition and they return either _true_ or _false_
     (or, sometimes, _don't know: ran out of time_). Although their
     reasoning capabilities are limited, they have matured
     tremendously in recent decades and are used now in a multitude of
     settings.  Examples of such tools include SAT solvers, SMT
     solvers, and model checkers.

   - _Proof assistants_ — or just _provers_ — are hybrid tools that
     automate the more routine aspects of creating proofs while
     depending on human guidance for more difficult aspects.  Widely
     used proof assistants include Isabelle, Agda, Twelf, ACL2, PVS,
     F\*, HOL4, Rocq, and Lean, among many others.

This course is based around Lean, a proof assistant that has been
under development since 2013 and has attracted a large and active
community of users in both research and at companies like DeepMind,
OpenAI, Anthropic, MSR, and AWS.

Lean provides a rich environment for interactive development of
machine-checked formal reasoning. The kernel of the Lean system is a
simple proof-checker, which guarantees that only correct deduction
steps are ever performed. On top of this kernel, the Lean environment
provides high-level facilities for proof development, including a
large library of common definitions and lemmas, powerful tactics for
constructing complex proofs semi-automatically, and a highly
extensible system for defining new proof-automation tactics and
notations for specific situations.

Lean and its relatives have become critical enablers for a [huge
variety of work](https://leanprover-community.github.io/papers.html) across computer science and mathematics:
- Formalizing the proof of [Fermat's Last Theorem](https://github.com/ImperialCollegeLondon/FLT)
- Formalizing the [Sphere Packing Problem](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
- DeepMind's AI model for IMO problems: [AlphaProof](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
- Formal specification for the [Cedar polucy language](https://github.com/cedar-policy/cedar-spec)

:::dev "Benjamin Pierce (bcpierce00)"
The individual references above should be merged into the categories below...
:::


- As a _platform for modeling programming languages_, proof assistants have
  become standard tools for researchers who need to describe and
  reason about complex language definitions. They have been used,
  for example, to check the security of the JavaCard platform,
  obtaining the highest level of common criteria certification,
  and for formal specifications of the x86 and LLVM instruction
  sets and programming languages such as C.

- As _environments for developing formally certified software
  and hardware_, they have been used, for example, to build
  CompCert{citep Bib.leroy2016}[], a fully-verified optimizing compiler for C,
  Cedar{citep Bib.disselkoen2024}[] and
  CertiKOS{citep Bib.gu2016certikos}[], a fully verified hypervisor, for proving the
  correctness of subtle algorithms involving floating point
  numbers, and as the basis for CertiCrypt, FCF, and SSProve,
  which are frameworks for proving cryptographic algorithms secure.
  They are also being used to build verified implementations of the
  open-source RISC-V processor architecture.

- As _proof assistants for mathematics_, they have been used to
  validate and help develop a number of important results.  For
  example, the ability to include complex computations inside proofs
  made it possible to develop the first formally verified proof of the
  4-color theorem.  This proof had previously been controversial among
  mathematicians because it required checking a large number of
  configurations using a program. More recently, an even more massive
  effort led to a formalization of the Feit-Thompson Theorem, the
  first major step in the classification of finite simple groups.

## Functional Programming

_Functional programming_ refers both to a collection of idioms that
can be used in almost any programming language and to a family of
languages designed to foreground these idioms, including Haskell,
OCaml, Standard ML, F\#, Scala, Scheme, Racket, Common Lisp, Clojure,
Erlang, F\*, and Lean itself.

Functional programming has been developed over many decades — indeed,
its roots go back to Church's lambda-calculus from the 1930s, well
_before_ the first electronic computers! But since the early '90s it
has enjoyed a surge of interest among both software engineers and
language designers.

The most basic tenet of functional programming is that, whenever
possible, computation should be _pure_, in the sense that the only
effect of execution should be to produce a result: it should be
free from _side effects_ such as I/O, assignments to mutable
variables, redirecting pointers, etc.  For example, whereas an
_imperative_ sorting function might take a list of numbers and
rearrange its pointers to put the list in order, a pure sorting
function would take the original list and return a fresh list
containing the same numbers in sorted order.

A significant benefit of this style of programming is that it makes
programs easier to understand and reason about. If every operation on
a data structure yields a new data structure, leaving the old one
intact, then there is no need to worry about how that structure is
being shared and whether a change by one part of the program might
break an invariant relied on by another part of the program. These
considerations are particularly critical in concurrent systems, where
every piece of mutable state shared between threads is a potential
source of pernicious bugs.

Another reason for the popularity of functional programming is related
to the first: functional programs are often much easier to parallelize
and physically distribute than their imperative counterparts.  If
running a computation has no effect other than producing a result,
then it does not matter _where_ it is run. Similarly, if a data
structure is never modified destructively, it can be copied freely,
across cores or across the network. Indeed, the "Map-Reduce" idiom,
which lies at the heart of massively distributed query processors like
Hadoop and is used by Google to index the entire web, is a classic
example of functional programming.

For purposes of these books, functional programming has yet another
significant attraction: it serves as a bridge between logic and
computer science. Indeed, Lean itself can be viewed as a combination
of a small but extremely expressive functional programming language
and a set of tools for stating and proving logical assertions.
Moreover, when we come to look more closely, we find that these two
sides of Lean are actually aspects of the very same underlying
machinery -- i.e., _proofs are programs_.


## Further Reading

This text is intended to be self contained, but readers looking
for follow-on textbooks or deeper treatments of particular topics will find some
suggestions for further reading in the {ref "Postscript"}[Postscript] chapter.

# Practicalities

## System Requirements

Lean runs on Windows, Linux, and MacOS.  The files in this book
have been tested with Lean version {leanVersion}[].

## Installation

The Visual Studio Code IDE is the recommended platform for using Lean.

- Install VS Code if needed
- From the Extensions tab of VS Code, install the Lean 4 extension
- Clone the [SF-in-Lean](https://github.com/plclub/sf-in-lean) git repo and open
  it in VS Code
- The first time you open a Lean file, the extension will offer to install Lean
  itself; accept, and it will fetch the version this book needs
- Wait for Lean to build the project (it takes a few minutes)

:::dev "Claude (AI assistant)" BeforeNextRelease
These steps send the reader to the *sources* repo, but the files a reader is
meant to work in are the ones the build generates: `make lf-student` writes a
standalone Lake project (its own `lakefile.toml` and `lean-toolchain`) to
`_out/lf/student/lean`, and that is where the exercises with `sorry`s live.  The
`LF/*.lean` files in the repo are Verso documents — prose plus code blocks — and
building the repo builds Verso and all three volumes, which is a good deal more
than "a few minutes".

There is also a chicken-and-egg problem in the ordering: running `make` at all
needs `elan`/`lake` already installed, but the step above gets Lean via the VS
Code extension, which only offers it once a Lean project is open.

Both go away once there is a released archive of the student `.lean` files: the
steps become "download and unpack, open the folder in VS Code, accept the
install prompt".  Until that exists, this section should probably say plainly
that readers get the files from their instructor or by following
`ALPHATESTERS.md`.
:::

## Exercises

Each chapter includes numerous exercises.  Each is marked with a
"star rating," which can be interpreted as follows:

   - One star: easy exercises that underscore points in the text
     and that, for most readers, should take only a minute or two.
     Get in the habit of working these as you reach them.

   - Two stars: straightforward exercises (five or ten minutes).

   - Three stars: exercises requiring a bit of thought (ten
     minutes to half an hour).

   - Four and five stars: more difficult exercises (half an hour
     and up).

Those using SF in a classroom setting should note that the autograder
assigns extra points to harder exercises:

```
1 star  = 1 point
2 stars = 2 points
3 stars = 3 points
4 stars = 6 points
5 stars = 10 points
```

Some exercises are marked "advanced," and some are marked "optional."
Doing just the non-optional, non-advanced exercises should provide
good coverage of the core material.  Optional exercises provide a bit
of extra practice with key concepts and introduce secondary themes
that may be of interest to some readers.  Advanced exercises offer an
extra challenge and a deeper cut at the ideas.

## Citation Format

If you want to refer to this volume in your own writing, please
do so as follows:

:::citation
:::

# For Potential Contributors

If you find things you'd like to help add or improve, your
contributions are welcome!  To get started, clone the
[SF-in-Lean git repo](https://github.com/plclub/sf-in-lean) and
have a look at `ALPHATESTERS.md`.

# For Instructors

A large compendium of exams from many offerings of CIS5000 ("Software
Foundations") at the University of Pennsylvania can be found at
<https://www.seas.upenn.edu/~cis5000/current/exams/index.html>. Until
2026, the course was offered in Rocq, but the ideas behind the
problems are still relevant.

# Acknowledgements

See `ACKNOWLEDGEMENTS.md` in the [SF-in-Lean git repo](https://github.com/plclub/sf-in-lean).





:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement (year := 2025)
The SF course at Penn (CIS 5000) sometimes attracts
students who don't have enough math background and begin really
flailing around the middle of the semester. I wonder if we could
help these people weed themselves out by offering some kind of more
detailed self-assessment near the beginning, maybe in this
chapter.

Some concepts that I would hope people have seen before:
  - recursive, polymorphic functional programming over lists
  - abstract definitions involving relations (e.g., reflexive,
    symmetric, transitive closure of a relation)
:::
