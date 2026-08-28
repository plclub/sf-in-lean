import SFLMeta
import Credits

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Preface" =>
%%%
tag := "Preface"
htmlSplit := .never
file := some "Preface"
%%%

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

# Welcome

This is the starting point for a series of electronic textbooks on _Software Foundations_, the mathematical underpinnings of
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
formalized and machine-checked: each chapter of each book is literally a script for
the Lean prover, and the books are intended to be read alongside (or inside) an
interactive session with Lean.  All the details are fully
formalized, and almost all of the exercises are designed to be
worked using Lean.

This book, _Logical Foundations in Lean_, lays groundwork for the
others in the series, introducing the reader to the basic ideas of functional
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
computer science. {citet Bib.manna1971}[] called it "the calculus of
computer science," while {citet Bib.halpern2001}[]'s paper _On the Unusual
Effectiveness of Logic in Computer Science_ catalogs scores of
ways in which logic offers critical tools and insights. Indeed,
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
has run in both directions, with CS also making key contributions to
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

This course is based around Lean, a prover that has been
under development since 2013 and that has attracted a large and active
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

:::dev "Benjamin Pierce (bcpierce00)"
The individual references above should be merged into the categories below.
In particular, the first three should go in the bullet about math, and the last one should go in the bullet about
modeling programming languages.  (I see that that first bullet could also use
citations for some of the points it already makes, but we can leave that for later...)
:::


- As a _platform for modeling programming languages_, proof assistants have
  become standard tools for researchers who need to describe and
  reason about complex language definitions. They have been used,
  for example, to check the security of the JavaCard platform,
  obtaining the highest level of common criteria certification,
  and for formal specifications of the x86 and LLVM instruction
  sets and programming languages such as C.
:::dev "Benjamin Pierce (bcpierce00)" PotentialImprovement
Citations for these would be nice.
:::

- As _environments for developing formally certified software
  and hardware_, they have been used, for example, to build
  CompCert{citep Bib.leroy2016}[], a fully-verified optimizing compiler for C,
  [Cedar](https://github.com/cedar-policy/cedar-spec){citep Bib.disselkoen2024}[], a formally-specified policy language, and
  CertiKOS{citep Bib.gu2016certikos}[], a fully verified hypervisor,
  and for proving the
  correctness of subtle algorithms involving floating point
  numbers, and as the basis for CertiCrypt, FCF, and SSProve,
  which are frameworks for proving cryptographic algorithms secure.
  They are also being used to build verified implementations of the
  open-source RISC-V processor architecture.

- As _proof assistants for mathematics_, they have been used to
  validate and help develop a number of important results.  For
  example, the ability to include complex computations inside proofs
  made it possible to develop the first formally verified proof of the
  4-color theorem, which had previously been controversial among
  mathematicians because the argument required checking a large number of
  configurations using a program. More recently, an even more massive
  effort led to a formalization of the Feit-Thompson Theorem, the
  first major step in the classification of finite simple groups.

  Lean, in particular, is now at the core of various formalization efforts in
  mathematics, such as the proof of [Fermat's Last Theorem](https://github.com/ImperialCollegeLondon/FLT),
  the [Sphere Packing Problem](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean).
  and even DeepMind's AI model for International Math Olympiad
  problems, [AlphaProof](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/).

## Functional Programming

_Functional programming_ refers both to a collection of powerful coding idioms that
can be used in almost any programming language and to a family of
languages designed to foreground these idioms, including Haskell,
OCaml, Standard ML, F\#, Scala, Scheme, Racket, Common Lisp, Clojure,
Erlang, F\*, and Lean itself.

Functional programming has been developed over many decades — indeed,
its roots go back to Church's lambda-calculus from the 1930s, well
_before_ the first electronic computers! But since the early '90s it
has enjoyed a surge of interest among both software engineers and
language designers.

The basic tenet of functional programming is that, whenever
possible, computation should be _pure_, in the sense that the only
effect of execution should be to produce a result. That is, it should be
free from _side effects_ such as I/O, assignments to mutable
variables, redirecting pointers, etc.  For example, whereas an
_imperative_ sorting function might take a list of numbers and
rearrange its pointers to put the list in order, a pure sorting
function would take the original list and return a fresh list
containing the same numbers in sorted order.

A significant benefit of this style of programming is that it makes
programs easier to understand and reason about. If every operation on
a data structure yields a new data structure and leaves the old one
intact, then there is no need to worry about how that structure is
being shared and whether a change by one part of the program might
break an invariant relied on by another part of the program.
This is particularly important when reasoning about concurrent systems, where
every piece of mutable state shared between threads is a potential
source of pernicious bugs.

Another reason for the popularity of functional programming, related
to the first, is that functional programs are often much easier to parallelize
and physically distribute than their imperative counterparts.  If
running a computation has no effect other than producing a result,
then it does not matter _where_ it is run. Likewise, if a data
structure is never modified destructively, it can be copied freely,
across cores or across the network. Indeed, the "Map-Reduce" idiom,
which lies at the heart of massively distributed query processors like
Hadoop and is used by Google to index the entire web, is a classic
example of functional programming.

For these books, functional programming has yet another
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

Lean runs on Linux, MacOS, and Windows.  The files in this book
have been tested with Lean version {leanVersion}[].

## Installation

The Visual Studio Code IDE is the recommended platform for using Lean. To get set up,
follow these steps:

- Install VS Code if needed.
- From the Extensions tab of VS Code, install the Lean 4 extension.
- Separately: Download the book, build it (if necessary) — more below.
- Open the built book directory in a VS Code window.
- Open a Lean file; the extension will offer to install Lean; accept, and it will fetch
  the version this book needs.
- Wait for Lean to build the project (it takes a few minutes).

### Downloading and using the book for a class

If you are *using this book as part of a class*, your instructor will have created
a "student" release for you. Download the `.zip` file for that release, unzip it,
and then open the resulting directory in VS Code. Open any `.lean` file (e.g., `LF/Basics.lean`) to get started.

If you would like to read the HTML version of the book, it should be hosted on your
course website (you may be reading it now!).

Note that as the book is changing while you are taking your class, you should download
a fresh `.zip` for each homework you do, opening it in a fresh directory. This way
you will have access to prior solutions, and you will automatically get any Lean
updates. More on exercises below.

### Downloading and building the book from Git, for self study

If you are *going through Software Foundations on your own*, you can get the most
up-to-date version from the [SF-in-Lean](https://github.com/plclub/sf-in-lean) GitHub
repository. Clone that repository and then build it by typing `make` from the root
directory. This will construct various versions of the book.

Assuming you want to start from the beginning, we recommend typing `make lf-student`
instead. This builds the _Logical Foundations_ volume in its student form
(full prose, with solutions elided) and writes two things to `_out/lf/student/`:

- `html/`, an HTML-formatted version of the whole book; and
- `lean/`, a standalone Lean project holding the same chapters as `.lean` files, with solutions to exercises omitted.

Use `make student` instead if you also want _Type Systems_ (`ts`) and
_Hoare Logic_ (`hl`). The first build compiles the whole dependency tree and
takes a while; later builds are incremental.

Now you can open the generated Lean project as its own folder — not as a file
inside your clone:

  ```display
  code _out/lf/student/lean
  ```

  or

  ```display
  cd _out/lf/student/lean
  code .
  ```

You can also use File → Open Folder.

Treat this as a scratch copy: *every `make` regenerates it from the
Verso sources, overwriting whatever is there.*  Work on your proofs
here, but keep anything you want to survive somewhere else.

If you would like to read the book HTML, start a local HTTP server and point it
at the generated HTML files:

  ```display
  python3 -m http.server 8000 -d _out/lf/student/html
  ```

Then visit `http://localhost:8000` and start reading.

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
Optional exercises provide a bit
of extra practice with key concepts and introduce secondary themes
that may be of interest to some readers.  Advanced exercises offer an
extra challenge and a deeper cut at the ideas.
Doing just the non-optional, non-advanced exercises should provide
good coverage of the core material.

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

# For Instructors

A large compendium of exams from many offerings of CIS5000 ("Software
Foundations") at the University of Pennsylvania can be found at
[https://www.seas.upenn.edu/~cis5000/current/exams/index.html](https://www.seas.upenn.edu/~cis5000/current/exams/index.html). Until
2026, the course was offered in Rocq, but the ideas behind the
problems are still relevant.


{include 2 Credits}
