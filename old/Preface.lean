prelude
import VersoManual
import VersoManual.InlineLean
import Illuminate
import SFLMeta.Bnf
import SFLMeta.Ignore
import SFLMeta.Save
import SFLMeta.Comment
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Instructors
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse

open Verso.Genre Manual
open SFLMeta

open InlineLean hiding lean

#doc (Manual) "Preface: Software Foundations in Lean" =>
%%%
htmlSplit := .never
file := "Preface"
%%%


Preface
:::dev
 SOONER: BCP 25: The SF course at Penn (CIS 5000) sometimes attracts
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

 ######################################################################
 Welcome

 This is the entry point to a series of electronic textbooks on
    various aspects of _Software Foundations_, the mathematical
    underpinnings of reliable software.  Topics in the series include
    basic concepts of logic, computer-assisted theorem proving, the
    Lean prover, functional programming, operational semantics, logics
    and techniques for reasoning about programs, static type systems,
    property-based random testing, and verification of practical C
    code.  The exposition is intended for a broad range of readers,
    from advanced undergraduates to PhD students and researchers.  No
    specific background in logic or programming languages is assumed,
    though a degree of mathematical maturity will be helpful.

    The principal novelty of the series is that it is one hundred
    percent formalized and machine-checked: each text is literally a
    script for Lean.  The books are intended to be read alongside (or
    inside) an interactive session with Lean.  All the details in the
    text are fully formalized in Lean, and most of the exercises are
    designed to be worked using Lean.

    The files in each book are organized into a sequence of core
    chapters, covering about one semester's worth of material and
    organized into a coherent linear narrative, plus a number of
    "offshoot" chapters covering additional topics.  All the core
    chapters are suitable for both upper-level undergraduate and
    graduate students.

    This book, _Logical Foundations_, lays groundwork for the others,
    introducing the reader to the basic ideas of functional
    programming, constructive logic, and the Lean prover.

 ######################################################################
 Overview

 Building reliable software is hard -- really hard.  The scale and
    complexity of modern systems, the number of people involved, and
    the range of demands placed on them make it challenging to build
    software that is even more-or-less correct, much less 100%%
    correct.  At the same time, the increasing degree to which
    information processing is woven into every aspect of society
    greatly amplifies the cost of bugs and insecurities.

    Computer scientists and software engineers have responded to these
    challenges by developing a host of techniques for improving
    software reliability, ranging from recommendations about managing
    software projects teams (e.g., extreme programming) to design
    philosophies for libraries (e.g., model-view-controller,
    publish-subscribe, etc.) and programming languages (e.g.,
    object-oriented programming, functional programming, ...)
    to mathematical techniques for
    specifying and reasoning about properties of software and tools
    for helping validate these properties.  The _Software Foundations_
    series is focused on this last set of tools.

    This volume weaves together three conceptual threads:

    (A) basic tools from _logic_ for making and justifying precise
        claims about programs;

    (B) the use of _proof assistants_ (or _provers_) to construct
        rigorous logical arguments;

    (C) _functional programming_, both as a method of programming that
        simplifies reasoning about programs and as a bridge between
        programming and logic.

 Logic

 Logic is the field of study whose subject matter is _proofs_ --
    unassailable arguments for the truth of particular propositions.
    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper _On the Unusual
    Effectiveness of Logic in Computer Science_ catalogs scores of
    ways in which logic offers critical tools and insights.  Indeed,
    they observe that, "As a matter of fact, logic has turned out to
    be significantly more effective in computer science than it has
    been in mathematics.  This is quite remarkable, especially since
    much of the impetus for the development of logic during the past
    one hundred years came from mathematics."

    In particular, the fundamental tools of _inductive proof_ are
    ubiquitous in all of computer science.  You have surely seen them
    before, perhaps in a course on discrete math or analysis of
    algorithms, but in this course we will examine them more deeply
    than you have probably done so far.
:::dev
 HIDE: That last claim is now only true if people read some
   optional chapters.  Oh well...
:::

 Proof Assistants

 The flow of ideas between logic and computer science has not been
    unidirectional: CS has also made important contributions to logic.
    One of these has been the development of software tools for
    helping construct proofs of logical propositions.  These tools
    fall into two broad categories:

       - _Automated theorem provers_ provide "push-button" operation:
         you give them a proposition and they return either _true_ or
         _false_ (or, sometimes, _don't know: ran out of time_).
         Although their reasoning capabilities are still limited,
         they have matured tremendously in recent decades and
         are used now in a multitude of settings.  Examples of such
         tools include SAT solvers, SMT solvers, and model checkers.

       - _Proof assistants_ are hybrid tools that automate the more
         routine aspects of building proofs while depending on human
         guidance for more difficult aspects.  Widely used proof
         assistants include Isabelle, Agda, Twelf, ACL2, PVS, F⋆,
         HOL4, Rocq, and Lean, among many others.

    This course is based around Lean, a proof assistant that has been
    under development since 2013 and has attracted a large community
    of users in both research and industry. Lean provides a rich
    environment for interactive development of machine-checked formal
    reasoning.  The kernel of the Lean system is a simple
    proof-checker, which guarantees that only correct deduction steps
    are ever performed.  On top of this kernel, the Lean environment
    provides high-level facilities for proof development, including a
    large library of common definitions and lemmas, powerful tactics
    for constructing complex proofs semi-automatically, and a
    special-purpose programming language for defining new
    proof-automation tactics for specific situations.

    Lean has been a critical enabler for a huge variety of work across
    computer science and mathematics:

-- TODO REWRITE
    - As a _platform for modeling programming languages_, it has
      become a standard tool for researchers who need to describe and
      reason about complex language definitions.  It has been used,
      for example, to check the security of the JavaCard platform,
      obtaining the highest level of common criteria certification,
      and for formal specifications of the x86 and LLVM instruction
      sets and programming languages such as C.

    - As an _environment for developing formally certified software
      and hardware_, Lean has been used, for example, to build TODO


    - As a _realistic environment for functional programming with
      dependent types_, it has inspired numerous innovations. For
      example, TODO

    - As a _proof assistant for higher-order logic_, it has been used
      to validate a number of important results in mathematics.  For
      example, TODO
:::dev
change this to lean and mention recent lean successes
:::
-- END TODO

 The term _functional programming_ refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a family of programming languages designed to
    emphasize these idioms, including Haskell, OCaml, Standard ML,
    F##, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, F⋆,
    and Lean.

    Functional programming has been developed over many decades --
    indeed, its roots go back to Church's lambda-calculus, which was
    invented in the 1930s, well _before_ the first electronic
    computers!  But since the early '90s it has enjoyed a surge of
    interest among industrial engineers and language designers,
    playing a key role in high-value systems at companies like Jane
    Street Capital, Microsoft, Facebook, Twitter, and Ericsson.
:::dev
companies should be updated!
:::
    The most basic tenet of functional programming is that, as much as
    possible, computation should be _pure_, in the sense that the only
    effect of execution should be to produce a result: it should be
    free from _side effects_ such as I/O, assignments to mutable
    variables, redirecting pointers, etc.  For example, whereas an
    _imperative_ sorting function might take a list of numbers and
    rearrange its pointers to put the list in order, a pure sorting
    function would take the original list and return a _new_ list
    containing the same numbers in sorted order.

    A significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant relied on by another part of the
    program.  These considerations are particularly critical in
    concurrent systems, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simpler behavior in the
    presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize and physically distribute than their
    imperative counterparts.  If running a computation has no effect
    other than producing a result, then it does not matter _where_ it
    is run.  Similarly, if a data structure is never modified
    destructively, then it can be copied freely, across cores or
    across the network.  Indeed, the "Map-Reduce" idiom, which lies at
    the heart of massively distributed query processors like Hadoop
    and is used by Google to index the entire web is a classic example
    of functional programming.

    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Lean itself can be viewed as a
    combination an extremely expressive functional
    programming language plus a set of tools for stating and proving
    logical assertions.  Moreover, when we come to look more closely,
    we find that these two sides of Lean are actually aspects of the
    very same underlying machinery -- i.e., _proofs are programs_.

 ######################################################################
 Further Reading

 This text is intended to be self contained, but readers looking
    for a deeper treatment of particular topics will find some
    suggestions for further reading in the Postscript chapter.
    Bibliographic information for all cited works can be found in the
    file Bib.lean.

 ######################################################################
 Practicalities

 System Requirements

 Lean runs on Windows, Linux, and macOS.  The files in this book
    have been tested with Lean (TODO PUT VERSION)

 Recommended Installation Method: Web Version (TODO WRITE)

 The Visual Studio Code (VS Code) IDE can cooperate with the Docker
    virtualization platform to compile Lean scripts without the need
    for any separate Lean installation.  This method is recommended for
    most Software Foundations readers.

     KNOWN PROBLEMS

 Alternative Installation Methods

 If you prefer, there are several other ways to use Lean. You will need:

    - A current installation of Lean, available from the Lean home
      page (https://Lean-prover.org/install).  The "Lean Platform"
      offers the easiest installation experience for most people,
      especially on Windows.

    - An IDE for interacting with Lean.  There are several choices:

        - `Lean 4` is an extension for Visual Studio Code that offers a
          simple interface via a familiar IDE.  This option is the
          recommended default.

          `Lean 4` can be used as an ordinary IDE or it can be combined
          with Docker (see below) for a lightweight installation
          experience.

 Exercises

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

    Some exercises are marked "advanced," and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge and a deeper cut at the material.

   #<span class="loud"># _Please do not post solutions to the exercises in a public place_. #</span>#
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  We especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.

 Downloading the Lean Files

 A tar file containing the full sources for the "release version"
    of this book (as a collection of Lean scripts and HTML files) is
    available at https://softwarefoundations.cis.upenn.edu.

    If you are using the book as part of a class, your professor may
    give you access to a locally modified version of the files; you
    should use that one instead of the public release version, so that
    you get any local updates during the semester.

 Chapter Dependencies

 A diagram of the dependencies between chapters and some suggested
    paths through the material can be found in the file #<a href="deps.html"><span class="inlineref">#`deps.html`#</span></a>#.

 ######################################################################
 Recommended Citation Format

 If you want to refer to this volume in your own writing, please
    do so as follows:
```
    @book            {$FIRSTAUTHOR:SF$VOLUMENUMBER,
    author       =   {$AUTHORS},
    editor       =   {Benjamin C. Pierce},
    title        =   "$VOLUMENAME",
    series       =   "Software Foundations",
    volume       =   "$VOLUMENUMBER",
    year         =   "$VOLUMEYEAR",
    publisher    =   "Electronic textbook",
    note         =   {Version $VERSION, \URL{http://softwarefoundations.cis.upenn.edu}}
    }
```


  ######################################################################
 Resources

 Sample Exams
TODO Update with Lean -> Rocq

 A large compendium of exams from many offerings of
    CIS5000 ("Software Foundations") at the University of Pennsylvania
    can be found at
    https://www.seas.upenn.edu/~cis5000/current/exams/index.html.
    There has been some drift of notations over the years, but most of
    the problems are still relevant to the current text.

 Lecture Videos

 Lectures for two intensive summer courses based on _Logical
    Foundations_ (part of the DeepSpec summer school series) can be
    found at https://deepspec.org/event/dsss17 and
    https://deepspec.org/event/dsss18/.  The video quality in the
    2017 lectures is poor at the beginning but gets better in the
    later lectures.

-- TODO ASK BENJAMIN
 ######################################################################
 Note for Instructors and Contributors

 If you plan to use these materials in your own teaching, or if you
    are using software foundations for self study and are finding
    things you'd like to help add or improve, your contributions are
    welcome!  You are warmly invited to join the private SF git repo.

    In order to keep the legalities simple and to have a single point
    of responsibility in case the need should ever arise to adjust the
    license terms, sublicense, etc., we ask all contributors (i.e.,
    everyone with access to the developers' repository) to assign
    copyright in their contributions to the appropriate "author of
    record," as follows:

      - I hereby assign copyright in my past and future contributions
        to the Software Foundations project to the Author of Record of
        each volume or component, to be licensed under the same terms
        as the rest of Software Foundations.  I understand that, at
        present, the Authors of Record are as follows: For Volumes 1
        and 2, known until 2016 as "Software Foundations" and from
        2016 as (respectively) "Logical Foundations" and "Programming
        Foundations," and for Volume 4, "QuickChick: Property-Based
        Testing in Rocq," the Author of Record is Benjamin C. Pierce.
        For Volume 3, "Verified Functional Algorithms," and volume 5,
        "Verifiable C," the Author of Record is Andrew W. Appel. For
        Volume 6, "Separation Logic Foundations," the author of record
        is Arthur Chargueraud. For components outside of designated
        volumes (e.g., typesetting and grading tools and other
        software infrastructure), the Author of Record is Benjamin C.
        Pierce.

    To get started, please send an email to Benjamin Pierce,
    describing yourself and how you plan to use the materials and
    including (A) the above copyright transfer text and (B) your
    github username.

    We'll set you up with access to the git repository and developers'
    mailing lists.  In the repository you'll find the files
    `INSTRUCTORS` and `CONTRIBUTING` with further instructions.

TODO NOTE ROCQ VERSION!

 ######################################################################
 Thanks

 Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    NSF Expeditions grant 1521523, _The Science of Deep
    Specification_.
