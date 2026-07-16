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

#doc (Manual) "Postscript: Software Foundations in Lean" =>
%%%
htmlSplit := .never
file := "Postscript"
%%%

 Postscript
:::dev
 SOONER: The FULL version could use some real text
:::

 Congratulations: We've made it to the end of _Logical
    Foundations in Lean_!

 Looking Back

 We've covered quite a bit of ground so far.  Here's a quick review...

   \- _Functional programming_:
          \- "declarative" programming style (recursion over immutable
            data structures, rather than looping over mutable arrays
            or pointer structures)
          \- higher-order functions
          \- polymorphism


     \- _Logic_, the mathematical basis for software engineering:

               logic                        calculus
        --------------------   ~   ----------------------------
        software engineering       mechanical/civil engineering


          \- inductively defined sets and relations
          \- inductive proofs
          \- proof objects


     \- _Lean_, an industrial-strength proof assistant
          \- functional core language
          \- core tactics
          \- automation


 ######################################################################
 Looking Forward

 If what you've seen so far has whetted your interest, you have
    several choices for further reading in later volumes of the
    _Software Foundations_ series.

    As of August 2026, there are two more volumes written in Lean.

    _Hoare Logic_: This short volume describes one of the primary methods
    for reasoning about _imperative_ programs- programs with state and
    mutation, like C++, Java, C, and Assembly- in a pure logic
    like Lean's. This method, called _Hoare Logic_, is embeddable into
    Lean's type system and is a powerful tool for determining
    the correct behavior of imperative code. Since most of the code
    in the wild today is imperative, this technique is both well-established
    and popular among industry professionals who analyze and fortify the
    correctness of systems.

    _Type Systems_: Another tool for reasoning about the correctness of a program
    is a _type system_. You have interacted thoroughly with Lean's rich type system,
    which is one of the most complex in a modern programming language. Most
    languages have type systems that are far less complex, but which still provide
    incredibly useful guardrails against ill-behaved programs. In this volume you
    will explore how to read, analyze, and design type systems in a proof assistant.

    Combined, these form the aggregate volume
    _Programming Language Foundations in Lean_.

    You may notice the "in Lean" tag on this and the next volume.
    The original _Logical Foundations_, _Programming Language Foundations_,
    and continuation of the _Software Foundations_ series is written in
    in _Rocq_, another proof assistant. Switching from Lean to Rocq has a
    medium-sized learning curve, but it's one that you are now more
    than prepared to tackle if you wish to do so.
    Additionally, there are active efforts to translate the following
    volumes of _Software Foundations_ into Lean. If this interests you,
    please see `CONTRIBUTING.md` and write the `sf-dev` team a note!


 ######################################################################
 Resources

 Here are some other good places to learn more...


         This book includes some optional chapters covering topics
         that you may find useful.  Take a look at the (TODO LINK)
         table of contents and the (TODO LINK)chapter dependency diagram to find
         them.

       \- For questions about Lean, the Lean Zulip (TODO LINK)
         is an excellent community resource.

       \- Here are some great books on functional programming:
            \- Learn You a Haskell for Great Good, by Miran Lipovaca
              \CITE Lipovaca 2011.
            \- Real World Haskell, by Bryan O'Sullivan, John Goerzen,
              and Don Stewart \CITE O'Sullivan 2008
            \- ...and many other excellent books on Haskell, OCaml,
              Scheme, Racket, Scala, F sharp, etc., etc.

       \- And some further resources for Lean:
           TODO LEAN RESOURCES

       \- If you're interested in real-world applications of formal
         verification to critical software, see the Postscript chapter
         of _Programming Language Foundations_.

       \- For applications of Lean in building verified systems,
       TODO LEAN MATERIALS
