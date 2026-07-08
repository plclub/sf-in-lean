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

 Postscript
 SOONER: The FULL version could use some real text

 Congratulations: We've made it to the end of _Logical
    Foundations_!

 Looking Back

 We've covered quite a bit of ground so far.  Here's a quick review...

   \- _Functional programming_:
          \- "declarative" programming style (recursion over immutable
            data structures, rather than looping over mutable arrays
            or pointer structures)
          \- higher-order functions
          \- polymorphism

 TERSE:

     \- _Logic_, the mathematical basis for software engineering:
<<
               logic                        calculus
        --------------------   ~   ----------------------------
        software engineering       mechanical/civil engineering
>>

          \- inductively defined sets and relations
          \- inductive proofs
          \- proof objects

 TERSE:

     \- _Rocq_, an industrial-strength proof assistant
          \- functional core language
          \- core tactics
          \- automation


 ######################################################################
 Looking Forward

 If what you've seen so far has whetted your interest, you have
    several choices for further reading in later volumes of the
    _Software Foundations_ series.  Some of these are intended to be
    accessible to readers immediately after finishing _Logical
    Foundations_; others require a few chapters from Volume 2,
    _Programming Language Foundations_.  The Preface chapter in each
    volume gives details about prerequisites.

 SOONER: Might be worth explicitly advertising each volume, like
   this?  Some danger of redunancy tho...

           \- _Programming Language Foundations_ (volume 2, by a set of
             authors similar to this book's) covers material that
             might be found in a graduate course on the theory of
             programming languages, including Hoare logic, operational
             semantics, and type systems.

           \- _Verified Functional Algorithms_ (volume 3, by Andrew
             Appel) builds on the themes of functional programming and
             program verification in Rocq, addressing a range of topics
             that might be found in a standard data structures course,
             with an eye to formal verification.


 ######################################################################
 Resources

 Here are some other good places to learn more...


         This book includes some optional chapters covering topics
         that you may find useful.  Take a look at the (TODO LINK)
         table of contents and the (TODO LINK)chapter dependency diagram to find
         them.

       \- For questions about Lean, the Lean Zulip (TODO LINK)
         is an excellent community resource.

       \- Here are some great books on functional programming
            \- Learn You a Haskell for Great Good, by Miran Lipovaca
              \CITE Lipovaca 2011.
            \- Real World Haskell, by Bryan O'Sullivan, John Goerzen,
              and Don Stewart \CITE O'Sullivan 2008
            \- ...and many other excellent books on Haskell, OCaml,
              Scheme, Racket, Scala, F sharp, etc., etc.

       \- And some further resources for Rocq:
           \- Certified Programming with Dependent Types, by Adam
             Chlipala \CITE Chlipala 2013.
           \- Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran \CITE Bertot 2004.

       \- If you're interested in real-world applications of formal
         verification to critical software, see the Postscript chapter
         of _Programming Language Foundations_.

       \- For applications of Rocq in building verified systems, the
         lectures and course materials for the 2017 DeepSpec Summer
         School are a great resource.
         https://deepspec.org/event/dsss17/index.html
