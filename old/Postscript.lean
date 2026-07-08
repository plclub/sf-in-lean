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

     \- _Lean_, an industrial-strength proof assistant
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
:::dev
 SOONER: Might be worth explicitly advertising each volume, like
   this?  Some danger of redunancy tho...
:::
           \- _Programming Language Foundations_ (volume 2, by a set of
             authors similar to this book's) covers material that
             might be found in a graduate course on the theory of
             programming languages, including Hoare logic, operational
             semantics, and type systems.

            TODO LEAN RESOURCES

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

       \- And some further resources for Lean:
           TODO LEAN RESOURCES

       \- If you're interested in real-world applications of formal
         verification to critical software, see the Postscript chapter
         of _Programming Language Foundations_.

       \- For applications of Lean in building verified systems,
       TODO LEAN MATERIALS
