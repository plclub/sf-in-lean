import VersoManual

open Verso.Genre.Manual

namespace SFLMeta

/-!
Shared bibliography entries for all SF-in-Lean volumes, transcribed from the
original SF sources `old/orig-lf-files/Bib.v` and `old/orig-plf-files/Bib.v`.
-/

namespace Bib

def aydemir2008 : InProceedings where
  title   := inlines!"Engineering Formal Metatheory"
  authors := #[inlines!"Brian Aydemir", inlines!"Arthur Charguéraud",
               inlines!"Benjamin C. Pierce", inlines!"Randy Pollack",
               inlines!"Stephanie Weirich"]
  year    := 2008
  booktitle := inlines!"ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL)"
  url     := "https://www.cis.upenn.edu/~bcpierce/papers/binders.pdf"

def bertot2004 : Article where
  title   := inlines!"Interactive Theorem Proving and Program Development: Coq'Art: The Calculus of Inductive Constructions"
  authors := #[inlines!"Yves Bertot", inlines!"Pierre Castéran"]
  journal := inlines!"Springer-Verlag"
  year    := 2004
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://tinyurl.com/z3o7nqu"

def chlipala2013 : Article where
  title   := inlines!"Certified Programming with Dependent Types"
  authors := #[inlines!"Adam Chlipala"]
  journal := inlines!"MIT Press"
  year    := 2013
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://tinyurl.com/zqdnyg2"

def harper2016 : Article where
  title   := inlines!"Practical Foundations for Programming Languages (Second Edition)"
  authors := #[inlines!"Robert Harper"]
  journal := inlines!"Cambridge University Press"
  year    := 2016
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://tinyurl.com/z82xwta"

def lipovaca2011 : Article where
  title   := inlines!"Learn You a Haskell for Great Good! A Beginner's Guide"
  authors := #[inlines!"Miran Lipovača"]
  journal := inlines!"No Starch Press"
  year    := 2011
  month   := some inlines!"April"
  volume  := inlines!""
  number  := inlines!""
  url     := "http://learnyouahaskell.com"

def mitchell1996 : Article where
  title   := inlines!"Foundations for Programming Languages"
  authors := #[inlines!"John C. Mitchell"]
  journal := inlines!"MIT Press"
  year    := 1996
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://tinyurl.com/zkosavw"

def nipkow2014 : Article where
  title   := inlines!"Concrete Semantics with Isabelle/HOL"
  authors := #[inlines!"Tobias Nipkow", inlines!"Gerwin Klein"]
  journal := inlines!"Springer"
  year    := 2014
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "http://www.concrete-semantics.org"

def osullivan2008 : Article where
  title   := inlines!"Real World Haskell: Code You Can Believe In"
  authors := #[inlines!"Bryan O'Sullivan", inlines!"John Goerzen",
               inlines!"Don Stewart"]
  journal := inlines!"O'Reilly"
  year    := 2008
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "http://book.realworldhaskell.org"

def pierce2002 : Article where
  title   := inlines!"Types and Programming Languages"
  authors := #[inlines!"Benjamin C. Pierce"]
  journal := inlines!"MIT Press"
  year    := 2002
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://tinyurl.com/gtnudmu"

def pugh1991 : InProceedings where
  title   := inlines!"The Omega test: a fast and practical integer programming algorithm for dependence analysis"
  authors := #[inlines!"William Pugh"]
  year    := 1991
  booktitle := inlines!"Proceedings of the 1991 ACM/IEEE Conference on Supercomputing"
  url     := "https://dl.acm.org/citation.cfm?id=125848"

def wadler2015 : Article where
  title   := inlines!"Propositions as Types"
  authors := #[inlines!"Philip Wadler"]
  journal := inlines!"Communications of the ACM"
  year    := 2015
  month   := none
  volume  := inlines!"58"
  number  := inlines!"12"
  pages   := (75, 84)
  url     := "https://dl.acm.org/citation.cfm?id=2699407"

def winskel1993 : Article where
  title   := inlines!"The Formal Semantics of Programming Languages: An Introduction"
  authors := #[inlines!"Glynn Winskel"]
  journal := inlines!"MIT Press"
  year    := 1993
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := "https://tinyurl.com/j2k6ev7"

end Bib

end SFLMeta
