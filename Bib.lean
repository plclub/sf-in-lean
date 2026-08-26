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
  url     := "https://doi.org/10.1145/1328438.1328443"

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
  url     := "https://doi.org/10.1145/2699407"

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
  url     := "https://mitpress.mit.edu/9780262731034/the-formal-semantics-of-programming-languages/"

def halpern2001: Article where
  title := inlines!"On the unusual effectiveness of logic in computer science"
  authors := #[inlines!"Joseph Y Halpern", inlines!"Robert Harper", inlines!"Neil Immerman",
                inlines!"Phokion G Kolaitis", inlines!"Moshe Y Vardi", inlines!"Victor Vianu"]
  journal := inlines!"Bulletin of Symbolic Logic"
  volume := inlines!"7"
  number := inlines!"2"
  year := 2001
  month   := none
  url := "https://doi.org/10.2307/2687775"

def manna1971: Article where
  title := inlines!"Toward automatic program synthesis"
  authors := #[inlines!"Zohar Manna", inlines!"Richard J Waldinger"]
  journal := inlines!"Communications of the ACM"
  volume := inlines!"14"
  number  := inlines!"3"
  year := 1971
  month := none
  url := "https://doi.org/10.1145/362566.362568"

def leroy2016 : InProceedings where
  title := inlines!"CompCert - A Formally Verified Optimizing Compiler"
  authors := #[inlines!"Xavier Leroy", inlines!"Sandrine Blazy", inlines!"Daniel Kästner", inlines!"Bernhard Schommer", inlines!"Markus Pister", inlines!"Christian Ferdinand"]
  booktitle := inlines!"ERTS 2016: Embedded Real Time Software and Systems, 8th European Congress"
  year := 2016
  url := "https://hal.science/hal-01238879"

def gu2016certikos: InProceedings where
  title := inlines!"CertiKOS: An extensible architecture for building certified concurrent OS kernels"
  authors :=#[inlines!"Ronghui Gu", inlines!"Zhong Shao", inlines!"Hao Chen",
      inlines!"Xiongnan Newman Wu" , inlines!"Jieung Kim", inlines!"Vilhelm Sjöberg", inlines!"David Costanzo"]
  booktitle := inlines!"12th USENIX Symposium on Operating Systems Design and Implementation (OSDI 16)"
  year := 2016
  url := "https://www.usenix.org/conference/osdi16/technical-sessions/presentation/gu"


def disselkoen2024: InProceedings where
  title := inlines!"How We Built Cedar: A Verification-Guided Approach"
  authors :=#[inlines!"Craig Disselkoen", inlines!"Aaron Eline", inlines!"Shaobo He",
      inlines!"Kyle Headley" , inlines!"Michael Hicks", inlines!"Kesha Hietala", inlines!"John Kaster",
      inlines!"Anwar Mamat",  inlines!"Matt McCutchen", inlines!"Neha Rungta", inlines!"others"]
  booktitle := inlines!"Companion Proceedings of the 32nd ACM International Conference on the Foundations of Software Engineering"
  year := 2024
  url := "https://doi.org/10.1145/3663529.3663854"

end Bib

end SFLMeta
