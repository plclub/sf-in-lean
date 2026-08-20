-- Shared Verso infrastructure for all SF-in-Lean volumes.
import Bib
import SFLMeta.Bnf
import SFLMeta.Comment
import SFLMeta.Details
import SFLMeta.DisplayMath
import SFLMeta.Epigraph
import SFLMeta.Exercise
import SFLMeta.Grade
import SFLMeta.Hide
import SFLMeta.Ignore
import SFLMeta.Instructors
import SFLMeta.Quiz
import SFLMeta.Save
import SFLMeta.SlideBreak
import SFLMeta.Solution
import SFLMeta.Terse
import SFLMeta.Theme
import SFLMeta.Version
import SFLMeta.Volume

namespace SFLMeta

export Verso.Genre.Manual.InlineLean (name leanCommand leanTerm module leanSection leanOutput)

end SFLMeta
