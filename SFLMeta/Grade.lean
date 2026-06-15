import VersoManual
import SFLMeta.Comment

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.grade` records a `-- GRADE_THEOREM <pts>: <name>` grading directive from
the code-forward source.  For now it is a pure noop — rendered empty, body
discarded at elaboration, exactly like `:::dev` (it shares `noopDirectiveFor`).
The grading spec survives verbatim in the generated `…Verso.lean` source, so the
grading infrastructure can later parse `:::grade` blocks (or this block can be
given real behaviour) to drive autograding scripts. -/
block_extension Block.grade where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def grade : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.grade args contents

end SFLMeta
