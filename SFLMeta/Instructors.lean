import VersoManual
import SFLMeta.Comment

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace SFLMeta

/-!
`Block.instructors` wraps notes addressed to instructors (originally
`-- INSTRUCTORS:` comments in the code-forward source).  Its Verso processing is
*identical* to `:::dev` / `:::hide`: the directive body is dropped at elaboration
(via the shared `noopDirectiveFor` expander), so it renders nothing and never
reaches the generated outputs, while the original text survives verbatim in the
generated `…Verso.lean` source.  The block is kept under its own name so a later
instructor-targeted build can treat it differently. -/
block_extension Block.instructors where
  data := Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def instructors : DirectiveExpanderOf Unit
  | args, contents => noopDirectiveFor ``Block.instructors args contents

/-- A ` ```instructors ` code block: the raw-body form of `:::instructors`.
Registered under the `instructors` name (shared with the directive, which lives
in a separate expander table) so the fence reads ` ```instructors `.  Like
` ```dev `, it takes its body as a raw string, so `to_verso` needn't wrap the
body in an inner code fence. -/
@[code_block instructors]
def instructorsBlock : CodeBlockExpanderOf Unit
  | args, str => noopCodeBlockFor ``Block.instructors args str

end SFLMeta
