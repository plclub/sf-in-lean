import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual

namespace SFLMeta

/-!
`{leanVersion}[]` expands to the version of the Lean toolchain that built the
book, so version numbers quoted in the prose can never drift out of date. Any
content given in the brackets is ignored. -/
@[role]
def leanVersion : RoleExpanderOf Unit
  | (), _ =>
    ``(Verso.Doc.Inline.code $(quote Lean.versionString))

end SFLMeta
