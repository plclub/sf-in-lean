import VersoManual

open Verso.Genre Manual

namespace SFLMeta

inductive Variant where
  | student
  | solution
  | terse
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Variant

variable (v : Variant)

def fromString? : String → Option Variant
  | "student" => student
  | "solution" => solution
  | "terse" => terse
  | _ => none

def isStudent := v == .student

def isSolution := v == .solution

def isTerse := v == .terse

end Variant

initialize currVariantRef : IO.Ref Variant ← IO.mkRef default

def setCurrVariant (v : Variant) : IO Unit := currVariantRef.set v

def getCurrVariant : IO Variant := currVariantRef.get

end SFLMeta
