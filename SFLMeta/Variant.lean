import VersoManual

open Lean Elab

namespace SFLMeta

inductive Variant where
  | student
  | solutions
  | terse
  deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson, Quote

def Variant.toString : Variant → String
  | .student => "student"
  | .solutions => "solutions"
  | .terse => "terse"

instance : ToString Variant where
  toString := Variant.toString

namespace Variant

variable (v : Variant)

def fromString? : String → Option Variant
  | "student" => student
  | "solutions" => solutions
  | "terse" => terse
  | _ => none

def isStudent := v == .student

def isSolution := v == .solutions

def isTerse := v == .terse

end Variant

initialize currVariantRef : IO.Ref Variant ← IO.mkRef default

def setCurrVariant (v : Variant) : IO Unit := currVariantRef.set v

def getCurrVariant : IO Variant := currVariantRef.get

structure Variants (α : Type) where
  student : α
  solutions : α
  terse : α
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

instance [Quote α] : Quote (Variants α) where
  quote vs :=
    let student := quote vs.student
    let solutions := quote vs.solutions
    let terse := quote vs.terse
    Lean.Unhygienic.run `(Variants.mk $student $solutions $terse)

namespace Variants

variable {α β γ : Type}

def get (vs : Variants α) (v : Variant) : α :=
  match v with
  | .student => vs.student
  | .solutions => vs.solutions
  | .terse => vs.terse

def map {β : Type} (f : α → β) (vs : Variants α) : Variants β := {
  student := f vs.student
  solutions := f vs.solutions
  terse := f vs.terse
}

instance : GetElem (Variants α) Variant α (fun _ _ => True) where
  getElem vs v _ := vs.get v

instance [HAppend α β γ] : HAppend (Variants α) (Variants β) (Variants γ) where
  hAppend vs1 vs2 := {
    student := vs1.student ++ vs2.student
    solutions := vs1.solutions ++ vs2.solutions
    terse := vs1.terse ++ vs2.terse
  }

end Variants

end SFLMeta
