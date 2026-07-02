module

public import Lean

public section

open Lean

/-- Add state tracking which names have been visited (and whether they are considered equal) to a monad -/
@[reducible, expose] def VisitedT (m : Type → Type) (α : Type) := StateT (Std.HashMap Name Bool) m α

namespace VisitedT

def size [Monad m] : VisitedT m Nat := do
  return (← get).size

def visited? [Monad m] (name : Name) : VisitedT m (Option Bool) := do
  let map ← get
  return map.get? name

def markTrue [Monad m] (name : Name) : VisitedT m Unit := do
  modify (·.insert name true)

def markFalse [Monad m] (name : Name) : VisitedT m Unit := do
  modify (·.insert name false)

def unmark [Monad m] (name : Name) : VisitedT m Unit := do
  modify (·.erase name)

end VisitedT


structure DebugConfig where
  silent : Bool
  depth : Nat

instance : Inhabited DebugConfig where
  default := { silent := true, depth := 0 }

/-- Provides utilities for debugging and tracing -/
@[reducible, expose] def DebugT (m : Type → Type) (α : Type) := StateT DebugConfig m α

namespace DebugT

def modifyDepth [Monad m] (f : Nat → Nat) : DebugT m Unit := do
  modify fun state => { state with depth := f state.depth }

def getDepth [Monad m] : DebugT m Nat := do
  return (← get).depth

def getSilent [Monad m] : DebugT m Bool := do
  return (← get).silent

def call [Monad m] (f : DebugT m β) : DebugT m β := do
  modifyDepth (· + 1)
  let res ← f
  modifyDepth (· - 1)
  return res

def dbg [Monad m] [MonadLiftT IO m] (msg : String) (level := "debug") : DebugT m Unit := do
  let silent ← getSilent
  if ! silent then
    let depth ← getDepth
    IO.println s!"[{level}:{depth}]: {msg}"

def runWithDebug [Monad m] (debug : Bool) (self : DebugT m α) := self.run { silent := ! debug, depth := 0 }

def toIO (self : DebugT (VisitedT CoreM) α) (ctx : Core.Context) (s : Core.State) : DebugT (VisitedT IO) α :=
  fun cfg vis => (self cfg vis).toIO' ctx s

end DebugT

/-- Defers calling `f` after `x`, i.e. calls `f` with the value of `x` and returns the value of `x` -/
def defer [Monad m] [Monad n] [MonadLiftT m n] (f : α → n Unit) (x : m α) : n α := do
  let res := (← x)
  f res
  return res
