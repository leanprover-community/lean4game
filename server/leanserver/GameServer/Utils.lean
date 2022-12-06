import Lean

open Lean

def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
{ msgs := log.msgs.filter (·.severity matches .error) }

/-- A version of `println!` that actually does its job by flushing stdout. -/
def output {α : Type} [ToString α] (s : α) : IO Unit := do
  println! s
  IO.FS.Stream.flush (← IO.getStdout)

def Lean.LocalDecl.toJson (decl : LocalDecl) : MetaM Json :=
  return Lean.ToJson.toJson [toString decl.userName, toString (← Meta.ppExpr decl.type)]
