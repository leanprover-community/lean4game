import Lean

open Lean

def Lean.Expr.getFVars (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds


/-- Returns the type of the goal after reverting all free variables in the order
where they appear in the goal type. -/
partial def normalizedRevertExpr (goal : MVarId) : MetaM Expr := do
  goal.withContext do
    let (_, new) ← goal.revert (← goal.getType).getFVars true
    let e ← new.getType
    if e.hasFVar then 
      return ← normalizedRevertExpr new
    else
      return (← new.getType)


def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
{ msgs := log.msgs.filter (·.severity matches .error) }

/-- A version of `println!` that actually does its job by flushing stdout. -/
def output {α : Type} [ToString α] (s : α) : IO Unit := do
  println! s
  IO.FS.Stream.flush (← IO.getStdout)  

def Lean.LocalDecl.toJson (decl : LocalDecl) : MetaM Json :=
  return Lean.ToJson.toJson [toString decl.userName, toString (← Meta.ppExpr decl.type)]
