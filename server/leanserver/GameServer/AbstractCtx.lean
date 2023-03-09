import Lean

section AbstractCtx
open Lean
open Meta

structure AbstractCtxResult :=
  (abstractMVarsResult : AbstractMVarsResult)

/-- Abstract LCtx and MCtx to transport an expression into different contexts -/
def abstractCtx (goal : MVarId) : MetaM AbstractCtxResult := do
  let goalDecl ← goal.getDecl
  let fvars := goalDecl.lctx.decls.toArray.filterMap id |> Array.map (mkFVar ·.fvarId)
  let goal ← mkLambdaFVars (usedLetOnly := false) fvars goalDecl.type
  let goal ← abstractMVars goal
  return {
    abstractMVarsResult := goal
  }

def openAbstractCtxResult (res : AbstractCtxResult) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let (mvars, binderInfo, expr) ← openAbstractMVarsResult res.abstractMVarsResult
  lambdaLetTelescope (← instantiateMVars expr) k

end AbstractCtx
