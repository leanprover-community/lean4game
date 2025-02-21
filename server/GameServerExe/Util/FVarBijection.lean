import Lean

namespace GameServer

open Lean Meta

structure FVarBijection where
  forward : Std.HashMap FVarId FVarId
  backward : Std.HashMap FVarId FVarId

instance : EmptyCollection FVarBijection := ⟨∅, ∅⟩

def FVarBijection.insert (bij : FVarBijection) (a b : FVarId) : FVarBijection :=
  ⟨bij.forward.insert a b, bij.backward.insert b a⟩

def FVarBijection.insert? (bij : FVarBijection) (a b : FVarId) : Option FVarBijection :=
  let a' := bij.forward.get? a
  let b' := bij.forward.get? b
  if (a' == none || a' == some b) && (b' == none || b' == some a)
  then some $ bij.insert a b
  else none

/-- Checks if `pattern` and `e` are equal up to FVar identities. -/
partial def matchExpr (pattern : Expr) (e : Expr) (bij : FVarBijection := {}) : Option FVarBijection :=
  match pattern, e with
  | .bvar i1, .bvar i2 => if i1 == i2 then bij else none
  | .fvar i1, .fvar i2 => bij.insert? i1 i2
  | .mvar _, .mvar _ => bij
  | .sort _u1, .sort _u2 => bij -- TODO?
  | .const n1 _ls1, .const n2 _ls2 =>
    if n1 == n2 then bij else none -- && (← (ls1.zip ls2).allM fun (l1, l2) => Meta.isLevelDefEq l1 l2)
  | .app f1 a1, .app f2 a2 =>
    some bij
      |> (Option.bind · (fun bij => matchExpr f1 f2 bij))
      |> (Option.bind · (fun bij => matchExpr a1 a2 bij))
  | .lam _ t1 b1 _, .lam _ t2 b2 _ =>
    some bij
      |> (Option.bind · (fun bij => matchExpr t1 t2 bij))
      |> (Option.bind · (fun bij => matchExpr b1 b2 bij))
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
    some bij
      |> (Option.bind · (fun bij => matchExpr t1 t2 bij))
      |> (Option.bind · (fun bij => matchExpr b1 b2 bij))
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    some bij
      |> (Option.bind · (fun bij => matchExpr t1 t2 bij))
      |> (Option.bind · (fun bij => matchExpr v1 v2 bij))
      |> (Option.bind · (fun bij => matchExpr b1 b2 bij))
  | .lit l1, .lit l2 =>
    if l1 == l2 then bij else none
  | .proj i1 n1 e1, .proj i2 n2 e2 =>
    if i1 == i2 && n1 == n2 then matchExpr e1 e2 bij else none
  -- ignore mdata:
  | .mdata _ pattern', _ =>
    matchExpr pattern' e bij
  | _, .mdata _ e' =>
    matchExpr pattern e' bij
  | _, _ => none

/-- Check if each fvar in `patterns` has a matching fvar in `fvars` -/
def matchDecls (patterns : Array Expr) (fvars : Array Expr) (strict := true)
    (initBij : FVarBijection := {}) (defeq := false) : MetaM (Option FVarBijection) := do
  let reducer := if defeq then whnf else pure
  -- We iterate through the array backwards hoping that this will find us faster results
  -- TODO: implement backtracking
  let mut bij := initBij
  for i in [:patterns.size] do
    let pattern := patterns[patterns.size - i - 1]!
    if bij.forward.contains pattern.fvarId! then
      continue
    for j in [:fvars.size] do
      let fvar := fvars[fvars.size - j - 1]!
      if bij.backward.contains fvar.fvarId! then
        continue

      if let some bij' := matchExpr
          (← reducer <| ← instantiateMVars $ ← inferType pattern)
          (← reducer <| ← instantiateMVars $ ← inferType fvar) bij then
        -- usedFvars := usedFvars.set! (fvars.size - j - 1) true
        bij := bij'.insert pattern.fvarId! fvar.fvarId!
        break
    if ! bij.forward.contains pattern.fvarId! then return none

  if !strict || fvars.all (fun fvar => bij.backward.contains fvar.fvarId!)
  then return some bij
  else return none
