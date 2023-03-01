import Lean
import GameServer.EnvExtensions
import GameServer.InteractiveGoal

open Lean
open Server
open Widget
open RequestM
open Meta


/-! ## GameGoal -/

namespace GameServer

def levelIdFromFileName? (fileName : String) : Option LevelId := Id.run do
  let fileParts := fileName.splitOn "/"
  if fileParts.length == 3 then
    if let some level := fileParts[2]!.toNat? then
      return some {game := `TestGame, world := fileParts[1]!, level := level}
  return none

def getLevelByFileName? [Monad m] [MonadEnv m] (fileName : String) : m (Option GameLevel) := do
  let some levelId := levelIdFromFileName? fileName
    | return none
  return ← getLevel? levelId

/-- Checks if `pattern` and `e` are equal up to mvars in `pattern` that may be assigned to fvars in `e`. -/
partial def matchExprAux (pattern : Expr) (e : Expr) : MetaM Bool := do
    match pattern, e with
    | .bvar i1, .bvar i2 => return i1 == i2
    | .fvar i1, .fvar i2 => return i1 == i2
    | .mvar _, .mvar _ => return true
    | .sort u1, .sort u2 => Meta.isLevelDefEq u1 u2
    | .const n1 ls1, .const n2 ls2 =>
      return n1 == n2 && (← (ls1.zip ls2).allM fun (l1, l2) => Meta.isLevelDefEq l1 l2)
    | .app f1 a1, .app f2 a2 =>
      return (← matchExprAux f1 f2) && (← matchExprAux a1 a2)
    | .lam _ t1 b1 _, .lam _ t2 b2 _ =>
      return (← matchExprAux t1 t2) && (← matchExprAux b1 b2)
    | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
      return (← matchExprAux t1 t2) && (← matchExprAux b1 b2)
    | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
      return (← matchExprAux t1 t2) && (← matchExprAux v1 v2)  && (← matchExprAux b1 b2)
    | .lit l1, .lit l2 =>
      return l1 == l2
    | .proj i1 n1 e1, .proj i2 n2 e2 =>
      return i1 == i2 && n1 == n2 && (← matchExprAux e1 e2)
    -- ignore mdata:
    | .mdata _ pattern', _ =>
      return ← matchExprAux pattern' e
    | _, .mdata _ e' =>
      return ← matchExprAux pattern e'
    -- assign fvars to mvars:
    | .mvar i1, .fvar _ =>
      match ← getExprMVarAssignment? i1 with
      | some pattern' => matchExprAux pattern' e
      | none =>
        i1.assign e
        return true
    | _, _ => return false

def matchExpr (pattern : Expr) (e : Expr) : MetaM Bool := do
  checkpointDefEq (mayPostpone := true) do
    matchExprAux pattern e

/-- Check if each meta variable in `declMvars` has a matching fvar in `declFvars` -/
def matchDecls (declMvars : Array Expr) (declFvars : Array Expr) : MetaM Bool := do
  -- We iterate through the array backwards hoping that this will find us faster results
  -- TODO: implement backtracking
  let mut usedFvars := (List.replicate declFvars.size false).toArray
  -- `usedFvars` keeps track of the fvars that were already used to match an mvar.
  for i in [:declMvars.size] do
    let declMvar := declMvars[declMvars.size - i - 1]!
    let mut found := false
    for j in [:declFvars.size] do
      let declFvar := declFvars[declFvars.size - j - 1]!
      let usedFvar := usedFvars[declFvars.size - j - 1]!
      if ¬ usedFvar then
        if ← matchExpr declMvar declFvar then
          usedFvars := usedFvars.set! (declFvars.size - j - 1) true
          found := true
          break
      else
        continue
    if ¬ found then return false
  return true

open Meta in
/-- Find all hints whose trigger matches the current goal -/
def findHints (goal : MVarId) (doc : FileWorker.EditableDocument) : MetaM (Array GameHint) := do
  goal.withContext do
    let some level ← getLevelByFileName? doc.meta.mkInputContext.fileName
      | throwError "Level not found: {doc.meta.mkInputContext.fileName}"
    let hints ← level.hints.filterMapM fun hint => do
      let (declMvars, binderInfo, hintGoal) ← forallMetaBoundedTelescope hint.goal hint.intros
      -- TODO: Protect mvars in the type of `goal` to be instantiated?
      if ← matchExpr hintGoal (← inferType $ mkMVar goal)
      then
        let lctx ← getLCtx -- Local context of the `goal`
        if ← matchDecls declMvars lctx.getFVars
        then
          return some { text := hint.text, hidden := hint.hidden }
        else return none
      else return none
    return hints

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- TODO: I couldn't find a good condition to find the correct snap. So we are looking
  -- for the first snap with goals here:
  withWaitFindSnap doc (fun s => ¬ (s.infoTree.goalsAt? doc.meta.text hoverPos).isEmpty)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals : List InteractiveGoals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ciAfter := { ci with mctx := ti.mctxAfter }
          let ci := if useAfter then ciAfter else { ci with mctx := ti.mctxBefore }
          -- compute the interactive goals
          let goals ← ci.runMetaM {} do
            return List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
          let goals ← ci.runMetaM {} do
             goals.mapM fun goal => do
              let hints ← findHints goal doc
              return ← goalToInteractive goal hints
          -- compute the goal diff
          -- let goals ← ciAfter.runMetaM {} (do
          --     try
          --       Widget.diffInteractiveGoals useAfter ti goals
          --     catch _ =>
          --       -- fail silently, since this is just a bonus feature
          --       return goals
          -- )
          return {goals}
        return some <| goals.foldl (· ++ ·) ⟨#[]⟩
      else
        return none

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    getInteractiveGoals

end GameServer
