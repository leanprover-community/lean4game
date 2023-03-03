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
        if ← isDefEq declMvar declFvar then
          usedFvars := usedFvars.set! (declFvars.size - j - 1) true
          found := true
          break
      else
        continue
    if ¬ found then return false
  return true

unsafe def evalHintMessageUnsafe : Expr → MetaM (Array Expr → MessageData) :=
  evalExpr (Array Expr → MessageData)
    (.forallE default (mkApp (mkConst ``Array [levelZero]) (mkConst ``Expr))
      (mkConst ``MessageData) .default)

@[implemented_by evalHintMessageUnsafe]
def evalHintMessage : Expr → MetaM (Array Expr → MessageData) := fun _ => pure (fun _ => "")

open Meta in
/-- Find all hints whose trigger matches the current goal -/
def findHints (goal : MVarId) (doc : FileWorker.EditableDocument) : MetaM (Array GameHint) := do
  goal.withContext do
    let some level ← getLevelByFileName? doc.meta.mkInputContext.fileName
      | throwError "Level not found: {doc.meta.mkInputContext.fileName}"
    let hints ← level.hints.filterMapM fun hint => do
      let (declMvars, binderInfo, hintGoal) ← forallMetaBoundedTelescope hint.goal hint.intros
      -- TODO: Protect mvars in the type of `goal` to be instantiated?
      if ← isDefEq hintGoal (← inferType $ mkMVar goal)
      then
        let lctx ← getLCtx -- Local context of the `goal`
        if ← matchDecls declMvars lctx.getFVars
        then
          let text := (← evalHintMessage hint.text) declMvars
          let ctx := {env := ← getEnv, mctx := ← getMCtx, lctx := ← getLCtx, opts := {}}
          let text ← (MessageData.withContext ctx text).toString
          return some { text := text, hidden := hint.hidden }
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
