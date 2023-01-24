import Lean
import GameServer.EnvExtensions

open Lean
open Server
open Widget
open RequestM
open Meta


/-! ## GameGoal -/

structure GameLocalDecl where
  userName : Name
  type : String
deriving FromJson, ToJson

structure GameMessage where
  message : String
  spoiler : Bool
deriving FromJson, ToJson

structure GameGoal where
  objects : List GameLocalDecl
  assumptions : List GameLocalDecl
  goal : String
  messages : Array GameMessage
deriving FromJson, ToJson


def Lean.MVarId.toGameGoal (goal : MVarId) (messages : Array GameMessage) : MetaM GameGoal := do
match (← getMCtx).findDecl? goal with
| none          => throwError "unknown goal"
| some mvarDecl => do
  -- toGameGoalAux below will sort local declarations from the context of goal into data and assumptions,
  -- discarding auxilliary declarations
  let rec toGameGoalAux : List (Option LocalDecl) → MetaM (List LocalDecl × List LocalDecl)
  | (some decl)::t => withLCtx mvarDecl.lctx mvarDecl.localInstances do
    let (o, a) ← toGameGoalAux t
    if decl.isAuxDecl then
      return (o, a)
    if (← inferType decl.type).isProp then
      return (o, decl::a)
    else
      return (decl::o, a)
  | none:: t => toGameGoalAux t
  | [] => return ([], [])
  withLCtx mvarDecl.lctx mvarDecl.localInstances do
    let (objects, assumptions) ← toGameGoalAux mvarDecl.lctx.decls.toList
    let objects ← objects.mapM fun decl => do
      return { userName := decl.userName, type := toString (← Meta.ppExpr decl.type) }
    let assumptions ← assumptions.mapM fun decl => do
      return { userName := decl.userName, type := toString (← Meta.ppExpr decl.type) }
    return {objects := objects, assumptions := assumptions, goal := toString (← Meta.ppExpr mvarDecl.type), messages }

namespace GameServer

/-- `Game.getGoals` client<-server reply. -/
structure PlainGoal where
  /-- The pretty-printed goals, empty if all accomplished. -/
  goals : Array GameGoal
  deriving FromJson, ToJson

-- TODO: Find a better way to pass on the file name?
def levelIdFromFileName [Monad m] [MonadError m] [MonadEnv m] (fileName : String) : m LevelId := do
  let fileParts := fileName.splitOn "/"
  if fileParts.length == 3 then
    if let some level := fileParts[2]!.toNat? then
      return {game := `TestGame, world := fileParts[1]!, level := level}
  throwError s!"Could not find level ID in file name: {fileName}"

def getLevelByFileName [Monad m] [MonadError m] [MonadEnv m] (fileName : String) : m GameLevel := do
  let levelId ← levelIdFromFileName fileName
  -- TODO: make world and game configurable
  let some level ← getLevel? levelId
    | throwError "Level not found"
  return level

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

open Meta in
/-- Find all messages whose trigger matches the current goal -/
def findMessages (goal : MVarId) (doc : FileWorker.EditableDocument) (hLog : IO.FS.Stream) : MetaM (Array GameMessage) := do
  goal.withContext do
    let level ← getLevelByFileName doc.meta.mkInputContext.fileName
    let messages ← level.messages.filterMapM fun message => do
      let (declMvars, binderInfo, messageGoal) ← forallMetaBoundedTelescope message.goal message.intros
      -- TODO: Protext mvars in the type of `goal` to be instantiated?
      if ← isDefEq messageGoal (← inferType $ mkMVar goal) -- TODO: also check assumptions
      then
        let lctx ← getLCtx -- Local context of the `goal`
        hLog.putStr s!"{← declMvars.mapM inferType} =?= {← lctx.getFVars.mapM inferType}"
        if ← matchDecls declMvars lctx.getFVars
        then
          return some { message := message.message, spoiler := message.spoiler }
        else return none
      else return none
    return messages

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- TODO: I couldn't find a good condition to find the correct snap. So we are looking
  -- for the first snap with goals here:
  withWaitFindSnap doc (fun s => ¬ (s.infoTree.goalsAt? doc.meta.text hoverPos).isEmpty)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals : List Widget.InteractiveGoals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ciAfter := { ci with mctx := ti.mctxAfter }
          let ci := if useAfter then ciAfter else { ci with mctx := ti.mctxBefore }
          -- compute the interactive goals
          let goals ← ci.runMetaM {} (do
            let goals := List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
            let goals ← goals.mapM Widget.goalToInteractive
            return {goals}
          )
          -- compute the goal diff
          let goals ← ciAfter.runMetaM {} (do
              try
                Widget.diffInteractiveGoals useAfter ti goals
              catch _ =>
                -- fail silently, since this is just a bonus feature
                return goals
          )
          -- TODO: add hints
          -- let goals ← ci.runMetaM {} $ goals.mapM fun goal => do
          --   let messages ← findMessages goal doc hLog
          --   return ← goal.toGameGoal messages
          return goals
        return some <| goals.foldl (· ++ ·) ∅
      else
        return none

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    getInteractiveGoals

structure Diagnostic where
  severity : Option Lean.Lsp.DiagnosticSeverity
  message : String
deriving FromJson, ToJson

open RequestM in
def getDiagnostics (params : GetInteractiveDiagnosticsParams) : RequestM (RequestTask (Array Diagnostic)) := do
  let doc ← readDoc
  let rangeEnd := params.lineRange?.map fun range =>
    doc.meta.text.lspPosToUtf8Pos ⟨range.«end», 0⟩
  let t := doc.cmdSnaps.waitAll fun snap => rangeEnd.all (snap.beginPos < ·)
  pure <| t.map fun (snaps, _) =>
    let diags? := snaps.getLast?.map fun snap =>
      snap.interactiveDiags.toArray.filterMap fun diag =>
        if params.lineRange?.all fun ⟨s, e⟩ =>
          -- does [s,e) intersect [diag.fullRange.start.line,diag.fullRange.end.line)?
          s ≤ diag.fullRange.start.line ∧ diag.fullRange.start.line < e ∨
          diag.fullRange.start.line ≤ s ∧ s < diag.fullRange.end.line
        then some {message := diag.message.stripTags, severity := diag.severity?}
        else none
    pure <| diags?.getD #[]

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getDiagnostics
    GetInteractiveDiagnosticsParams
    (Array Diagnostic)
    getDiagnostics

end GameServer
