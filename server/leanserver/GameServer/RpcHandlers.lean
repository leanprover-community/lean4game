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

structure GameGoal where
  objects : List GameLocalDecl
  assumptions : List GameLocalDecl
  goal : String
  messages : Array String
deriving FromJson, ToJson


def Lean.MVarId.toGameGoal (goal : MVarId) (messages : Array String) : MetaM GameGoal := do
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
def levelIdFromFileName [Monad m] [MonadError m] [MonadEnv m] (fileName : String) : m Nat := do
  if fileName.startsWith "/level" then
    if let some id := (fileName.drop "/level".length).toNat? then
      return id
  throwError s!"Could not find level ID in file name: {fileName}"
  return 1

def getLevelByFileName [Monad m] [MonadError m] [MonadEnv m] (fileName : String) : m GameLevel := do
  let levelId ← levelIdFromFileName fileName
  -- TODO: make world and game configurable
  let some level ← getLevel? {game := `TestGame, world := `TestWorld, level := levelId}
    | throwError "Level not found"
  return level

open Meta in
/-- Find all messages whose trigger matches the current goal -/
def findMessages (goal : MVarId) (doc : FileWorker.EditableDocument) : MetaM (Array String) := do
  let level ← getLevelByFileName doc.meta.mkInputContext.fileName
  let messages ← level.messages.filterMapM fun message => do
    let (declMvars, binderInfo, messageGoal) ← forallMetaBoundedTelescope message.goal message.intros
    if ← isDefEq messageGoal (← inferType $ mkMVar goal) -- TODO: also check assumptions
    then return some message.message
    else return none
  return messages

/-- Get goals and messages at a given position -/
def getGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option PlainGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- TODO: I couldn't find a good condition to find the correct snap. So we are looking
  -- for the first snap with goals here:
  withWaitFindSnap doc (fun s => ¬ (s.infoTree.goalsAt? doc.meta.text hoverPos).isEmpty)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
          let goals := List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
          let goals ← ci.runMetaM {} $ goals.mapM fun goal => do
            let messages ← findMessages goal doc
            return ← goal.toGameGoal messages
          return goals
        return some { goals := goals.foldl (· ++ ·) ∅ }
      else
        return none

builtin_initialize
  registerBuiltinRpcProcedure
    `Game.getGoals
    Lsp.PlainGoalParams
    (Option PlainGoal)
    getGoals

end GameServer
