import Lean

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
deriving FromJson, ToJson


def Lean.MVarId.toGameGoal (goal : MVarId) : MetaM GameGoal := do
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
    return {objects := objects, assumptions := assumptions, goal := toString (← Meta.ppExpr mvarDecl.type) }


namespace GameServer


/-- `Game.getGoals` client<-server reply. -/
structure PlainGoal where
  /-- The pretty-printed goals, empty if all accomplished. -/
  goals : Array GameGoal
  deriving FromJson, ToJson

def getGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option PlainGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- NOTE: use `>=` since the cursor can be *after* the input
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
          let goals := List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
          let goals ← ci.runMetaM {} $ goals.mapM fun goal => do
            return ← goal.toGameGoal
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
