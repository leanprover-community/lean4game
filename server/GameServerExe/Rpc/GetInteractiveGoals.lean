import GameServerExe.Widget.InteractiveGoalWithHints
import GameServer.Tactic.Hint.Defs
import GameServerExe.Util.FVarBijection
import I18n

/-! ## GameGoal -/
namespace GameServer

open Widget

set_option autoImplicit false

open Lean
open Server
open Lean.Widget (InteractiveDiagnostic)
open GameServer.Widget
open RequestM
open Meta

open RequestM in

-- The editor apparently uses this
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option <| InteractiveGoals)) := do
  let doc ← readDoc
  -- let rc ← readThe RequestContext
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- TODO: I couldn't find a good condition to find the correct snap. So we are looking
  -- for the first snap with goals here:
  withWaitFindSnap doc (fun s => ¬ (s.infoTree.goalsAt? doc.meta.text hoverPos).isEmpty)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals : List <| Array InteractiveGoal ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
          let ciAfter := { ci with mctx := ti.mctxAfter }
          let ci := if useAfter then ciAfter else { ci with mctx := ti.mctxBefore }
          -- compute the interactive goals
          let goals ← ci.runMetaM {} do
            return List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
          let goals ← ci.runMetaM {} do
             goals.mapM fun goal => do
              -- let hints ← findHints goal doc.meta rc.initParams
              return ← goalToInteractive goal
          -- compute the goal diff
          -- let goals ← ciAfter.runMetaM {} (do
          --     try
          --       Widget.diffInteractiveGoals useAfter ti goals
          --     catch _ =>
          --       -- fail silently, since this is just a bonus feature
          --       return goals
          -- )
          return goals
        return some <| ⟨goals.foldl (· ++ ·) #[]⟩
      else
        return none
