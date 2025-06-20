import GameServerExe.Widget.InteractiveGoalWithHints
import GameServerExe.Widget.InteractiveDiagnostic
import GameServerExe.FindHints
import Lean

namespace GameServer

open GameServer.Widget

open Lean Server RequestM

open Lean.Widget (InteractiveDiagnostic)

-- NOTE: Changes here need to be reflected in  the corresponding `interface` in `rcp_api.ts`
-- on the client-side.
/-- Collected goals throughout the proof. Used for communication with the game client. -/
structure ProofState where
  /-- goals after each line. includes the hints. -/
  steps : Array <| InteractiveGoalsWithHints
  /-- diagnostics contains all errors and warnings.

  TODO: I think they contain information about which line they belong to. Verify this.
  -/
  diagnostics : Array InteractiveDiagnostic := default
  /-- Whether the level is considered solved. -/
  completed : Bool
  completedWithWarnings : Bool
  lastPos : Nat -- only for debugging
deriving RpcEncodable

/-- Request that returns the goals at the end of each line of the tactic proof
plus the diagnostics (i.e. warnings/errors) for the proof.
 -/
def getProofState (_ : Lsp.PlainGoalParams) : RequestM (RequestTask (Option ProofState)) := do
  let doc ← readDoc
  let rc ← readThe RequestContext
  let text := doc.meta.text

  withWaitFindSnap
    doc
    -- TODO (Alex): I couldn't find a good condition to find the correct snap. So we are looking
    -- for the first snap with goals here.
    -- NOTE (Jon): The entire proof is in one snap, so hoped that Position `0` is good enough.
    (fun snap => ¬ (snap.infoTree.goalsAt? doc.meta.text 0).isEmpty)
    (notFoundX := return none)
    fun snap => do
      -- `snap` is the one snapshot containing the entire proof.
      let mut steps : Array <| InteractiveGoalsWithHints := #[]

      -- Question: Is there a difference between the diags of this snap and the last snap?
      -- Should we get the diags from there?
      -- Answer: The last snap only copied the diags from the end of this snap
      let mut diag : Array InteractiveDiagnostic := #[] -- TODO: snap.interactiveDiags.toArray

      -- Level is completed if there are no errors or warnings
      let completedWithWarnings : Bool := ¬ diag.any (·.severity? == some .error)
      let completed : Bool := completedWithWarnings ∧ ¬ diag.any (·.severity? == some .warning)

      let mut intermediateGoalCount := 0

      -- only the positions that have non-whitespace characters since the last position
      -- should add a new proof step.
      let positionsWithSource : Array (String.Pos × String) :=
        text.positions.zipWithIndex.filterMap (
          fun (pos, i) => match i with
          | 0 => some (pos, "")
          | i' + 1 =>
            let source : String := Substring.toString ⟨text.source, text.positions.get! i', pos⟩
            if source.trim.length == 0 then
              none
            else
              some (pos, source))

      -- Drop the last position as we ensured that there is always a newline at the end
      for ((pos, source), i) in positionsWithSource.zipWithIndex do
        -- iterate over all steps in the proof and get the goals and hints at each position

        -- diags are labeled in Lsp-positions, which differ from the lean-internal
        -- positions by `1`.
        let lspPosAt := text.utf8PosToLspPos pos

        let mut diagsAtPos : Array InteractiveDiagnostic := filterUnsolvedGoal <|
          -- `+1` for getting the errors after the line.
          match i with
          | 0 =>
            -- `lspPosAt` is `(0, 0)`
            diag.filter (fun d => d.range.start == lspPosAt )
          | i' + 1 =>
            diag.filter (fun d =>
              ((text.utf8PosToLspPos <| (positionsWithSource.get! i').1) ≤ d.range.start) ∧
              d.range.start < lspPosAt )

        if let goalsAtResult@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text pos then
          let goalsAtPos' : List <| List InteractiveGoalWithHints ← goalsAtResult.mapM
            fun { ctxInfo := ci, tacticInfo := tacticInfo, useAfter := useAfter, .. } => do
              -- TODO: What does this function body do?
              -- let ciAfter := { ci with mctx := ti.mctxAfter }
              let ci := if useAfter then
                  { ci with mctx := tacticInfo.mctxAfter }
                else
                  { ci with mctx := tacticInfo.mctxBefore }
              -- compute the interactive goals
              let goalMvars : List MVarId ← ci.runMetaM {} do
                return if useAfter then tacticInfo.goalsAfter else tacticInfo.goalsBefore

              let interactiveGoals : List InteractiveGoalWithHints ← ci.runMetaM {} do
                goalMvars.mapM fun goal => do
                  let hints ← findHints goal doc.meta rc.initParams
                  let interactiveGoal ← goalToInteractive goal
                  return ⟨interactiveGoal, hints⟩
              -- TODO: This code is way old, can it be deleted?
              -- compute the goal diff
              -- let goals ← ciAfter.runMetaM {} (do
              --     try
              --       Widget.diffInteractiveGoals useAfter ti goals
              --     catch _ =>
              --       -- fail silently, since this is just a bonus feature
              --       return goals
              -- )
              return interactiveGoals
          let goalsAtPos : Array InteractiveGoalWithHints := ⟨goalsAtPos'.foldl (· ++ ·) []⟩

          diagsAtPos ← completionDiagnostics goalsAtPos.size intermediateGoalCount
            completed completedWithWarnings lspPosAt diagsAtPos

          intermediateGoalCount := goalsAtPos.size

          steps := steps.push ⟨goalsAtPos, source, diagsAtPos, lspPosAt.line, lspPosAt.character⟩
        else
          -- No goals present
          steps := steps.push ⟨#[], source, diagsAtPos, lspPosAt.line, none⟩

      -- Filter out the "unsolved goals" message
      diag := filterUnsolvedGoal diag

      let lastPos := text.utf8PosToLspPos positionsWithSource.back!.1
      let remainingDiags : Array InteractiveDiagnostic :=
        diag.filter (fun d => lastPos ≤ d.range.start)

      return some {
        steps := steps,
        diagnostics := remainingDiags,
        completed := completed,
        completedWithWarnings := completedWithWarnings,
        lastPos := lastPos.line
        }
