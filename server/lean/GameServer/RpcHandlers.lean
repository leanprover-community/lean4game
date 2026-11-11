import GameApi.EnvExtensions
import GameApi.Hints
import GameServer.CheckProof.FilterUnsolvedGoal
import GameServer.CheckProof.FindHints
import GameServer.Lean.InteractiveGoal
import I18n

open Lean
open Server
open Widget
open RequestM
open Meta
open Std

/-! ## GameGoal -/

namespace GameServer

-- TODO: no need to have `RequestM`, just anything where `mut` works
/-- Add custom diagnostics about whether the level is completed. -/
def completionDiagnostics (goalCount : Nat) (prevGoalCount : Nat) (completed : Bool)
    (completedWithWarnings : Bool) (pos : Lsp.Position)
    (startDiags : Array InteractiveDiagnostic := #[]) :
    RequestM <| Array InteractiveDiagnostic := do
  let mut out : Array InteractiveDiagnostic := startDiags
  if goalCount == 0 then
    if completed then
      out := out.push {
        -- TODO: marking these with `t!` has the implication that every game
        -- needs to translate these messages again,
        -- but cannot think of another option
        -- that would not involve manually adding them somewhere in the translation files.
        message := .text t!"level completed! 🎉"
        range := {
          start := pos
          «end» := pos
          }
        severity? := Lsp.DiagnosticSeverity.information }
    else if completedWithWarnings then
      out := out.push {
        message := .text t!"level completed with warnings… 🎭"
        range := {
          start := pos
          «end» := pos
          }
        severity? := Lsp.DiagnosticSeverity.information }
    else
      pure ()
  else if goalCount < prevGoalCount then
    -- If there is any errors, goals might vanish without being 'solved'
    -- so showing the message "intermediate goal solved" would be confusing.
    if (¬ (filterUnsolvedGoal startDiags).any (·.severity? == some .error)) then
      out := out.push {
        message := .text t!"intermediate goal solved! 🎉"
        range := {
          start := pos
          «end» := pos
          }
        severity? := Lsp.DiagnosticSeverity.information
      }

  return out

structure ProofStateParams extends Lsp.PlainGoalParams where
  worldId: String
  levelId: Nat
  deriving FromJson, ToJson

/-- Request that returns the goals at the end of each line of the tactic proof
plus the diagnostics (i.e. warnings/errors) for the proof.
 -/
def getProofState (p : ProofStateParams) : RequestM (RequestTask (Option ProofState)) := do
  let doc ← readDoc
  let rc ← readThe RequestContext
  let text := doc.meta.text

  bindTaskCostly doc.cmdSnaps.waitAll fun (snaps, _) => do
    mapTaskCostly doc.reporter fun () => do
      let mut steps : Array <| InteractiveGoalsWithHints := #[]

      let mut diag : Array InteractiveDiagnostic ← doc.diagnosticsMutex.atomically do
        let ds ← get
        let stickyDiags ← ds.stickyDiagsRef.get
        let diags := ds.diags
        return stickyDiags ++ diags |>.toArray

      -- Level is completed if there are no errors or warnings
      let completedWithWarnings : Bool := ¬ diag.any (·.severity? == some .error)
      let completed : Bool := completedWithWarnings ∧ ¬ diag.any (·.severity? == some .warning)

      let mut intermediateGoalCount := 0

      let positionsWithSource : Array (String.Pos.Raw × String) := Id.run do
        let mut res := #[]
        for i in [0:text.positions.size] do
          --TODO(ALEX): Generalize for other start positions
          let PROOF_START_LINE := 2
          if i < PROOF_START_LINE then continue -- skip problem statement
          -- for some reason, the client expects an empty tactic in the beginning
          if i == PROOF_START_LINE then
            res := res.push (text.positions[i]!, "")
          if i >= text.positions.size - 2 then continue -- skip final linebreak
          let source : String :=
            Substring.Raw.toString ⟨text.source, text.positions[i]!, text.positions[i + 1]!⟩
          if source.trimAscii.isEmpty then continue -- skip empty lines
          res := res.push (text.positions[i + 1]!, source)
        return res

      -- Drop the last position as we ensured that there is always a newline at the end
      for ((pos, source), i) in positionsWithSource.zipIdx do
        -- iterate over all steps in the proof and get the goals and hints at each position

        -- diags are labeled in Lsp-positions, which differ from the lean-internal
        -- positions by `1`.
        let lspPosAt := text.utf8PosToLspPos pos

        let diagsAtPos : Array InteractiveDiagnostic :=
          -- `+1` for getting the errors after the line.
          match i with
          | 0 =>
            -- `lspPosAt` is `(0, 0)`
            diag.filter (fun d => d.range.start == lspPosAt )
          | i' + 1 =>
            diag.filter (fun d =>
              ((text.utf8PosToLspPos <| (positionsWithSource[i']!).1) ≤ d.range.start) ∧
              d.range.start < lspPosAt )

        let diagsAtPos := filterUnsolvedGoal diagsAtPos


        let some snap := snaps.find? (fun snap => snap.endPos >= pos)
          | panic! "No snap found"
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
                  let some game := rc.initParams.rootUri?
                    | throwError "GameId not found"
                  let some level ← getLevel? {game := game, world := p.worldId, level := p.levelId}
                    | throwError "Level not found"
                  let hints ← findHints goal level
                  let interactiveGoal ← goalToInteractive goal
                  return ⟨interactiveGoal, hints⟩
              return interactiveGoals
          let goalsAtPos : Array InteractiveGoalWithHints := ⟨goalsAtPos'.foldl (· ++ ·) []⟩

          let diagsAtPos ← completionDiagnostics goalsAtPos.size intermediateGoalCount
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

end GameServer

@[server_rpc_method]
def Game.getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) :=
  FileWorker.getInteractiveGoals p

@[server_rpc_method]
def Game.getProofState (p : GameServer.ProofStateParams) : RequestM (RequestTask (Option GameServer.ProofState)) :=
  GameServer.getProofState p
