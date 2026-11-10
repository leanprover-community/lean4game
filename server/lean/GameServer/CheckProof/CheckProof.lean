import GameApi.EnvExtensions
import GameServer.CheckProof.CheckResult
import GameServer.CheckProof.FilterUnsolvedGoal
import GameServer.CheckProof.FindHints
import GameServer.Lean.InteractiveGoal

open Lean Server Widget RequestM

namespace GameServer

structure CheckProofParams where
  gameId : String
  worldId : String
  levelId : Nat
  /-- 0-based line in the document of the first tactic. -/
  proofStartLine : Nat
  /-- The number of lines of each step, which follow each other from `proofStartLine` on.
  A step can span several lines, e.g. `have h : P := by` and the proof of `P`. -/
  stepLines : Array Nat
  /-- Whether to include hover information for goals and hypotheses. -/
  hovers : Bool := false
  deriving FromJson, ToJson

def checkProof (p : CheckProofParams) : RequestM (RequestTask CheckResult) := do
  let doc ← readDoc
  let text := doc.meta.text
  let levelId : LevelId := { game := p.gameId, world := p.worldId, level := p.levelId }

  bindTaskCostly doc.cmdSnaps.waitAll fun (snaps, _) => do
    mapTaskCostly doc.reporter fun () => do
      let diags : Array InteractiveDiagnostic ← doc.diagnosticsMutex.atomically do
        let ds ← get
        return (← ds.stickyDiagsRef.get) ++ ds.diags |>.toArray

      -- Ignore diagnostics from the level file in front of the `Runner` command.
      let runnerLine := p.proofStartLine - 1
      let diags := diags.filter (·.range.start.line ≥ runnerLine)

      let completedWithWarnings := ¬ diags.any (·.severity? == some .error)
      let completed := completedWithWarnings ∧ ¬ diags.any (·.severity? == some .warning)

      let diags := filterUnsolvedGoal diags
      -- Diagnostics on the `Runner` line concern the entire proof,
      -- e.g. "declaration uses `sorry`", and are reported in the last step.
      let (proofDiags, diags) := diags.partition (·.range.start.line == runnerLine)

      -- The initial state is evaluated at the beginning of the first tactic.
      let startPos : String.Pos.Raw := Id.run do
        for i in [p.proofStartLine : text.positions.size - 1] do
          let lineStart := text.positions[i]!
          let line := Substring.Raw.toString ⟨text.source, lineStart, text.positions[i + 1]!⟩
          let tactic := line.trimAsciiStart.toString
          if !tactic.trimAscii.isEmpty then
            -- the indentation consists of ASCII whitespace, i.e. one byte per character
            return ⟨lineStart.byteIdx + line.utf8ByteSize - tactic.utf8ByteSize⟩
        return text.positions[p.proofStartLine]!

      -- The position after each step together with its tactic, without the indentation
      -- of its first line, which is also removed from the other lines.
      let stepPositions : Array (String.Pos.Raw × String) := Id.run do
        let mut res := #[(startPos, "")]
        let mut line := p.proofStartLine
        for n in p.stepLines do
          let last := min (line + n) (text.positions.size - 1)
          let source := Substring.Raw.toString ⟨text.source, text.positions[line]!, text.positions[last]!⟩
          line := last
          let lines := (source.trimAsciiEnd.toString.splitOn "\n").dropWhile (·.trimAscii.isEmpty)
          let some first := lines.head? | continue
          let indent := first.length - first.trimAsciiStart.toString.length
          let dedent (l : String) : String :=
            let ws := l.length - l.trimAsciiStart.toString.length
            (l.drop (min ws indent)).toString
          let tactic := "\n".intercalate (lines.map dedent)
          res := res.push (text.positions[last]!, tactic)
        return res

      let mut steps : Array CheckStep := #[]
      let mut hoverTable : HoverTable := {}
      let mut prevLspPos : Lsp.Position := ⟨p.proofStartLine, 0⟩
      for ((pos, tactic), i) in stepPositions.zipIdx do
        let lspPos := text.utf8PosToLspPos pos
        let isLast := i + 1 == stepPositions.size
        -- the last step also gets everything after the last tactic, e.g. unsolved goals
        let mut stepDiags := diags.filter fun (d : InteractiveDiagnostic) =>
          prevLspPos ≤ d.range.start ∧ (isLast ∨ d.range.start < lspPos)
        if isLast then
          stepDiags := stepDiags ++ proofDiags.map fun (d : InteractiveDiagnostic) =>
            { d with range := ⟨lspPos, lspPos⟩ }
        prevLspPos := lspPos

        let mut goals : Array CheckGoal := #[]
        if let some snap := snaps.find? (·.endPos >= pos) then
          for { ctxInfo := ci, tacticInfo := ti, useAfter, .. } in snap.infoTree.goalsAt? text pos do
            let ci := { ci with mctx := if useAfter then ti.mctxAfter else ti.mctxBefore }
            let goalMVars := if useAfter then ti.goalsAfter else ti.goalsBefore
            let interactiveGoals ← ci.runMetaM {} do
              let some level ← getLevel? levelId
                | throwError "Level not found: {levelId.world} {levelId.level}"
              goalMVars.toArray.mapM fun goal => do
                return (← goalToInteractive goal, ← findHints goal level)
            for (goal, hints) in interactiveGoals do
              if p.hovers then
                let (checkGoal, table) ←
                  (CheckGoal.ofInteractiveWithHovers goal hints).run hoverTable
                hoverTable := table
                goals := goals.push checkGoal
              else
                goals := goals.push (CheckGoal.ofInteractive goal hints)

        steps := steps.push {
          tactic
          goals
          diagnostics := stepDiags.map (CheckDiagnostic.ofInteractive p.proofStartLine) }

      return {
        steps,
        completed,
        completedWithWarnings
        hovers := hoverTable.hovers
        hoverDocs := hoverTable.docs }
