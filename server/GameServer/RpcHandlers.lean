import GameServer.EnvExtensions
import GameServer.InteractiveGoal
import GameServer.Hints
import I18n

open Lean
open Server
open Widget
open RequestM
open Meta

/-! ## GameGoal -/

namespace GameServer

def levelIdFromFileName? (initParams : Lsp.InitializeParams) (fileName : String) : Option LevelId := Id.run do
  let fileParts := fileName.splitOn "/"
  if fileParts.length == 3 then
    if let (some level, some game) := (fileParts[2]!.toNat?, initParams.rootUri?) then
      return some {game, world := fileParts[1]!, level := level}
  return none

def getLevelByFileName? [Monad m] [MonadEnv m] (initParams : Lsp.InitializeParams) (fileName : String) : m (Option GameLevel) := do
  let some levelId := levelIdFromFileName? initParams fileName
    | return none
  return ← getLevel? levelId

structure FVarBijection :=
  (forward : HashMap FVarId FVarId)
  (backward : HashMap FVarId FVarId)

instance : EmptyCollection FVarBijection := ⟨{},{}⟩

def FVarBijection.insert (bij : FVarBijection) (a b : FVarId) : FVarBijection :=
  ⟨bij.forward.insert a b, bij.backward.insert b a⟩

def FVarBijection.insert? (bij : FVarBijection) (a b : FVarId) : Option FVarBijection :=
  let a' := bij.forward.find? a
  let b' := bij.forward.find? b
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
def matchDecls (patterns : Array Expr) (fvars : Array Expr) (strict := true) (initBij : FVarBijection := {}) : MetaM (Option FVarBijection) := do
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
          (← instantiateMVars $ ← inferType pattern)
          (← instantiateMVars $ ← inferType fvar) bij then
        -- usedFvars := usedFvars.set! (fvars.size - j - 1) true
        bij := bij'.insert pattern.fvarId! fvar.fvarId!
        break
    if ! bij.forward.contains pattern.fvarId! then return none

  if !strict || fvars.all (fun fvar => bij.backward.contains fvar.fvarId!)
  then return some bij
  else return none

open Meta in
/-- Find all hints whose trigger matches the current goal -/
def findHints (goal : MVarId) (m : DocumentMeta) (initParams : Lsp.InitializeParams) : MetaM (Array GameHint) := do
  goal.withContext do
    let some level ← getLevelByFileName? initParams m.mkInputContext.fileName
      | throwError "Level not found: {m.mkInputContext.fileName}"
    let hints ← level.hints.filterMapM fun hint => do
      openAbstractCtxResult hint.goal fun hintFVars hintGoal => do
        if let some fvarBij := matchExpr (← instantiateMVars $ hintGoal) (← instantiateMVars $ ← inferType $ mkMVar goal)
        then

          -- NOTE: This code for `hintFVarsNames` is also duplicated in the
          -- "Statement" command, where `hint.rawText` is created. They need to be matching.
          -- NOTE: This is a bit a hack of somebody who does not know how meta-programming works.
          -- All we want here is a list of `userNames` for the `FVarId`s in `hintFVars`...
          -- and we wrap them in `«{}»` here since I don't know how to do it later.
          let mut hintFVarsNames : Array Expr := #[]
          for fvar in hintFVars do
            let name₁ ← fvar.fvarId!.getUserName
            hintFVarsNames := hintFVarsNames.push <| Expr.fvar ⟨s!"«\{{name₁}}»"⟩

          let lctx := (← goal.getDecl).lctx -- the player's local context
          if let some bij ← matchDecls hintFVars lctx.getFVars
            (strict := hint.strict) (initBij := fvarBij)
          then
            let userFVars := hintFVars.map fun v => bij.forward.findD v.fvarId! v.fvarId!
            -- Evaluate the text in the player's context to get the new variable names.
            let text := (← evalHintMessage hint.text) (userFVars.map Expr.fvar)
            let ctx := {env := ← getEnv, mctx := ← getMCtx, lctx := lctx, opts := {}}
            let text ← (MessageData.withContext ctx text).toString

            -- Here we map the goal's variable names to the player's variable names.
            let mut varNames : Array <| Name × Name := #[]
            for (fvar₁, fvar₂) in bij.forward.toArray do
              -- get the `userName` of the fvar in the opened local context of the hint.
              let name₁ ← fvar₁.getUserName
              -- get the `userName` in the player's local context.
              let name₂ := (lctx.get! fvar₂).userName
              varNames := varNames.push (name₁, name₂)

            return some {
              text := text,
              hidden := hint.hidden,
              rawText := hint.rawText,
              varNames := varNames }

          else return none
        else
          return none
    return hints

def filterUnsolvedGoal (a : Array InteractiveDiagnostic) :
    Array InteractiveDiagnostic :=
  a.filter (fun d => match d.message with
  | .append ⟨(.text x) :: _⟩ => x != "unsolved goals"
  | _ => true)

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
    (fun snap => ¬ (snap.infoTree.goalsAt? doc.meta.text doc.meta.text.positions.back).isEmpty)
    (notFoundX := return none)
    fun snap => do
      -- `snap` is the one snapshot containing the entire proof.
      let mut steps : Array <| InteractiveGoalsWithHints := #[]
      -- Question: Is there a difference between the diags of this snap and the last snap?
      -- Should we get the diags from there?
      -- Answer: The last snap only copied the diags from the end of this snap
      let mut diag : Array InteractiveDiagnostic := snap.interactiveDiags.toArray

      -- Level is completed if there are no errors or warnings
      let completedWithWarnings : Bool := ¬ diag.any (·.severity? == some .error)
      let completed : Bool := completedWithWarnings ∧ ¬ diag.any (·.severity? == some .warning)

      let mut intermediateGoalCount := 0

      let positionsWithSource : Array (String.Pos × String) := Id.run do
        let mut res := #[]
        for i in [0:text.positions.size] do
          --TODO(ALEX): Generalize for other start positions
          let PROOF_START_LINE := 2
          if i < PROOF_START_LINE then continue -- skip problem statement
          -- for some reason, the client expects an empty tactic in the beginning
          if i == PROOF_START_LINE then
            res := res.push (text.positions.get! i, "")
          if i >= text.positions.size - 2 then continue -- skip final linebreak
          let source : String :=
            Substring.toString ⟨text.source, text.positions.get! i, text.positions.get! (i + 1)⟩
          if source.trim.length == 0 then continue -- skip empty lines
          res := res.push (text.positions.get! (i + 1), source)
        return res

      -- Drop the last position as we ensured that there is always a newline at the end
      for ((pos, source), i) in positionsWithSource.zipWithIndex do
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
              ((text.utf8PosToLspPos <| (positionsWithSource.get! i').1) ≤ d.range.start) ∧
              d.range.start < lspPosAt )

        let diagsAtPos := filterUnsolvedGoal diagsAtPos

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
                  let hints := #[] -- TODO: HINTS← findHints goal doc.meta rc.initParams
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

      let lastPos := text.utf8PosToLspPos positionsWithSource.back.1
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
def Game.getProofState (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option GameServer.ProofState)) :=
  GameServer.getProofState p
