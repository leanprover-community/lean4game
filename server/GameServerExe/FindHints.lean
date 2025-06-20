import GameServerExe.Widget.InteractiveGoalWithHints
import GameServer.EnvExtensions
import GameServerExe.Util.FVarBijection
import GameServerExe.Widget.InteractiveDiagnostic

import I18n

namespace GameServer

open Lean
open Server
open GameServer.Widget
open Lean.Widget (InteractiveDiagnostic)
open RequestM
open Meta


/-- expects a file name of the form `/{worldId}/Level_{levelId}.lean` where `{levelId}` is a Nat. -/
def levelIdFromFileName? (initParams : Lsp.InitializeParams) (fileName : String) : Option LevelId := Id.run do
  let fileParts := fileName.splitOn "/"
  if fileParts.length == 3 then
    let some game := initParams.rootUri?
      | return none
    -- the filename has the form `Level_01.lean` and we extract `01`.
    let some level := ((fileParts[2]!.splitOn ".")[0]!.splitOn "_")[1]!.toNat?
      | return none
    return some {game := .mkSimple game, world := .mkSimple fileParts[1]!, level := level}
  return none

def getLevelByFileName? {m : Type → Type} [Monad m] [MonadEnv m] (initParams : Lsp.InitializeParams) (fileName : String) : m (Option GameServer.Level) := do
  let some levelId := levelIdFromFileName? initParams fileName
    | return none
  return ← getLevel? levelId

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

open Meta in
/-- Find all hints whose trigger matches the current goal -/
def findHints (goal : MVarId) (m : DocumentMeta) (initParams : Lsp.InitializeParams) : MetaM (Array GameHint) := do
  goal.withContext do
    let some level ← getLevelByFileName? initParams m.mkInputContext.fileName
      | throwError "Level not found: {m.mkInputContext.fileName}"
    let hints ← level.hints.filterMapM fun hint => do
      openAbstractCtxResult hint.goal fun hintFVars hintGoal => do
        let reducer := if hint.defeq then whnf else pure
        if let some fvarBij := matchExpr
          (← reducer <| ← instantiateMVars $ hintGoal)
          (← reducer <| ← instantiateMVars $ ← inferType $ mkMVar goal)
        then

          -- NOTE: This code for `hintFVarsNames` is also duplicated in the
          -- "Statement" command, where `hint.rawText` is created. They need to be matching.
          -- NOTE: This is a bit a hack of somebody who does not know how meta-programming works.
          -- All we want here is a list of `userNames` for the `FVarId`s in `hintFVars`...
          -- and we wrap them in `«{}»` here since I don't know how to do it later.
          let mut hintFVarsNames : Array Expr := #[]
          for fvar in hintFVars do
            let name₁ ← fvar.fvarId!.getUserName
            hintFVarsNames := hintFVarsNames.push <| Expr.fvar ⟨.mkSimple s!"«\{{name₁}}»"⟩

          let lctx := (← goal.getDecl).lctx -- the player's local context
          if let some bij ← matchDecls hintFVars lctx.getFVars
            (strict := hint.strict) (initBij := fvarBij) (defeq := hint.defeq)
          then
            let userFVars := hintFVars.map fun v => bij.forward.getD v.fvarId! v.fvarId!
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
