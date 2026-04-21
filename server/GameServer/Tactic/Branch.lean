import GameServer.EnvExtensions
import I18n.EnvExtension

namespace GameServer.Tactic

open Lean Elab I18n

/-- This tactic allows us to execute an alternative sequence of tactics, but without affecting the
proof state. We use it to define Hints for alternative proof methods or dead ends. -/
elab (name := Branch) "Branch" t:tacticSeq : tactic => do
  let b ← saveState
  Tactic.evalTactic t

  -- Show an info whether the branch proofs all remaining goals.
  let gs ← Tactic.getUnsolvedGoals
  if gs.isEmpty then
    -- trace[debug] "This branch finishes the proof."
    pure ()
  else
    trace[debug] "This branch leaves open goals."

  -- data to keep
  let msgs ← Core.getMessageLog
  let env ← getEnv
  let gameExtState := gameExt.getState env
  let translationExtState := untranslatedKeysExt.getState env

  -- restore state
  b.restore

  -- add data which should be kept
  Core.setMessageLog msgs
  modifyEnv (fun env => gameExt.setState env gameExtState)
  modifyEnv (fun env => untranslatedKeysExt.setState env translationExtState)
