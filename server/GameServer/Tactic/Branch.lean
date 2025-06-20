import Lean

namespace GameServer

open Lean Elab

/-- This tactic allows us to execute an alternative sequence of tactics, but without affecting the
proof state. We use it to define Hints for alternative proof methods or dead ends. -/
elab (name := GameServer.Tactic.Branch) "Branch" t:tacticSeq : tactic => do
  let b ← saveState
  Tactic.evalTactic t

  -- Show an info whether the branch proofs all remaining goals.
  let gs ← Tactic.getUnsolvedGoals
  if gs.isEmpty then
    -- trace[debug] "This branch finishes the proof."
    pure ()
  else
    trace[debug] "This branch leaves open goals."

  let msgs ← Core.getMessageLog
  b.restore
  Core.setMessageLog msgs
