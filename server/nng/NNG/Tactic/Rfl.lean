import Mathlib.Lean.Expr.Basic
import Lean.Elab.Tactic.Basic

/-! # `rfl` tactic

Added `withReducible` to prevent `rfl` proving stuff like `n + 0 = n`.
-/

namespace MyNat

open Lean Meta Elab Tactic

-- @[match_pattern] def MyNat.rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/-- Modified `rfl` tactic.

`rfl` closes goals of the form `A = A`.

Note that teh version for this game is somewhat weaker than the real one. -/
syntax (name := rfl) "rfl" : tactic

@[tactic MyNat.rfl] def evalRfl : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do withReducible <| mvarId.refl; pure []
-- TODO: `rfl` should be able to prove `R ↔ R`!


-- @[tactic MyNat.rfl] def evalRfl : Tactic := fun _ =>
--   liftMetaTactic fun mvarId => do mvarId.refl; pure []
-- (with_reducible rfl)

end MyNat
