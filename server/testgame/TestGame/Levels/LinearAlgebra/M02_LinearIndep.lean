import TestGame.Metadata

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Real.Basic           -- definiert `ℝ`
import Mathlib.Algebra.Module.LinearMap -- definiert `→ₗ`
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
-- import Mathlib.LinearAlgebra.Finsupp
import Mathlib.Algebra.BigOperators.Basic -- default
-- import Mathlib.LinearAlgebra.LinearIndependent

Game "TestGame"
World "Basis"
Level 2

Title "Lineare Unabhängigkeit"

--notation "ℝ²" => Fin 2 → ℝ

Introduction
"
"

Statement
"Zeige, dass `![1, 0], ![1, 1]` linear unabhängig über `ℝ` sind."
    : True := by -- linearIndependent ℝ ![(![1, 0] : ℝ²), ![1, 1]] := by
  trivial

-- begin
--   rw fintype.linear_independent_iff,
--   intros c h,
--   simp at h,
--   intros i,
--   fin_cases i,
--   swap,
--   { exact h.2 },
--   { have h' := h.1,
--     rw [h.2, add_zero] at h',
--     exact h'}
-- end
