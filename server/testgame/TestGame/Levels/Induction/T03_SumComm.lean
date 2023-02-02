
import Mathlib.Algebra.BigOperators.Basic
import Mathlib

import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Induction"
Level 1

Title "Simp"

Introduction
"
"

Statement
""
    (n : ℕ) : True := by
  trivial

Tactics simp


-- Σ_i Σ_j ... = Σ_j Σ_i ...
-- rw [sum_comm]
example : ¬ ∀ (x : ℕ), x ≥ 10 := by
  push_neg
  use 5
  simp

¬ ∀ (...) ↔ ∃ (¬ ...)
