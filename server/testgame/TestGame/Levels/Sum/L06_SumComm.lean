import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib.Algebra.BigOperators.Fin

set_option tactic.hygienic false

open BigOperators

Game "TestGame"
World "Sum"
Level 6

Title "Summe vertauschen"

Introduction
"
"

Statement
""
    (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, (i : ℕ) * j =
    ∑ j : Fin m, ∑ i : Fin n, (i : ℕ) * j := by
  rw [Finset.sum_comm]
