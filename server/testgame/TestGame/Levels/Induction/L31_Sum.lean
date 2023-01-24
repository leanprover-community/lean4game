import Mathlib.Algebra.BigOperators.Basic
import Mathlib

import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Induction"
Level 1

Title "Summe"

Introduction
"
"

Statement
""
    (n : ℕ) : 2 * (∑ i : Fin (n+1), ↑i) = n * (n + 1) := by
  induction' n with n hn
  simp
  sorry -- done in Lean3.

Tactics intro constructor assumption
