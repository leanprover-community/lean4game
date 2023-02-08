import Mathlib.Algebra.BigOperators.Basic
import Mathlib

import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Induction"
Level 2

Title "endliche Summe"

Introduction
"
n^3 + 2n ist durch 3 teilbar für alle ganzen Zahlen n
"

Statement
"n^3 + 2n ist durch 3 teilbar für alle ganzen Zahlen n"
    (n : ℤ) : 3 ∣ n^3 + 2*n := by
  induction n
  sorry
  sorry

Tactics rw simp ring

-- example (n : ℕ) : (n - 1) * (n + 1) = (n ^ 2 - 1) := by
--   induction' n with n hn
--   ring
--   rw [Nat.succ_eq_one_add]
--   rw []
