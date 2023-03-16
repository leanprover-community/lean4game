import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib.Algebra.BigOperators.Fin

set_option tactic.hygienic false

Game "TestGame"
World "Sum"
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
  induction a
  norm_cast
  change 3 ∣ (Nat.succ n : ℤ) ^ 3 + 2 * (Nat.succ n : ℤ)
  rw [Int.ofNat_succ]
  sorry
  sorry

-- example (n : ℕ) : (n - 1) * (n + 1) = (n ^ 2 - 1) := by
--   induction' n with n hn
--   ring
--   rw [Nat.succ_eq_one_add]
--   rw []
