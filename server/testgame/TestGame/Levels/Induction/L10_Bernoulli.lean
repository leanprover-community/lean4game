import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Induction"
Level 5

Title "Bernoulli Ungleichung"

Introduction
"
TODO: Induktion (& induktion vs rcases)

"


example (x : ℕ) (n : ℕ) : 1 + n * x ≤ (x + 1) ^ n := by
  induction' n with n hn
  simp
  rw [Nat.succ_mul]
  rw [Nat.pow_succ]
  sorry

example (n : ℕ) : (∑ i : Fin (n + 1), ↑(2 * i - 1)) = n ^ 2 := by
  induction' n with n hn
  simp

#check Finset.sum_comm

Statement
"Zeige $\\sum_{i = 0}^n i = \\frac{n ⬝ (n + 1)}{2}$."
  (n : ℕ) : (∑ i : Fin (n + 1), ↑i) = n * (n + 1) / 2 := by
  apply hh1
  induction' n with n hn
  simp
  sorry
  -- rw [Fin.sum_univ_castSucc]
  -- simp [nat_succ]
  -- rw [mul_add, hn]
  -- ring

Tactics ring
