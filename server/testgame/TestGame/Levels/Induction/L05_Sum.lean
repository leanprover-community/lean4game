import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Induction"
Level 5

Title "Induktion"

Introduction
"
"

open BigOperators

lemma arithmetic_sum (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction' n with n hn
  simp
  rw [Fin.sum_univ_castSucc]
  rw [mul_add]
  simp
  rw [mul_add, hn]
  simp_rw [Nat.succ_eq_one_add]
  ring


Statement
"Zeige $\\sum_{i = 0}^n i^3 = (\\sum_{i = 0}^n i)^2$."
  (n : ℕ) : (∑ i : Fin (n + 1), (i : ℕ)^3) = (∑ i : Fin (n + 1), (i : ℕ))^2 := by
  induction' n with n hn
  simp
  conv_rhs =>
    rw [Fin.sum_univ_castSucc]
    simp
    rw [add_pow_two]
    rw [arithmetic_sum]
    rw [mul_assoc, add_assoc, ←pow_two, ←Nat.succ_mul n, Nat.succ_eq_add_one, ←pow_succ]
  conv_lhs =>
    rw [Fin.sum_univ_castSucc]
    simp
    rw [hn]


NewTactics ring
