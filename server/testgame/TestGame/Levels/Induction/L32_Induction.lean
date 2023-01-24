import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

Game "TestGame"
World "Induction"
Level 2

Title "Induktion"

Introduction
"
TODO: Induktion (& induktion vs rcases)

"


theorem nat_succ (n : ℕ) : Nat.succ n = n + 1 := rfl

lemma hh1 (n m : ℕ) (h : 2 * m = n) : m = n / 2 := by
  rw [←h]
  rw [Nat.mul_div_right]
  simp

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
