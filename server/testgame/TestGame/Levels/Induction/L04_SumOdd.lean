import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

Game "TestGame"
World "Induction"
Level 4

Title "Bernoulli Ungleichung"

Introduction
"
Hier nochmals eine Übung zur Induktion.
"

open BigOperators

Statement
"Zeige folgende Gleichung zur Summe aller ungeraden Zahlen:

$\\sum_{i = 0}^n (2n + 1) = n ^ 2$."
    (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  induction' n with n hn
  simp
  rw [Fin.sum_univ_castSucc]
  simp
  rw [hn, Nat.succ_eq_add_one]
  ring

NewTactics ring
