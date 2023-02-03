import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

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
  rw [nat_succ]
  sorry -- waiting on Algebra.BigOperators.Fin
  --simp [Fin.sum_univ_cast_succ]
  --rw [hn]
  --ring

NewTactics ring
