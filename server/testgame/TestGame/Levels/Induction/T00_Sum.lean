import TestGame.Metadata
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Induction"
Level 3

Title "Induktion"

Introduction
"
"

open BigOperators

Statement
"Zeige $\\sum_{i = 0}^n i^3 = (\\sum_{i = 0}^n i^3)^2$."
  (n : ℕ) : (∑ i : Fin (n + 1), (i : ℕ)^3) = (∑ i : Fin (n + 1), (i : ℕ))^2 := by
  induction n
  simp
  sorry

Tactics ring
