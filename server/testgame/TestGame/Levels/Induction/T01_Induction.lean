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
2^n > n^2   für   n ≥ 5
"

Statement
"2^n > n^2   für   n ≥ 5"
    (n : ℕ) : True := by
  sorry

Tactics rw simp ring
