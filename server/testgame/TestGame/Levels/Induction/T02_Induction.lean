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

NewTactics rw simp ring
