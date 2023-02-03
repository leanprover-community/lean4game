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
    (n : ℤ) : True := by
  sorry

NewTactics rw simp ring
