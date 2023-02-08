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
    (n : ℕ) (h : 5 ≤ n) : n^2 < 2 ^ n := by
  induction n with
  | 0 | 1 | 2 | 3 | 4 => by contradiction
  | n.succ  => by sorry


example (n : ℕ) (h : 5 ≤ n) : n^2 < 2 ^ n
| 0 | 1 | 2 | 3 | 4 => by
  sorry
| n + 5  => by sorry

NewTactics rw simp ring
