import TestGame.Metadata

import TestGame.Options.BigOperators
import Mathlib.Algebra.BigOperators.Fin

set_option tactic.hygienic false

open Nat

Game "TestGame"
World "Sum"
Level 2

Title "endliche Summe"

-- TODO: Tactics `mono` and `omega` are not ported yet.

Introduction
"
2^n > n^2   für   n ≥ 5
"

Statement
"2^n > n^2   für   n ≥ 5"
    (n : ℕ) : (n + 5)^2 < 2 ^ (n + 5) := by
induction' n with n ih
simp
rw [succ_eq_add_one]
simp_rw [add_pow_two] at *
ring_nf at ih ⊢
sorry



example (n : ℕ) (h : 5 ≤ n) : n^2 < 2 ^ n
| 0 | 1 | 2 | 3 | 4 => by
  sorry
| n + 5  => by sorry

NewTactics rw simp ring
