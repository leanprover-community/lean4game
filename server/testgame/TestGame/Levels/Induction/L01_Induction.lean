import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "Induction"
Level 1

Title "Induktion"

Introduction
"
Dieses Kapitel enthält noch ein paar Übungen zur Induktion.
"

Statement
"Zeige dass $5^n + 7$ durch $4$ teilbar ist."
    (n : ℕ) : 4 ∣ 5^n + 7 := by
  induction n
  simp
  rcases n_ih
  rw [Nat.pow_succ, Nat.mul_succ, add_assoc, h, mul_comm, ←mul_add]
  simp

--NewLemmas Nat.pow_succ, Nat.mul_succ, add_assoc, mul_comm, ←mul_add

-- example (n : ℕ) : Even (n^2 + n) := by
--   induction n
--   simp
--   rw [Nat.succ_eq_add_one]
--   rcases n_ih with ⟨x, h⟩
--   use x + n_1 + 1
--   ring_nf at *
--   rw [←h]
--   ring
