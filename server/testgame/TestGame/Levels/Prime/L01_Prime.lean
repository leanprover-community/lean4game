import TestGame.Metadata
import Mathlib.Data.Nat.Prime

import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

import TestGame.ToBePorted

Game "TestGame"
World "Prime"
Level 1

Title "Primzahlen"

Introduction
"
"

Statement
  "TODO"
    (n : ℕ) : ∃! (n : ℕ), Nat.Prime n ∧ Even n := by
  use (2 : ℕ)
  constructor
  simp only [true_and]
  use 1
  intro y
  rintro ⟨h₁, h₂⟩
  rw [← Nat.Prime.even_iff]
  assumption
  assumption

Conclusion ""

NewTactics

NewLemmas
