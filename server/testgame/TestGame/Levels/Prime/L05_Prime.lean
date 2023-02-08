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
Level 5

Title "Primzahlen"

Introduction
"
Mathematisch gesehen, bedeutet die Definition von vorhin dass $p$ ein
irreduzibles Element ist, und Primzahlen sind oft durch
`∀ (a b : ℕ), p ∣ a * b → p ∣ a ∨ p ∣ b`
definiert. Auf den natürlichen Zahlen, sind die beiden äquivalent.
"

Statement
"Zeige dass $p \\ge 2$ eine Primzahl ist, genau dann wenn
$p \\mid a\\cdot b \\Rightarrow (p \\mid a) \\lor (p \\mid b)$."
    (p : ℕ) (h₂ : 2 ≤ p):
    Nat.Prime p ↔ ∀ (a b : ℕ), p ∣ a * b → p ∣ a ∨ p ∣ b := by
  constructor
  intro h a b
  apply (Nat.Prime.dvd_mul h).mp
  intro h
  rw [Nat.prime_iff]
  change p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b
  rw [Nat.isUnit_iff, ←and_assoc]
  constructor
  constructor
  linarith
  linarith
  assumption
