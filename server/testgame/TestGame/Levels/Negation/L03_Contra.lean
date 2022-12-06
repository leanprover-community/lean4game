import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Contradiction"
Level 3

Title "Widerspruch"

Introduction
"
Im weiteren kann man auch Widersprüche erhalten, wenn man Annahmen der Form
`A = B` hat, wo Lean weiss, dass `A und `B` unterschiedlich sind, z.B. `0 = 1` in `ℕ`
oder auch Annahmen der Form `A ≠ A` (`\\ne`).
"

Statement
  "Ein Widerspruch impliziert alles."
    (A : Prop) (a b c : ℕ) (g₁ : a = b) (g₂ : b = c) (h : a ≠ c) : A := by
  rw [g₁] at h
  contradiction

Message (A : Prop) (a : ℕ) (b : ℕ) (c : ℕ) (g₁ : a = b) (g₂ : b = c) (h : a ≠ c) : A =>
  "Recap: `rw [...] at h` hilft dir hier."

Message (A : Prop) (a : ℕ) (b : ℕ) (c : ℕ) (g₁ : a = b) (g₂ : b = c) (h : b ≠ c) : A =>
  "`b ≠ c` muss man als `¬ (b = c)` lesen. Deshalb findet `contradiction` hier direkt
  einen Widerspruch."

Tactics contradiction
