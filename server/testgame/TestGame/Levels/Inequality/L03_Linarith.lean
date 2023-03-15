import TestGame.Metadata
import Mathlib.Tactic.Linarith

Game "TestGame"
World "Inequality"
Level 3

Title "Linarith"

Introduction
"
Die Taktik `linarith` kann alle Systeme von linearen (Un-)gleichungen über `ℤ`, `ℚ`, etc. lösen.
Über `ℕ` ist sie etwas schwächer, aber einfache Aussagen kann sie trotzdem beweisen.
"

Statement
"Wenn $n \\ge 2$, zeige, dass $n$ nich Null sein kann."
    (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  linarith

NewTactic linarith

NewLemma Nat.pos_iff_ne_zero
