import TestGame.Metadata
import Mathlib.Tactic.Ring

Game "TestGame"
World "Function"
Level 1

Title "Funktionen"

Introduction
"
Funktionen werden in Lean als `(f : ℕ → ℕ)` geschrieben (`\\to`), also mit dem gleichen
Pfeil wie Implikationen. Entsprechend kann man Implikationen und Funktionen genau
gleich behandeln.

"

Statement : ∃ (f : ℕ → ℕ), ∀ (x : ℕ), f x = 0 := by
  let g := fun (x : ℕ) ↦ 0
  use g
  simp

Conclusion ""

NewTactic use simp
