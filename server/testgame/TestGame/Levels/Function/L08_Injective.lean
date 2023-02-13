import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 6

Title ""

Introduction
"
"

Statement
""
 : (fun (n : ℤ) ↦ n + 1).Injective := by
  intro a b hab
  simp at hab
  assumption
