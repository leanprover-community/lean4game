import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 8

Title "Surjektive"

Introduction
"
"

Statement
""
: (fun (n : ℤ) ↦ n + 1).Surjective := by
  intro y
  use y-1
  simp
