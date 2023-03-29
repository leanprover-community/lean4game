import Adam.Metadata
import Mathlib

Game "Adam"
World "SetFunction"
Level 2

Title ""

Introduction
"
"

Statement
""
    (U : Set ℕ) (f : ℕ → ℕ) : U ⊆ f ⁻¹' (f '' U) := by
  intro x hx
  use x
  constructor
  assumption
  rfl
