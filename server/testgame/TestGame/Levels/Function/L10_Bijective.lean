import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 8

Title ""

Introduction
"
"

Statement
""
  : (fun (n : ℤ) ↦ n + 1).Bijective := by
  constructor
  intro a b hab
  simp at hab
  assumption
  intro y
  use y-1
  simp
