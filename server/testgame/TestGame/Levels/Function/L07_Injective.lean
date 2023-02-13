import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 5

Title ""

Introduction
"
"
open Set Function

def f3 : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1

#eval (f3 + f3) 2

example : ¬ f3.Injective := by
  unfold Injective
  push_neg
  use 2
  use 3
  simp
