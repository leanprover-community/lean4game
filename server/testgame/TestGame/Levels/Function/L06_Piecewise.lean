import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 4

Title ""

Introduction
"
"

open Set

def f2 : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1

#eval (f2 + f2) 2

#check range f2

Statement
""
    : True := by
  trivial

#check Set.piecewise
