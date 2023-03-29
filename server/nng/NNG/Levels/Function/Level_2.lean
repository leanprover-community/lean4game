import NNG.Metadata
import NNG.MyNat.Theorems.Addition
import NNG.MyNat.Multiplication

Game "NNG"
World "Function"
Level 2
Title ""

open MyNat

Introduction
"

"

Statement
""
    : ℕ → ℕ := by
  intro n
  exact 3 * n + 2

NewTactic intro

Conclusion
"

"
