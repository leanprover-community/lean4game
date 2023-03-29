import NNG.Metadata
import NNG.MyNat.Theorems.Addition
import NNG.MyNat.Multiplication

Game "NNG"
World "Function"
Level 5
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q : Type) : P → (Q → P) := by
  intro p
  intro q
  exact p

Conclusion
"

"
