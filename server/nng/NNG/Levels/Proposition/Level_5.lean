import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 5
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q : Prop) : P → (Q → P) := by
  intro p
  intro q
  exact p

Conclusion
"

"
