import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 7
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  intro hpq hqr
  intro p
  apply hqr
  apply hpq
  exact p

Conclusion
"

"
