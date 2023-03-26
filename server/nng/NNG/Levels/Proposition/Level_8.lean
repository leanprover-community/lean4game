import NNG.Metadata
import NNG.MyNat.Addition
import NNG.MyNat.Theorems.Proposition


Game "NNG"
World "Proposition"
Level 8
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  rw [not_iff_imp_false]
  rw [not_iff_imp_false]
  intro f
  intro h
  intro p
  apply h
  apply f
  exact p

NewLemma not_iff_imp_false

Conclusion
"

"
