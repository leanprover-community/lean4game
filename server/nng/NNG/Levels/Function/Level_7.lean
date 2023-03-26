import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Function"
Level 7
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) := by
  intro f
  intro h
  intro p
  apply h
  apply f
  exact p

Conclusion
"

"
