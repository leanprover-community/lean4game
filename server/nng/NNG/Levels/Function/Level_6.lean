import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Function"
Level 6
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  intro f
  intro h
  intro p
  have j : Q → R := f p
  apply j
  apply h
  exact p

Conclusion
"

"
