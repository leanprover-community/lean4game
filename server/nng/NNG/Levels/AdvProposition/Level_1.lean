import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 1
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  exact p
  exact q

NewTactic constructor

Conclusion
"

"
