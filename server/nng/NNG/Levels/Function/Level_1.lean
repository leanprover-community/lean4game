import NNG.Metadata
import NNG.MyNat.Theorems.Addition
import NNG.MyNat.Multiplication

Game "NNG"
World "Function"
Level 1
Title ""

open MyNat

Introduction
"

"

Statement
"If $P$ is true, and $P\\implies Q$ is also true, then $Q$ is true."
    (P Q : Prop) (p : P) (h : P → Q) : Q := by
  exact h p

NewTactic exact

Conclusion
"

"
