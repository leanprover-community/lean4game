import NNG.Metadata
import NNG.MyNat.Theorems.Addition
import NNG.MyNat.Multiplication

Game "NNG"
World "Function"
Level 3
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q R S T U: Type) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) :
    U := by
  have q := h p
  have t : T := j q
  have u : U := l t
  exact u

NewTactic «have»

Conclusion
"

"
