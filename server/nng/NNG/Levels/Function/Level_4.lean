import NNG.Metadata
import NNG.MyNat.Theorems.Addition
import NNG.MyNat.Multiplication

Game "NNG"
World "Function"
Level 4
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U) : U :=
by
  apply l
  apply j
  apply h
  exact p

NewTactic apply

Conclusion
"

"
