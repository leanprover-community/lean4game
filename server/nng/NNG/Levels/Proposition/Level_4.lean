import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 4
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q R S T U: Prop) (p : P) (h : P → Q) (i : Q → R)
    (j : Q → T) (k : S → T) (l : T → U) : U := by
  apply l
  apply j
  apply h
  exact p

DisabledTactic «have» 

Conclusion
"

"
