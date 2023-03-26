import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 3
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q R S T U: Prop) (p : P) (h : P → Q) (i : Q → R)
    (j : Q → T) (k : S → T) (l : T → U) : U := by
  have q := h p
  have t := j q
  have u := l t
  exact u

DisabledTactic apply

Conclusion
"

"
