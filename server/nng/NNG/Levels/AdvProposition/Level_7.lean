import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "NNG"
World "AdvProposition"
Level 7
Title ""

open MyNat

Introduction
"

"

Statement or_symm
""
    (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with p | q
  right
  exact p
  left
  exact q

Conclusion
"

"
