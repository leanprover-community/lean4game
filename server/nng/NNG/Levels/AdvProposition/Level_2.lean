import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 2
Title ""

open MyNat

Introduction
"

"

set_option tactic.hygienic false

Statement --and_symm
""
    (P Q : Prop) : P ∧ Q → Q ∧ P :=  by
  intro h
  rcases h with ⟨p, q⟩
  constructor
  exact q
  exact p

NewTactic rcases

Conclusion
"

"
