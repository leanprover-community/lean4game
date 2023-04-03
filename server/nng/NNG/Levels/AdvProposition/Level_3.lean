import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 3
Title ""

open MyNat

Introduction
"

"

Statement --and_trans
""
    (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq
  intro hqr
  rcases hpq with ⟨p, q⟩
  rcases hqr with ⟨q', r⟩
  constructor
  assumption
  assumption

Conclusion
"

"
