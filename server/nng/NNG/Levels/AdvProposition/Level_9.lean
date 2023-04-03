import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import NNG.MyNat.Theorems.Proposition



Game "NNG"
World "AdvProposition"
Level 9
Title ""

open MyNat

Introduction
"

"

Statement --contra
""
  (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro h
  rcases h with ⟨p, np ⟩
  contradiction
  -- rw [not_iff_imp_false] at np
  -- exfalso
  -- apply np
  -- exact p

NewTactic exfalso contradiction

Conclusion
"

"
