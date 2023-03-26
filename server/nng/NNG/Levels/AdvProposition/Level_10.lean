import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 10
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  by_cases p : P
  · by_cases q : Q
    intro h p' -- cc
    assumption
    intro h p'
    have g : ¬ P := h q
    contradiction
  · by_cases q : Q
    intro h p
    assumption
    intro h p
    contradiction

Conclusion
"

"
