import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "NNG"
World "AdvProposition"
Level 8
Title ""

open MyNat

Introduction
"

"

Statement and_or_distrib_left
""
    (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  intro h
  rcases h with ⟨hp, hqr⟩
  rcases hqr with q | r
  left
  constructor
  assumption
  assumption
  right
  constructor
  assumption
  assumption
  intro h
  rcases h with hpq | hpr
  rcases hpq with ⟨p, q⟩
  constructor
  assumption
  left
  assumption
  rcases hpr with ⟨hp, hr⟩
  constructor
  assumption
  right
  assumption

Conclusion
"

"
