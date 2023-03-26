import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 5
Title ""

open MyNat

Introduction
"

"

Statement iff_trans
""
    (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  constructor
  intro p
  apply hqr.1
  apply hpq.1
  assumption
  intro r
  apply hpq.2
  apply hqr.2
  assumption

Conclusion
"

"
