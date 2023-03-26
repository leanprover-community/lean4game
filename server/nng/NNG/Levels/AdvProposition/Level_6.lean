import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
--import Mathlib.Logic.Basic

Game "NNG"
World "AdvProposition"
Level 6
Title ""

open MyNat

Introduction
"

"

Statement
""
    (P Q : Prop) : Q → (P ∨ Q) := by
  intro q
  right
  assumption

NewTactic left right

Conclusion
"

"
