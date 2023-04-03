import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 4
Title ""

open MyNat

Introduction
"

"

Statement --iff_trans
""
    (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq
  intro hqr
  rcases hpq with ⟨hpq, hqp⟩
  rcases hqr with ⟨hqr, hrq⟩
  constructor
  exact fun x => hqr (hpq x) -- cc
  exact fun x => hqp (hrq x) -- cc

Conclusion
"

"
