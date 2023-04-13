import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 3
Title "and_trans"

open MyNat

Introduction
"

"

Statement --and_trans
"If $P$, $Q$ and $R$ are true/false statements, then $P\\land Q$ and
$Q\\land R$ together imply $P\\land R$."
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
