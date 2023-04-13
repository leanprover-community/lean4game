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
The mathematical statement $P\\iff Q$ is equivalent to $(P\\implies Q)\\land(Q\\implies P)$. The `cases`
and `split` tactics work on hypotheses and goals (respectively) of the form `P ↔ Q`. If you need
to write an `↔` arrow you can do so by typing `\\iff`, but you shouldn't need to. After an initial
`intro h,` you can type `cases h with hpq hqp` to break `h : P ↔ Q` into its constituent parts.

"

Statement --iff_trans
"If $P$, $Q$ and $R$ are true/false statements, then
$P\\iff Q$ and $Q\\iff R$ together imply $P\\iff R$."
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
