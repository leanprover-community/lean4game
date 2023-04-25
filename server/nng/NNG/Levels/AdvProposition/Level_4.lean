import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 4
Title ""

open MyNat

Introduction
"
The mathematical statement $P\\iff Q$ is equivalent to $(P\\implies Q)\\land(Q\\implies P)$. The `rcases`
and `constructor` tactics work on hypotheses and goals (respectively) of the form `P ↔ Q`. If you need
to write an `↔` arrow you can do so by typing `\\iff`, but you shouldn't need to.

"

Statement --iff_trans
"If $P$, $Q$ and $R$ are true/false statements, then
$P\\iff Q$ and $Q\\iff R$ together imply $P\\iff R$."
    (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  Hint "Similar to \"and\", you can use `intro` and `rcases` to add the `P ↔ Q` to your
  assumptions and split it into its constituent parts."
  Branch
    intro hpq
    intro hqr
    Hint "Now you want to use `rcases {hpq} with ⟨pq, qp⟩`."
    rcases hpq with ⟨hpq, hqp⟩
    rcases hqr with ⟨hqr, hrq⟩
  intro ⟨pq, qp⟩
  intro ⟨qr, rq⟩
  Hint "If you want to prove an iff-statement, you can use `constructor` to split it
  into its two implications."
  constructor
  · intro p
    apply qr
    apply pq
    exact p
  · intro r
    apply qp
    apply rq
    exact r

NewDefinition Iff
