import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 8
Title "`and_or_distrib_left`"

open MyNat

Introduction
"
We know that $x(y+z)=xy+xz$ for numbers, and this
is called distributivity of multiplication over addition.
The same is true for `∧` and `∨` -- in fact `∧` distributes
over `∨` and `∨` distributes over `∧`. Let's prove one of these.
"

Statement --and_or_distrib_left
"If $P$. $Q$ and $R$ are true/false statements, then
$$P\\land(Q\\lor R)\\iff(P\\land Q)\\lor (P\\land R).$$ "
    (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  intro h
  rcases h with ⟨hp, hqr⟩
  rcases hqr with q | r
  left
  constructor
  exact hp
  exact q
  right
  constructor
  exact hp
  exact r
  intro h
  rcases h with hpq | hpr
  rcases hpq with ⟨p, q⟩
  constructor
  exact p
  left
  exact q
  rcases hpr with ⟨hp, hr⟩
  constructor
  exact hp
  right
  exact hr


Conclusion
"
You already know enough to embark on advanced addition world. But the next two levels comprise
just a couple more things.
"
