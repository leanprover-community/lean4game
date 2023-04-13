import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "NNG"
World "AdvProposition"
Level 8
Title "`and_or_distrib_left`"

open MyNat

Introduction
"
We know that `x(y+z)=xy+xz` for numbers, and this
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
## Pro tip

Did you spot the import? What do you think it does?

If you follow the instructions at
<a href=\"https://github.com/leanprover-community/mathlib#installation\" target=\"blank\">the mathlib github page</a>
you will be able to install Lean and mathlib on your own system, and then you can create a new project
and experiment with such imports yourself.

"
