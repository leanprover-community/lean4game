import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "NNG"
World "AdvProposition"
Level 7
Title "`or_symm`"

open MyNat

Introduction
"
Proving that $(P\\lor Q)\\implies(Q\\lor P)$ involves an element of danger.
`intro h,` is the obvious start. But now,
even though the goal is an `∨` statement, both `left` and `right` put
you in a situation with an impossible goal. Fortunately, after `intro h,`
you can do `cases h with p q`. Then something new happens: because
there are two ways to prove `P ∨ Q` (namely, proving `P` or proving `Q`),
the `cases` tactic turns one goal into two, one for each case. You should
be able to make it home from there. 
"

Statement --or_symm
"If $P$ and $Q$ are true/false statements, then
$$P\\lor Q\\implies Q\\lor P.$$ "
    (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with p | q
  right
  exact p
  left
  exact q

Conclusion
"

"
