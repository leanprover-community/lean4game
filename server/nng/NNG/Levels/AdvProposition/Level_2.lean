import NNG.Metadata
import NNG.MyNat.Addition
import Std.Tactic.RCases

Game "NNG"
World "AdvProposition"
Level 2
Title "the `cases` tactic"

open MyNat

Introduction
"
If `P ∧ Q` is in the goal, then we can make progress with `split`.
But what if `P ∧ Q` is a hypothesis? In this case, the `cases` tactic will enable
us to extract proofs of `P` and `Q` from this hypothesis.

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
symmetry of the \"and\" relation. The obvious first move is

`intro h,`

because the goal is an implication and this tactic is guaranteed
to make progress. Now `h : P ∧ Q` is a hypothesis, and

`cases h with p q,`

will change `h`, the proof of `P ∧ Q`, into two proofs `p : P`
and `q : Q`. From there, `split` and `exact` will get you home.
"

set_option tactic.hygienic false

Statement --and_symm
"If $P$ and $Q$ are true/false statements, then $P\\land Q\\implies Q\\land P$. "
    (P Q : Prop) : P ∧ Q → Q ∧ P :=  by
  intro h
  rcases h with ⟨p, q⟩
  constructor
  exact q
  exact p

NewTactic rcases

Conclusion
"

"
