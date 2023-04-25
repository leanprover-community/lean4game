import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 2
Title "the `rcases` tactic"

open MyNat

Introduction
"
If `P ∧ Q` is in the goal, then we can make progress with `constructor`.
But what if `P ∧ Q` is a hypothesis? In this case, the `rcases` tactic will enable
us to extract proofs of `P` and `Q` from this hypothesis.
"

Statement -- and_symm
"If $P$ and $Q$ are true/false statements, then $P\\land Q\\implies Q\\land P$. "
    (P Q : Prop) : P ∧ Q → Q ∧ P :=  by
  Hint "The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
  symmetry of the \"and\" relation. The obvious first move is

  ```
  intro h
  ```

  because the goal is an implication and this tactic is guaranteed
  to make progress."
  intro h
  Hint "Now `{h} : P ∧ Q` is a hypothesis, and

  ```
  rcases {h} with ⟨p, q⟩
  ```

  will change `{h}`, the proof of `P ∧ Q`, into two proofs `p : P`
  and `q : Q`.

  You can write `⟨p, q⟩` with `\\<>` or `\\<` and `\\>`. Note that `rcases h` by itself will just
  automatically name the new assumptions."
  rcases h with ⟨p, q⟩
  Hint "Now a combination of `constructor` and `exact` will get you home."
  constructor
  exact q
  exact p

NewTactic rcases

