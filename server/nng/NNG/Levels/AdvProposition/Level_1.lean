import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 1
Title "the `split` tactic"

open MyNat

Introduction
"
The logical symbol `∧` means \"and\". If $P$ and $Q$ are propositions, then
$P\\land Q$ is the proposition \"$P$ and $Q$\".
"

Statement
"If $P$ and $Q$ are true, then $P\\land Q$ is true."
    (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  Hint "If your *goal* is `P ∧ Q` then
  you can make progress with the `constructor` tactic, which turns one goal `P ∧ Q`
  into two goals, namely `P` and `Q`."
  constructor
  Hint "Now you have two goals. The first one is `P`, which you can proof now. The
  second one is `Q` and you see it in the queue \"Other Goals\". You will have to prove it afterwards."
  Hint (hidden := true) "This first goal can be proved with `exact p`."
  exact p
  -- Hint "Observe that now the first goal has been proved, so it disappears and you continue
  -- proving the second goal."
  -- Hint (hidden := true) "Like the first goal, this is a case for `exact`."
  -- -- TODO: It looks like these hints get shown above as well, but weirdly the hints from
  -- -- above to not get shown here.
  exact q

NewTactic constructor
NewDefinition And

Conclusion
"
"
