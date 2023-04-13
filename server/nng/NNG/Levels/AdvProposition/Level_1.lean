import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 1
Title "the `split` tactic"

open MyNat

Introduction
"
In this world we will learn five key tactics needed to solve all the
levels of the Natural Number Game, namely `split`, `cases`, `left`, `right`, and `exfalso`.
These, and `use` (which we'll get to in Inequality World) are all the
tactics you will need to beat all the levels of the game.

## Level 1: the `split` tactic.

The logical symbol `∧` means \"and\". If $P$ and $Q$ are propositions, then
$P\\land Q$ is the proposition \"$P$ and $Q$\". If your *goal* is `P ∧ Q` then
you can make progress with the `split` tactic, which turns one goal `⊢ P ∧ Q`
into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a `split`,
you will be able to finish off the goals with the `exact` tactic.
"

Statement
"If $P$ and $Q$ are true, then $P\\land Q$ is true."
    (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  exact p
  exact q

NewTactic constructor

Conclusion
"

"
