import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 1
Title "the `exact` tactic"

open MyNat

Introduction
"
What's going on in this world?

We're going to learn about manipulating propositions and proofs.
Fortunately, we don't need to learn a bunch of new tactics -- the
ones we just learnt (`exact`, `intro`, `have`, `apply`) will be perfect.

The levels in proposition world are \"back to normal\", we're proving
theorems, not constructing elements of sets. Or are we?
"

Statement
"If $P$ is true, and $P\\implies Q$ is also true, then $Q$ is true."
    (P Q : Prop) (p : P) (h : P → Q) : Q := by
Hint
"
In this situation, we have true/false statements $P$ and $Q$,
a proof $p$ of $P$, and $h$ is the hypothesis that $P\\implies Q$.
Our goal is to construct a proof of $Q$. It's clear what to do
*mathematically* to solve this goal, $P$ is true and $P$ implies $Q$
so $Q$ is true. But how to do it in Lean?

Adopting a point of view wholly unfamiliar to many mathematicians,
Lean interprets the hypothesis $h$ as a function from proofs
of $P$ to proofs of $Q$, so the rather surprising approach

```
exact h p
```

works to close the goal.

Note that `exact h P` (with a capital P) won't work;
this is a common error I see from beginners. \"We're trying to solve `P`
so it's exactly `P`\". The goal states the *theorem*, your job is to
construct the *proof*. $P$ is not a proof of $P$, it's $p$ that is a proof of $P$.

In Lean, Propositions, like sets, are types, and proofs, like elements of sets, are terms.
"
exact h p
