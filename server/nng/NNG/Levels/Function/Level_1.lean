import NNG.Metadata

-- TODO: Cannot import level from different world.

Game "NNG"
World "Function"
Level 1
Title "the `exact` tactic"

open MyNat

Introduction
"
## A new kind of goal.

All through addition world, our goals have been theorems,
and it was our job to find the proofs.
**The levels in function world aren't theorems**. This is the only world where
the levels aren't theorems in fact. In function world the object of a level
is to create an element of the set in the goal. The goal will look like `Goal: X`
with $X$ a set and you get rid of the goal by constructing an element of $X$.
I don't know if you noticed this, but you finished
essentially every goal of Addition World (and Multiplication World and Power World,
if you played them) with `rfl`.
This tactic is no use to us here.
We are going to have to learn a new way of solving goals &ndash; the `exact` tactic.


## The `exact` tactic

If you can explicitly see how to make an element of your goal set,
i.e. you have a formula for it, then you can just write `exact <formula>`
and this will close the goal.
"

Statement
"If $P$ is true, and $P\\implies Q$ is also true, then $Q$ is true."
    (P Q : Prop) (p : P) (h : P → Q) : Q := by
  Hint
  "In this situation, we have sets $P$ and $Q$ (but Lean calls them types),
  and an element $p$ of $P$ (written `p : P`
  but meaning $p\\in P$). We also have a function $h$ from $P$ to $Q$,
  and our goal is to construct an
  element of the set $Q$. It's clear what to do *mathematically* to solve
  this goal -- we can
  make an element of $Q$ by applying the function $h$ to
  the element $p$. But how to do it in Lean? There are at least two ways
  to explain this idea to Lean,
  and here we will learn about one of them, namely the method which
  uses the `exact` tactic.

  Concretely, `h p` is an element of type `Q`, so you can use `exact h p` to use it.

  Note that while in mathematics you might write $h(p)$, in Lean you always avoid brackets
  for function application: `h p`. Brackets are only used for grouping elements, for
  example for repeated funciton application, you could write `g (h p)`.
  "
  Hint (hidden := true) "
  **Important note**: Note that `exact h P,` won't work (with a capital $P$);
  this is a common error I see from beginners.
  $P$ is not an element of $P$, it's $p$ that is an element of $P$.

  So try `exact h p`.
  "
  exact h p

NewTactic exact simp

Conclusion
"

"
