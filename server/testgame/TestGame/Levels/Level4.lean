import TestGame.Metadata

Game "TestGame"
World "Old"
Level 4

Title "Addition"

Introduction
"
Peano defined addition `a + b` by induction on `b`, or,
more precisely, by *recursion* on `b`. He first explained how to add 0 to a number:
this is the base case.

* `add_zero (a : ℕ) : a + 0 = a`

We will call this theorem `add_zero`. It has just appeared in your inventory!
Mathematicians sometimes call it \"Lemma 2.1\" or \"Hypothesis P6\" or something. But
computer scientists call it `add_zero` because it tells you
what the answer to \"$x$ add zero\" is. It's a *much* better name than \"Lemma 2.1\".
Even better, we can use the rewrite tactic with `add_zero`.
If you ever see `x + 0` in your goal, `rewrite [add_zero]` will simplify it to `x`.
This is because `add_zero` is a proof that `x + 0 = x` (more precisely,
`add_zero x` is a proof that `x + 0 = x` but Lean can figure out the `x` from the context).

Now here's the inductive step. If you know how to add `d` to `a`, then
Peano tells you how to add `succ(d)` to `a`. It looks like this:

* `add_succ (a d : ℕ) : a + succ(d) = succ (a + d)`

What's going on here is that we assume `a + d` is already
defined, and we define `a + succ(d)` to be the number after it.
This is also in your inventory now -- `add_succ` tells you
how to add a successor to something. If you ever see `... + succ ...`
in your goal, you should be able to use `rewrite [add_succ]` to make
progress. Here is a simple example where we shall see both. Let's prove
that $x$ add the number after $0$ is the number after $x$.

Observe that the goal mentions `... + succ ...`. So type

`rewrite [add_succ]`

and hit enter; see the goal change.
"

Statement "" (a : ℕ ) : a + succ 0 = succ a := by
  rewrite [add_succ]
  rewrite [add_zero]
  rfl

Message (a : ℕ) : succ (a + 0) = succ a  => "
Do you see that the goal now mentions ` ... + 0 ...`? So type

`rewrite [add_zero]`

and try to finish the level alone from there.
"

Conclusion "Congratulations for completing your fourth level! This is the end of the tutorial part
of the game. Serious things start in the next level."

Tactics rfl rewrite

Lemmas add_succ add_zero
