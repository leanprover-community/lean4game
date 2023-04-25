import NNG.Levels.Addition.Level_6

Game "NNG"
World "Addition"
Title "Addition World"

Introduction
"
Welcome to Addition World. If you've done all four levels in tutorial world
and know about `rw` and `rfl`, then you're in the right place. Here's
a reminder of the things you're now equipped with which we'll need in this world.

## Data:

  * a type called `ℕ` or `MyNat`.
  * a term `0 : ℕ`, interpreted as the number zero.
  * a function `succ : ℕ → ℕ`, with `succ n` interpreted as \"the number after `n`\".
  * Usual numerical notation `0,1,2` etc. (although `2` onwards will be of no use to us until much later ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : ℕ) : a + 0 = a`. Use with `rw [add_zero]`.
  * `add_succ (a b : ℕ) : a + succ(b) = succ(a + b)`. Use with `rw [add_succ]`.
  * The principle of mathematical induction. Use with `induction` (which we learn about in this chapter).


## Tactics:

  * `rfl` :  proves goals of the form `X = X`.
  * `rw [h]` : if `h` is a proof of `A = B`, changes all `A`'s in the goal to `B`'s.
  * `induction n with d hd` : we're going to learn this right now.


You will also find all this information in your Inventory to read the documentation.
"