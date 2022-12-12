import TestGame.Metadata

Game "TestGame"
World "Old"
Level 2

Title "The rewriting spell"

Introduction
"
The rewrite spell is the way to \"substitute in\" the value
of an expression. In general, if you have a hypothesis of the form `A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`.

The documentation for `rewrite` just appeared in your spell book.
Play around with the menus and see what is there currently.
More information will appear as you progress.

Take a look in the top right box at what we have.
The variables $x$ and $y$ are natural numbers, and we have
an assumption `h` that $y = x + 7$. Our goal
is to prove that $2y=2(x+7)$. This goal is obvious -- we just
substitute in $y = x+7$ and we're done. In Lean, we do
this substitution using the `rewrite` spell. This spell takes a list of equalities
or equivalences so you can cast `rewrite [h]`.
"

Statement "" (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl

Message (x : ℕ) (y : ℕ) (h : y = x + 7) : 2*(x + 7) = 2*(x + 7) =>
"Great! Now the goal should be easy to reach using the `rfl` spell."

Conclusion "Congratulations for completing your second level!"

Tactics rfl rewrite
