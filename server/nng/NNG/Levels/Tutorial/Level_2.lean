import NNG.Metadata
import NNG.MyNat.Multiplication

Game "NNG"
World "Tutorial"
Level 2
Title "the rewrite (rw) tactic"

Introduction
"
In this level, you also get \"Assumptions\" about your objects. These are hypotheses of which
you assume (or know) that they are true.

The `rewrite` tactic is the way to \"substitute in\" the value of a variable.
If you have a hypothesis of the form `A = B`, and your goal mentions
the left hand side `A` somewhere,
then the rewrite tactic will replace the `A` in your goal with a `B`.

*(Note: For this game, `rw` is a shorthand for `rewrite`. Out in the real world, `rw` tries to call
`rfl` automatically afterwards.)*
"

Statement
"If $x$ and $y$ are natural numbers, and $y = x + 7$, then $2y = 2(x + 7)$."
    (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  Hint "You can use `rewrite [h]` to replace the `{y}` with `x + 7`.
  Note that the assumption `h` is written
  inside square brackets: `[h]`."
  rw [h]
  Hint "In this game not all hints are directly shown. If you need help finishing the proof, click
  on \"More Help\" below!"
  Hint (hidden := true)
  "Now both sides are identical, so you can use `rfl` to close the goal."
  rfl

NewTactic rw

Conclusion
"
If you want to inspect the proof you created, toggle \"Editor mode\" above.

There you can also move your cursor around the proof to see the \"state\" of the proof at this point.

Each tactic is written on a new line and Lean is sensitive to indentation (i.e. there must be no
spaces before any of the tactics)
"
