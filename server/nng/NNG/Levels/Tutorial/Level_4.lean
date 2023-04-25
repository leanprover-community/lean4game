import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Tutorial"
Level 4
Title "addition"

open MyNat

Introduction
"
Peano defined addition $a + b$ by induction on $b$, or, more precisely, by *recursion* on $b$.
He first explained how to add $0$ to a number: this is the base case.

* `add_zero (a : ℕ) : a + 0 = a`

We will call this theorem `add_zero`.
More precisely, `add_zero` is the name of the *proof* of the
theorem. Note the name of this proof. Mathematicians sometimes call it
\"Lemma 2.1\" or \"Hypothesis P6\" or something.
But computer scientists call it `add_zero` because it tells you what the answer to
\"x add zero\" is. It's a much better name than \"Lemma 2.1\".
Even better, you can use the `rw` tactic
with `add_zero`. If you ever see `x + 0` in your goal,
`rw [add_zero]` should simplify it to `x`. This is
because `add_zero` is a proof that `x + 0 = x`
(more precisely, `add_zero x` is a proof that `x + 0 = x` but
Lean can figure out the `x` from the context).

Now here's the inductive step. If you know how to add $d$ to $a$, then Peano
tells you how to add $\\operatorname{succ} (d)$ to $a$. It looks like this:

- `add_succ (a d : ℕ) : a + (succ d) = succ (a + d)`

What's going on here is that we assume `a + d` is already defined, and we define
`a + (succ d)` to be the number after it.
Note the name of this proof too: `add_succ` tells you how to add a successor
to something.
If you ever see `… + succ …` in your goal, you should be able to use
`rw [add_succ]` to make progress.
"

Statement
"For all natural numbers $a$, we have $a + \\operatorname{succ}(0) = \\operatorname{succ}(a)$."
    (a : ℕ) : a + succ 0 = succ a := by
  Hint "You find `{a} + succ …` in the goal, so you can use `rw` and `add_succ`
  to make progress."
  Hint (hidden := true) "Explicitely, type `rw [add_succ]`!"
  rw [add_succ]
  Hint "Now you see a term of the form `… + 0`, so you can use `add_zero`."
  Hint (hidden := true) "Explicitely, type `rw [add_zero]`!"
  Branch
    simp? -- TODO
  rw [add_zero]
  Hint (hidden := true) "Finally both sides are identical."
  rfl

NewLemma MyNat.add_succ MyNat.add_zero
NewDefinition Add

Conclusion
"
You have finished tutorial world! If you're happy, let's move onto Addition World,
and learn about proof by induction.

## Inspection time

If you want to examine the proof, toggle \"Editor mode\" and click somewhere
inside the proof to see the state at that point!
"
