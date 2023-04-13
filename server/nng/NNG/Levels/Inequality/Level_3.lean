import NNG.Metadata
import NNG.MyNat.LE
import Mathlib.Tactic.Use
import Std.Tactic.RCases

Game "NNG"
World "Inequality"
Level 3
Title "le_succ_of_le"

open MyNat

Introduction
"
We have seen how the `use` tactic makes progress on goals of the form `⊢ ∃ c, ...`.
But what do we do when we have a *hypothesis* of the form `h : ∃ c, ...`?
The hypothesis claims that there exists some natural number `c` with some
property. How are we going to get to that natural number `c`? It turns out
that the `cases` tactic can be used (just like it was used to extract
information from `∧` and `∨` and `↔` hypotheses). Let me talk you through
the proof of $a\\le b\\implies a\\le\\operatorname{succ}(b)$.

The goal is an implication so we clearly want to start with 

`intro h,`

. After this, if you *want*, you can do something like

`rw le_iff_exists_add at h ⊢,`

(get the sideways T with `\\|-` then space). This changes the `≤` into
its `∃` form in `h` and the goal -- but if you are happy with just
*imagining* the `∃` whenever you read a `≤` then you don't need to do this line.

Our hypothesis `h` is now `∃ (c : mynat), b = a + c` (or `a ≤ b` if you
elected not to do the definitional rewriting) so

`cases h with c hc,`

gives you the natural number `c` and the hypothesis `hc : b = a + c`.
Now use `use` wisely and you're home.

"

Statement
"For all naturals $a$, $b$, if $a\\leq b$ then $a\\leq \\operatorname{succ}(b)$. 
"
    (a b : ℕ) : a ≤ b → a ≤ (succ b) := by
  intro h
  rcases h with ⟨c, hc⟩
  rw [hc]
  use c + 1
  sorry
  --rfl

Conclusion
"

"
