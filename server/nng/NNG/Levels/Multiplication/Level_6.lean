import NNG.Levels.Multiplication.Level_5

Game "NNG"
World "Multiplication"
Level 6
Title "succ_mul"

open MyNat

Introduction
"
We now begin our journey to `mul_comm`, the proof that `a * b = b * a`.
We'll get there in level 8. Until we're there, it is frustrating
but true that we cannot assume commutativity. We have `mul_succ`
but we're going to need `succ_mul` (guess what it says -- maybe you
are getting the hang of Lean's naming conventions).

Remember also that we have tools like

* `add_right_comm a b c : a + b + c = a + c + b`

These things are the tools we need to slowly build up the results
which we will need to do mathematics \"normally\".
We also now have access to Lean's `simp` tactic,
which will solve any goal which just needs a bunch
of rewrites of `add_assoc` and `add_comm`. Use if
you're getting lazy!
"

Statement MyNat.succ_mul
"For all natural numbers $a$ and $b$, we have
$\\operatorname{succ}(a) \\cdot b = ab + b$."
    (a b : ℕ) : succ a * b = a * b + b := by
  induction b with d hd
  · rw [mul_zero]
    rw [mul_zero]
    rw [add_zero]
    rfl
  · rw [mul_succ]
    rw [mul_succ]
    rw [hd]
    rw [add_succ]
    rw [add_succ]
    rw [add_right_comm]
    rfl

LemmaTab "Mul"

Conclusion
"

"
