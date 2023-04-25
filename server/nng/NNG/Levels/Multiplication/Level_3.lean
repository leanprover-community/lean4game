import NNG.Levels.Multiplication.Level_2

Game "NNG"
World "Multiplication"
Level 3
Title "one_mul"

open MyNat

Introduction
"
These proofs from addition world might be useful here:

* `one_eq_succ_zero : 1 = succ 0`
* `succ_eq_add_one a : succ a = a + 1`

We just proved `mul_one`, now let's prove `one_mul`.
Then we will have proved, in fancy terms,
that 1 is a \"left and right identity\"
for multiplication (just like we showed that
0 is a left and right identity for addition
with `add_zero` and `zero_add`).
"

Statement MyNat.one_mul
"For any natural number $m$, we have $ 1 \\cdot m = m$."
    (m : ℕ): 1 * m = m := by
  induction m with d hd
  · rw [mul_zero]
    rfl
  · rw [mul_succ]
    rw [hd]
    rw [succ_eq_add_one]
    rfl

LemmaTab "Mul"

Conclusion ""
