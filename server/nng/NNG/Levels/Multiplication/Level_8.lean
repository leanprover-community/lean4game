import NNG.Levels.Multiplication.Level_7

Game "NNG"
World "Multiplication"
Level 8
Title "mul_comm"

open MyNat

Introduction
"
Finally, the boss level of multiplication world. But (assuming you
didn't cheat) you are well-prepared for it -- you have `zero_mul`
and `mul_zero`, as well as `succ_mul` and `mul_succ`. After this
level you can of course throw away one of each pair if you like,
but I would recommend you hold on to them, sometimes it's convenient
to have exactly the right tools to do a job.
"

Statement MyNat.mul_comm
"Multiplication is commutative."
    (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  · rw [zero_mul]
    rw [mul_zero]
    rfl
  · rw [succ_mul]
    rw [← hd]
    rw [mul_succ]
    rfl

LemmaTab "Mul"

Conclusion
"
You've now proved that the natural numbers are a commutative semiring!
That's the last collectible in Multiplication World.

* `CommSemiring ℕ`

But don't leave multiplication just yet -- prove `mul_left_comm`, the last
level of the world, and then we can beef up the power of `simp`.
"

-- TODO: collectible
-- instance mynat.comm_semiring : comm_semiring mynat := by structure_helper