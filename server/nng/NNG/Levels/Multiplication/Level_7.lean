import NNG.Levels.Multiplication.Level_6

Game "NNG"
World "Multiplication"
Level 7
Title "add_mul"

open MyNat

Introduction
"
We proved `mul_add` already, but because we don't have commutativity yet
we also need to prove `add_mul`. We have a bunch of tools now, so this won't
be too hard. You know what -- you can do this one by induction on any of
the variables. Try them all! Which works best? If you can't face
doing all the commutativity and associativity, remember the high-powered
`simp` tactic mentioned at the bottom of Addition World level 6,
which will solve any puzzle which needs only commutativity
and associativity. If your goal looks like `a + (b + c) = c + b + a` or something,
don't mess around doing it explicitly with `add_comm` and `add_assoc`,
just try `simp`.
"

Statement MyNat.add_mul
"Addition is distributive over multiplication.
In other words, for all natural numbers $a$, $b$ and $t$, we have
$(a + b) \times t = at + bt$."
    (a b t : ℕ) : (a + b) * t = a * t + b * t := by
  induction b with d hd
  · rw [zero_mul]
    rw [add_zero]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [succ_mul]
    rw [hd]
    rw [succ_mul]
    rw [add_assoc]
    rfl

LemmaTab "Mul"

Conclusion
"

"
