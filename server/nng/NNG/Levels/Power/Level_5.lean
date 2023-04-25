import NNG.Levels.Power.Level_4


Game "NNG"
World "Power"
Level 5
Title "pow_add"

open MyNat

Statement MyNat.pow_add
"For all naturals $a$, $m$, $n$, we have $a^{m + n} = a ^ m  a ^ n$."
    (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with t ht
  · rw [add_zero, pow_zero, mul_one]
    rfl
  · rw [add_succ, pow_succ, pow_succ, ht, mul_assoc]
    rfl

LemmaTab "Pow"
