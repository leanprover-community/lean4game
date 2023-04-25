import NNG.Levels.Power.Level_3


Game "NNG"
World "Power"
Level 4
Title "one_pow"

open MyNat

Statement MyNat.one_pow
"For all naturals $m$, $1 ^ m = 1$."
    (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with t ht
  · rw [pow_zero]
    rfl
  · rw [pow_succ]
    rw [ht]
    rw [mul_one]
    rfl

LemmaTab "Pow"
