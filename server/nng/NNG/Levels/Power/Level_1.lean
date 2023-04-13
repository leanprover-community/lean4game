import NNG.Metadata
--import NNG.MyNat.Power

Game "NNG"
World "Power"
Level 1
Title "zero_pow_zero"

open MyNat

Introduction
"

"

Statement
"$0 ^ 0 = 1$"
    : (0 : ℕ) ^ 0 = (1 : ℕ) := by -- (0 : ℕ) ^ (0 : ℕ) = 1 := by
  trivial

Conclusion
"

"

