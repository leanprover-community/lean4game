import NNG.Levels.Multiplication
import NNG.MyNat.Power

Game "NNG"
World "Power"
Level 1
Title "zero_pow_zero"

open MyNat

Statement MyNat.zero_pow_zero
"$0 ^ 0 = 1$"
    : (0 : ℕ) ^ 0  = 1 := by
  rw [pow_zero]
  rfl

NewLemma MyNat.pow_zero MyNat.pow_succ
NewDefinition Pow
LemmaTab "Pow"
