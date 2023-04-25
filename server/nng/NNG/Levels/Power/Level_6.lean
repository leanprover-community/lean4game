import NNG.Levels.Power.Level_5

Game "NNG"
World "Power"
Level 6
Title "mul_pow"

open MyNat

Introduction
"
You might find the tip at the end of level 9 of Multiplication World
useful in this one. You can go to the main menu and pop back into
Multiplication World and take a look -- you won't lose any of your
proofs.
"

Statement MyNat.mul_pow
"For all naturals $a$, $b$, $n$, we have $(ab) ^ n = a ^ nb ^ n$."
    (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with t Ht
  · rw [pow_zero, pow_zero, pow_zero, mul_one]
    rfl
  · rw [pow_succ, pow_succ, pow_succ, Ht]
    -- simp
    repeat rw [mul_assoc]
    rw [mul_comm a (_ * b), mul_assoc, mul_comm b a]
    rfl

LemmaTab "Pow"
