import NNG.Levels.AdvAddition.Level_12

Game "NNG"
World "AdvAddition"
Level 13
Title "ne_succ_self"

open MyNat

Introduction
"
The last level in Advanced Addition World is the statement
that $n\\not=\\operatorname{succ}(n)$.
"

Statement --ne_succ_self
"For any natural number $n$, we have
$$ n \\neq \\operatorname{succ}(n). $$"
     (n : ℕ) : n ≠ succ n := by
  Hint (hidden := true) "I would start a proof by induction on `n`."
  induction n with d hd
  · apply zero_ne_succ
  · Hint (hidden := true) "If you have no clue, you could start with `rw [Ne, Not]`."
    Branch
      rw [Ne, Not]
    intro hs
    apply hd
    apply succ_inj
    exact hs

LemmaTab "Nat"

Conclusion
"
Congratulations. You've completed Advanced Addition World and can move on
to Advanced Multiplication World (after first doing
Multiplication World, if you didn't do it already).
"
