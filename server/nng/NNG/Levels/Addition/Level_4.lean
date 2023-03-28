import NNG.Metadata
import NNG.MyNat.Addition
import NNG.Levels.Addition.Level_3

Game "NNG"
World "Addition"
Level 4
Title "`add_comm` (boss level)"

open MyNat

namespace AdditionWorld

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
  induction b with d hd
  · rw [add_zero]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [hd]
    rw [add_succ]
    rfl

Introduction
"
[boss battle music]

Look in your inventory to see the proofs you have available.
These should be enough.
"

Statement add_comm
"On the set of natural numbers, addition is commutative.
In other words, for all natural numbers $a$ and $b$, we have
$a + b = b + a$."
    (a b : ℕ) : a + b = b + a := by
  Branch
    induction a with d hd
    · rw [zero_add]
      rw [add_zero]
      rfl
    · rw [succ_add]
      rw [hd]
      rw [add_succ]
      rfl
  induction b with d hd
  · rw [zero_add]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [hd]
    rw [succ_add]
    rfl

NewLemma MyNat.succ_add

Conclusion
"
If you got this far -- nice! You're nearly ready to make a choice:
Multiplication World or Function World. But there are just a couple
more useful lemmas in Addition World which you should prove first.
Press on to level 5.
"
