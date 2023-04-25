import NNG.Levels.Addition.Level_1

Game "NNG"
World "Addition"
Level 2
Title "add_assoc (associativity of addition)"

open MyNat

Introduction
"
It's well-known that $(1 + 2) + 3 = 1 + (2 + 3)$; if we have three numbers
to add up, it doesn't matter which of the additions we do first. This fact
is called *associativity of addition* by mathematicians, and it is *not*
obvious. For example, subtraction really is not associative: $(6 - 2) - 1$
is really not equal to $6 - (2 - 1)$. We are going to have to prove
that addition, as defined the way we've defined it, is associative.

See if you can prove associativity of addition.
"

Statement MyNat.add_assoc

"On the set of natural numbers, addition is associative.
In other words, for all natural numbers $a, b$ and $c$, we have
$ (a + b) + c = a + (b + c). $"
    (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  Hint "Because addition was defined by recursion on the right-most variable,
  use induction on the right-most variable (try other variables at your peril!).

  Note that when Lean writes `a + b + c`, it means `(a + b) + c`. If it wants to talk
  about `a + (b + c)` it will put the brackets in explictly."
  Branch
    induction a
    Hint "Good luck with that…"
    simp?
    --rw [zero_add, zero_add]
    --rfl
  Branch
    induction b
    Hint "Good luck with that…"
  induction c with c hc
  Hint (hidden := true) "look at the lemma `add_zero`."
  rw [add_zero]
  Hint "`rw [add_zero]` only rewrites one term of the form `… + 0`, so you might to
  use it multiple times."
  rw [add_zero]
  rfl
  Hint (hidden := true) "`add_succ` might help here."
  rw [add_succ]
  rw [add_succ]
  rw [add_succ]
  Hint (hidden := true) "Now you can use the induction hypothesis."
  rw [hc]
  rfl

NewLemma MyNat.zero_add
LemmaTab "Add"
