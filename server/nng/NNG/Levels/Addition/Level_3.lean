import NNG.Levels.Addition.Level_2

Game "NNG"
World "Addition"
Level 3
Title "succ_add"

open MyNat

Introduction
"
Oh no! On the way to `add_comm`, a wild `succ_add` appears. `succ_add`
is the proof that `succ(a) + b = succ(a + b)` for `a` and `b` in your
natural number type. We need to prove this now, because we will need
to use this result in our proof that `a + b = b + a` in the next level.

NB: think about why computer scientists called this result `succ_add` .
There is a logic to all the names.

Note that if you want to be more precise about exactly where you want
to rewrite something like `add_succ` (the proof you already have),
you can do things like `rw [add_succ (succ a)]` or
`rw [add_succ (succ a) d]`, telling Lean explicitly what to use for
the input variables for the function `add_succ`. Indeed, `add_succ`
is a function: it takes as input two variables `a` and `b` and outputs a proof
that `a + succ(b) = succ(a + b)`. The tactic `rw [add_succ]` just says to Lean \"guess
what the variables are\".
"

Statement MyNat.succ_add
"For all natural numbers $a, b$, we have
$ \\operatorname{succ}(a) + b = \\operatorname{succ}(a + b)$."
    (a b : ℕ) : succ a + b = succ (a + b)  := by
  Hint (hidden := true) "You might again want to start by induction
  on the right-most variable."
  Branch
    induction a
    Hint "Induction on `a` will not work."
  induction b with d hd
  · rw [add_zero]
    rw [add_zero]
    rfl
  · rw [add_succ]
    rw [hd]
    rw [add_succ]
    rfl

LemmaTab "Add"

Conclusion
"

"
