import NNG.Levels.AdvAddition.Level_9
import Std.Tactic.RCases

Game "NNG"
World "AdvAddition"
Level 10
Title "add_left_eq_zero"

open MyNat

Introduction
"
In Lean, `a ≠ b` is *defined to mean* `(a = b) → False`.
This means that if you see `a ≠ b` you can *literally treat
it as saying* `(a = b) → False`. Computer scientists would
say that these two terms are *definitionally equal*.

The following lemma, $a+b=0\\implies b=0$, will be useful in inequality world.
"

Statement MyNat.add_left_eq_zero
"If $a$ and $b$ are natural numbers such that
$$ a + b = 0, $$
then $b = 0$."
    {a b : ℕ} (h : a + b = 0) : b = 0 := by
  Hint "
  You want to start of by making a distinction `b = 0` or `b = succ d` for some
  `d`. You can do this with

  ```
  induction b
  ```
  even if you are never going to use the induction hypothesis.
  "

  -- TODO: induction vs rcases

  Branch
    rcases b
    -- TODO: `⊢ zero = 0` :(
  induction b with d
  · rfl
  · Hint "This goal seems impossible! However, our hypothesis `h` is also impossible,
    meaning that we still have a chance!
    First let's see why `h` is impossible. We can

    ```
    rw [add_succ] at h
    ```
    "
    rw [add_succ] at h
    Hint "
    Because `succ_ne_zero (a + {d})` is a proof that `succ (a + {d}) ≠ 0`,
    it is also a proof of the implication `succ (a + {d}) = 0 → False`.
    Hence `succ_ne_zero (a + {d}) h` is a proof of `False`!

    Unfortunately our goal is not `False`, it's a generic
    false statement.

    Recall however that the `exfalso` command turns any goal into `False`
    (it's logically OK because `False` implies every proposition, true or false).
    You can probably take it from here.
    "
    Branch
      have j := succ_ne_zero (a + d) h
      exfalso
      exact j
    exfalso
    apply succ_ne_zero (a + d)
    exact h

LemmaTab "Add"

Conclusion
"

"
