import NNG.Levels.AdvAddition.Level_2


Game "NNG"
World "AdvAddition"
Level 3
Title "succ_eq_succ_of_eq"

open MyNat

Introduction
"
We are going to prove something completely obvious: if $a=b$ then
$\\operatorname{succ}(a)=\\operatorname{succ}(b)$. This is *not* `succ_inj`!
"

Statement MyNat.succ_eq_succ_of_eq
"For all naturals $a$ and $b$, $a=b\\implies \\operatorname{succ}(a)=\\operatorname{succ}(b)$."
    {a b : ℕ} : a = b → succ a = succ b := by
  Hint "This is trivial -- we can just rewrite our proof of `a=b`.
  But how do we get to that proof? Use the `intro` tactic."
  intro h
  Hint "Now we can indeed just `rw` `a` to `b`."
  rw [h]
  Hint (hidden := true) "Recall that `rfl` closes these goals."
  rfl

LemmaTab "Nat"
