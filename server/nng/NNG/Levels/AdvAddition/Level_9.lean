import NNG.Levels.AdvAddition.Level_8

Game "NNG"
World "AdvAddition"
Level 9
Title "succ_ne_zero"

open MyNat

Introduction
"
Levels 9 to 13 introduce the last axiom of Peano, namely
that $0\\not=\\operatorname{succ}(a)$. The proof of this is called `zero_ne_succ a`.

```
zero_ne_succ (a : ¬) : 0 ≠ succ a
```

$X\\ne Y$ is *defined to mean* $X = Y\\implies{\\tt False}$, similar to how `¬A` was defined.
"
-- TODO: I dont think there is a `symmetry` tactic anymore.
-- The `symmetry` tactic will turn any goal of the form `R x y` into `R y x`,
-- if `R` is a symmetric binary relation (for example `=` or `≠`).
-- In particular, you can prove `succ_ne_zero` below by first using
-- `symmetry` and then `exact zero_ne_succ a`.

Statement MyNat.succ_ne_zero
"Zero is not the successor of any natural number."
    (a : ℕ) : succ a ≠ 0 := by
  Hint "You have several options how to start. One would be to recall that `≠` is defined as
  `(· = ·) → False` and start with `intro`. Or do `rw [Ne, Not]` to explicitely remove the
  `≠`. Or you could use the lemma `Ne.symm (a b : ℕ) : a ≠ b → b ≠ a` which I just added to your
  inventory."
  Branch
    rw [Ne, Not]
    intro h
    apply zero_ne_succ a
    rw [h]
    rfl
  Branch
    exact (zero_ne_succ a).symm
  apply Ne.symm
  exact zero_ne_succ a


NewLemma MyNat.zero_ne_succ Ne.symm Eq.symm Iff.symm
NewDefinition Ne
LemmaTab "Nat"

Conclusion
"

"
