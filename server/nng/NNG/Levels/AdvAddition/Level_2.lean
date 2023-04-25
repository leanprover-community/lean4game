import NNG.Levels.AdvAddition.Level_1


Game "NNG"
World "AdvAddition"
Level 2
Title "succ_succ_inj"

open MyNat

Introduction
"
In the below theorem, we need to apply `succ_inj` twice. Once to prove
$\\operatorname{succ}(\\operatorname{succ}(a))=\\operatorname{succ}(\\operatorname{succ}(b))
\\implies \\operatorname{succ}(a)=\\operatorname{succ}(b)$, and then again
to prove $\\operatorname{succ}(a)=\\operatorname{succ}(b)\\implies a=b$.
However `succ a = succ b` is
nowhere to be found, it's neither an assumption or a goal when we start
this level. You can make it with `have` or you can use `apply`.
"

Statement
"For all naturals $a$ and $b$, if we assume
$\\operatorname{succ}(\\operatorname{succ}(a))=\\operatorname{succ}(\\operatorname{succ}(b))$,
then we can deduce $a=b$. "
    {a b : ℕ} (h : succ (succ a) = succ (succ b)) : a = b := by
  Branch
    exact succ_inj (succ_inj h)
  apply succ_inj
  apply succ_inj
  assumption

LemmaTab "Nat"

Conclusion
"
## Sample solutions to this level.

Make sure you understand them all. And remember that `rw` should not be used
with `succ_inj` -- `rw` works only with equalities or `↔` statements,
not implications or functions.

```
example {a b : ℕ} (h : succ (succ a) = succ (succ b)) : a = b := by
  apply succ_inj
  apply succ_inj
  exact h

example {a b : ℕ} (h : succ (succ a) = succ (succ b)) : a = b := by
  apply succ_inj
  exact succ_inj h

example {a b : ℕ} (h : succ (succ a) = succ (succ b)) : a = b := by
  exact succ_inj (succ_inj h)
```
"
