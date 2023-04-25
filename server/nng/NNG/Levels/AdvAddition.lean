import NNG.Levels.AdvAddition.Level_13

Game "NNG"
World "AdvAddition"
Title "Advanced Addition World"

Introduction
"
Peano's original collection of axioms for the natural numbers contained two further
assumptions, which have not yet been mentioned in the game:

```
succ_inj (a b : ℕ) :
  succ a = succ b → a = b

zero_ne_succ (a : ℕ) :
  zero ≠ succ a
```

The reason they have not been used yet is that they are both implications,
that is,
of the form $P\\implies Q$. This is clear for `succ_inj a b`, which
says that for all $a$ and $b$ we have $\\operatorname{succ}(a)=\\operatorname{succ}(b)\\implies a=b$.
For `zero_ne_succ` the trick is that $X\\ne Y$ is *defined to mean*
$X = Y\\implies{\\tt False}$. If you have played through proposition world,
you now have the required Lean skills (i.e., you know the required
tactics) to work with these implications.
"