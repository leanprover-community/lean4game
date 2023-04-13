import NNG.Metadata
import NNG.MyNat.AdvAddition
import NNG.MyNat.Multiplication

Game "NNG"
World "AdvAddition"
Level 10
Title "add_left_eq_zero"

open MyNat

Introduction
"
In Lean, `a ≠ b` is *defined to mean* `(a = b) → false`. 
This means that if you see `a ≠ b` you can *literally treat
it as saying* `(a = b) → false`. Computer scientists would
say that these two terms are *definitionally equal*. 

The following lemma, $a+b=0\\implies b=0$, will be useful in inequality world.
Let me go through the proof, because it introduces several new
concepts: 

* `cases b`, where `b : mynat`
* `exfalso`
* `apply succ_ne_zero`

We're going to prove $a+b=0\\implies b=0$. Here is the
strategy. Each natural number is either `0` or `succ(d)` for
some other natural number `d`. So we can start the proof
with 

`cases b with d,`

and then we have two goals, the case `b = 0` (which you can solve easily)
and the case `b = succ(d)`, which looks like this:

```
a d : mynat,
H : a + succ d = 0
⊢ succ d = 0
```

Our goal is impossible to prove. However our hypothesis `H`
is also impossible, meaning that we still have a chance!
First let's see why `H` is impossible. We can

`rw add_succ at H,`

to turn `H` into `H : succ (a + d) = 0`. Because
`succ_ne_zero (a + d)` is a proof that `succ (a + d) ≠ 0`,
it is also a proof of the implication `succ (a + d) = 0 → false`.
Hence `succ_ne_zero (a + d) H` is a proof of `false`!
Unfortunately our goal is not `false`, it's a generic
false statement. 

Recall however that the `exfalso` command turns any goal into `false`
(it's logically OK because `false` implies every proposition, true or false).
You can probably take it from here.
"

Statement -- add_left_eq_zero
"If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $b = 0$."
    {{a b : ℕ}} (H : a + b = 0) : b = 0 := by
  induction b with d
  rfl
  rw [add_succ] at H
  exfalso
  apply succ_ne_zero (a + d)
  exact H

Conclusion
"

"
