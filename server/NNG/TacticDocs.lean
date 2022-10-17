import NNG.GameServer.Commands

import NNG.Tactics

TacticDoc rfl
"
## Summary

`rfl` proves goals of the form `X = X`.

## Details

The `rfl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
Objects
  a b c d : ℕ
Prove:
  (a + b) * (c + d) = (a + b) * (c + d)
```

then

`rfl`

will close the goal and solve the level."

TacticDoc induction_on
"
## Summary

If `n : ℕ` is in our objects list, then `induction_on n`
attempts to prove the current goal by induction on `n`, with the inductive
assumption in the `succ` case being `ind_hyp`.

### Example:
If your current goal is:
```
Objects
  n : ℕ
Prove:
  2 * n = n + n
```

then

`induction_on n`

will give us two goals:

```
Prove:
  2 * 0 = 0 + 0
```

and
```
Objects
  n : ℕ,
Assumptions
  ind_hyp : 2 * n = n + n
Prove:
  2 * succ n = succ n + succ n
```
"

TacticDoc rewrite
"
## Summary

If `h` is a proof of `X = Y`, then `rewrite [h],` will change
all `X`s in the goal to `Y`s. Variants: `rewrite [<- h]` (changes
`Y` to `X`) and
`rewrite [h] at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).

## Details

The `rewrite` tactic is a way to do \"substituting in\". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rewrite h`
will change them all to `B`'s. 

2) The `rewrite` tactic will also work with proofs of theorems
which are equalities (look for them in the inventory).
For example, if your inventory contains `add_zero x : x + 0 = x`, 
then `rewrite [add_zero]` will change `x + 0` into `x` in your goal 
(or fail with an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rewrite` is not the tactic you want to use. For example,
`rewrite [P = Q]` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rewrite [h]` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rewrite [<- h]` (get the arrow with `\\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
Objects
  x y : ℕ
Assumptions  
  h : x = y + y
Prove:
  succ (x + 0) = succ (y + y)
```

then

`rewrite [add_zero]`

will change the goal into `succ x = succ (y + y)`, and then

`rewrite [h]`

will change the goal into `succ (y + y) = succ (y + y)`, which
can be solved with `rfl,`.

### Example: 
You can use `rewrite` to change a hypothesis as well. 
For example, if your local context looks like this:
```
Objects
  x y : ℕ
Assumptions
  h1 : x = y + 3
  h2 : 2 * y = x
Prove:
  y = 3
```
then `rewrite [h1] at h2` will turn `h2` into `h2 : 2 * y = y + 3`.
"

TacticDoc intro
"Useful to introduce stuff"

TacticSet basics := rfl induction_on intro rewrite