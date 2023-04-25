import GameServer.Commands

TacticDoc rfl
"
## Summary

`rfl` proves goals of the form `X = X`.

## Details

The `rfl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

## Example:
If it looks like this in the top right hand box:
```
Objects:
  a b c d : ℕ
Goal:
  (a + b) * (c + d) = (a + b) * (c + d)
```

then `rfl` will close the goal and solve the level.

## Game modifications
`rfl` in this game is weakened.

The real `rfl` could also proof goals of the form `A = B` where the
two sides are not *exactly identical* but merely
*\"definitionally equal\"*. That means the real `rfl`
could prove things like `a + 0 = a`.

"


TacticDoc rw
"
## Summary

If `h` is a proof of `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s.

### Variants

* `rw [← h#` (changes `Y` to `X`)
* `rw [h] at h2` (changes `X` to `Y` in hypothesis `h2` instead of the goal)
* `rw [h] at *` (changes `X` to `Y` in the goal and all hypotheses)

## Details

The `rw` tactic is a way to do \"substituting in\". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw [h]`
will change them all to `B`'s.

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).
For example, in world 1 level 4
we learn about `add_zero x : x + 0 = x`, and `rw [add_zero]`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw [h]` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:

```
Objects:
  x y : ℕ
Assumptions:
  h : x = y + y
Goal:
  succ (x + 0) = succ (y + y)
```

then

`rw [add_zero]`

will change the goal into `succ x = succ (y + y)`, and then

`rw [h]`

will change the goal into `succ (y + y) = succ (y + y)`, which
can be solved with `rfl`.

### Example:

You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:

```
Objects:
  x y : ℕ
Assumptions:
  h1 : x = y + 3
  h2 : 2 * y = x
Goal:
  y = 3
```
then `rw [h1] at h2` will turn `h2` into `h2 : 2 * y = y + 3`.

## Game modifications

The real `rw` tactic does automatically try to call `rfl` afterwards. We disabled this
feature for the game.
"

TacticDoc induction
"
"

TacticDoc exact
"
"

TacticDoc apply
"
"

TacticDoc intro
"
"

TacticDoc «have»
"
"

TacticDoc constructor
"
"

TacticDoc rcases
"
"

TacticDoc left
"
"

TacticDoc revert
"
"

TacticDoc tauto
"
"

TacticDoc right
"
"

TacticDoc by_cases
"
"

TacticDoc contradiction
"
"

TacticDoc exfalso
"
"

TacticDoc simp
"
"

TacticDoc «repeat»
"
"