import GameServer.Commands

DefinitionDoc MyNat as "ℕ"
"
The Natural Numbers. These are constructed through:

* `(0 : ℕ)`, an element called zero.
* `(succ : ℕ → ℕ)`, the successor function , i.e. one is `succ 0` and two is `succ (succ 0)`.
* `induction` (or `rcases`), tactics to treat the cases $n = 0$ and `n = m + 1` seperately.

## Game Modifications

This notation is for our own version of the natural numbers, called `MyNat`.
The natural numbers implemented in Lean's core are called `Nat`.

If you end up getting someting of type `Nat` in this game, you probably
need to write `(4 : ℕ)` to force it to be of type `MyNat`.

*Write with `\\N`.*
"

DefinitionDoc Add as "+" "
Addition on `ℕ` is defined through two axioms:

* `add_zero (a : ℕ) : a + 0 = a`
* `add_succ (a d : ℕ) : a + succ d = succ (a + d)`
"

DefinitionDoc Pow as "^" "
Power on `ℕ` is defined through two axioms:

* `pow_zero (a : ℕ) : a ^ 0 = 1`
* `pow_succ (a b : ℕ) : a ^ succ b = a ^ b * a`

## Game-specific notes

Note that you might need to manually specify the type of the first number:

```
(2 : ℕ) ^ 1
```

If you write `2 ^ 1` then lean will try to work in it's inbuild `Nat`, not in
the game's natural numbers `MyNat`.
"

DefinitionDoc One as "1" "
`1 : ℕ` is by definition `succ 0`. Use `one_eq_succ_zero`
to change between the two.
"

DefinitionDoc False as "False" "
`False` is a proposition that that is always false, in contrast to `True` which is always true.

A proof of `False`, i.e. `(h : False)` is used to implement a contradiction: From a proof of `False`
anything follows, *ad absurdum*.

For example, \"not\" (`¬ A`) is therefore implemented as `A → False`.
(\"If `A` is true then we have a contradiction.\")
"

DefinitionDoc Not as "¬" "
Logical \"not\" is implemented as `¬ A := A → False`.

*Write with `\\n`.*
"

DefinitionDoc And as "∧" "
(missing)

*Write with `\\and`.*
"

DefinitionDoc Or as "∨" "
(missing)

*Write with `\\or`.*
"

DefinitionDoc Iff as "↔" "
(missing)

*Write with `\\iff`.*
"

DefinitionDoc Mul as "*" ""

DefinitionDoc Ne as "≠" ""