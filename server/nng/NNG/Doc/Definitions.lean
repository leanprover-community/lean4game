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
"

DefinitionDoc Add as "+" "
Addition on `ℕ` is defined through two axioms:

* `add_zero (a : ℕ) : a + 0 = a`
* `add_succ (a d : ℕ) : a + succ d = succ (a + d)`
"
  
DefinitionDoc Mul as "*" ""