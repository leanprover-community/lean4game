import GameServer.Commands

DefinitionDoc MyNat as "ℕ"
"
The Natural Numbers.

## Game Modifications

This notation is for our own version of the natural numbers, called `MyNat`.
The natural numbers implemented in Lean's core are called `Nat`.

If you end up getting someting of type `Nat` in this game, you probably
need to write `(4 : ℕ)` to force it to be of type `MyNat`.
"