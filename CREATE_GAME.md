# Level

A level is a single exercise that should be solved by the user. Here is an example:

```lean
import GameServer.Commands            -- also import everything else you need.

Game "NNG"
World "Addition"
Level 2                               -- must start at `1` and be consequtive.
Title "add_zero"

Introduction ""                       -- optional. Is displayed throughout the level.

Statement MyNat.zero_add              -- optional. if name is specified, the lemma will be added to the inventory
"description in mathematical term"    -- optional. mathematical description
    (n : ℕ) : n + 0 = n := by         -- statement: exactly how it would be in a `theorem`. (bug: forgets about implicit arguments)
  intro k
  rw [add_zero]
  Hint "look at {k}."                 -- hint at this place. `{k}` gets the user's name for the variable (bug currently)
  Hint (hidden := true) "more"        -- hidden hint
  use n
  Branch                              -- A branch in the proof. Does not modify the goal but useful
    simp                              -- to place hints at dead ends etc.
    tauto
  rw [add_comm]
  rfl

LemmaTab "Nat"                        -- optional. specify the tab that's open in the lemma inventory

NewLemma add_zero                     -- optional. add lemma to inventory
NewTactic rw                          -- optional. add lemma to inventory
NewDefinition Nat                     -- optional. add lemma to inventory
DisabledLemma add_zero                -- optional. disable specific lemmas
DisabledTactic tauto simp             -- optional. disable tactics
OnlyLemma add_zero                    -- optional. disable all lemmas but these
OnlyTactic assumption rw              -- optional. disable all tactics but these

Conclusion ""                         -- optional. Show when level completed
```

And in the following there are some tips that might be important.

## Imports

You're level can import levels from the same world

```
import NNG.Levels.Addition.Level_1
```

as well as entire other worlds

```
import NNG.Levels.Multiplication
```

However, you must not import a single level in a different world's level or
it will mess up the World introduction texts (bug?)

## Documentation (Lemmas, Tactics, Definitions)

It will complain when the specified lemma/tactic names do not have documentation.
In that case you need to add `LemmaDoc`/`TacticDoc`/`DefinitionDoc` entries in the
doc part (and `ctrl+shift+X`-reload your file in VSCode). See info under `Game > Documentation`

# World

combines multiple levels, like a chapter. Description pending.

# Game

Combines different games in form of a directed graph. Description pending.

## Documentation
It is recommended to have all documentation for the inventory centrally and import it in
the levels

```lean
LemmaDoc MyNat.add_squared as "add_squared" in "Pow"
"(missing)"

TacticDoc constructor
"(missing)"

DefinitionDoc One as "1"
"(missing)"
```

Notes:

* The lemma name must be **fully qualified**. The string display name can be arbitrary.
* Tactics must have their proper name. use `TacticDoc «have» ""` if it does not work
  without french quotes.
* Definition names can be arbitrary. E.g. I used `DefinitionDoc Symbol.Fun as "fun x ↦ x"` once.

There will be features added to get automatic information from mathlib!
