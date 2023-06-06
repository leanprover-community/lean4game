# Creating a game.

Ideally one takes the [NNG template](https://github.com/hhu-adam/NNG4) to create a new game.

## Game Structure

A game consist of worlds which have multiple levels each. In the following we describe how to create a level file and how to combine these into a game.

### Level

#### Preample

A level file is a lean file that imports at least `GameServer.Commands` and starts with the four lean commands

```lean
Game "NNG"
World "Addition"
Level 1
Title "The rfl tactic"
```

Note that the levels inside a world must have consequtive numbering starting with `1`. The `Game`
and `World` strings can be anything.

#### Statement

The core of a level is the `Statement`, which is the exercise that should be proven:

```lean
Statement MyNat.zero_add
"For all natural numbers $n$, we have $0 + n = n$."
    (n : ℕ) : 0 + n = n := by
  Hint "You can start a proof by `induction n`."
  induction n with n hn
  · Hint "This is the base case."
    rw [add_zero]
    rfl
  · Hint "This is the induction hypothesis"
    rw [add_succ]
    Branch
      simp
      Hint "A branch is an alternative tactic sequence. Does not need to finish the proof."
    rw [hn]
    rfl
```

The first two arguments (name, attributes, and description) are optional. Thereafter you have a statement and a proof.

- The proof should always be a tactic proof, i.e. the `:= by` is mandatory.
- In the proof you can use `Hint "text"` to display text if the goal state in-game matches the one where `Hint` is placed. For more options about hints, see below.
- In the proof you can add a `Branch` that runs an alternativ tactic sequence, which helps setting `Hints` in different places. The `Branch` does not affect the main proof and does not need to finish any goals.
- If you specify a name (`MyNat.zero_add`), this lemma will be available in future levels. (Note that a future level must also import this level, so that Lean knows about the added statement). The name must be *fully qualified*.
- If you add a description (i.e. non-Lean exercise statement), it will be shown above the exercise. It supports Markdown (including katex).

#### Introduction/Conclusion

Optionally, you can add a `Introduction "some text"` and `Conclusion "some text"` to your level. the introduction will always be visible on top, the conclusion is displayed once the level is solved.

#### Lemmas/Tactics/Definitions

Only enabled lemmas/tactics/definitions (called "items" here) are available in a level.

To add a new item in a level, you can add

```lean
NewTactic rfl simp
NewLemma MyNat.add_zero
NewDefinition Nat
```

Once added, items will be available in all future levels/worlds, unless you disable them for a particular level with

```lean
DisabledTactic tauto
DisabledLemma MyNat.add_zero
```

or specify explicitely which items should be available with

```lean
OnlyTactic rw rfl apply
OnlyLemma MyNat.add_zero
```

Lastly, all items need documentation entries (which are imported in the level), see more about that below. There is also explains the `LemmaTab`

### World

Multiple levels are combined into a world and the worlds are then added to the game. It is recommended that all levels of a world are inside one folder (e.g. `NNG/Levels/Addition/`) and
then there is one world file (`NNG/Levels/Addition.lean`) which contains the following

```lean
import NNG.Levels.Addition.Level_1
import NNG.Levels.Addition.Level_2

Game "NNG"
World "Addition"
Title "Addition World"

Introduction "some text"
```

The `Title` is the world's display title. The `Introduction` is displayed before loading level 1.
Note that all levels of a world should be imported by the world file and they **must not** be
imported in another world's levels. (bug?)

However, you can import an entire world in a different world's level: `import NNG.Levels.Addition`

### Game

The Game itself (i.e. the main file of you lake project, `NNG.lean`) should import all worlds and have the following layout, concluding with `MakeGame`:

```lean
import NNG.Levels.Addition
import NNG.Levels.Multiplication
import NNG.Levels.Power

Game "NNG"
Title "Natural Number Game"
Introduction "some text"

Path Addition → Multiplication → Power

MakeGame
```

There can be several `Path` statements to define the relation between the worlds. The worlds
must form a directed acyclic graph, i.e. have no loops. The order of worlds influences which tactics and lemmas will be unlocked in a given level.

### Documentation

Each tactic, lemma, or definition (all called items here) that is introduced in the game
needs a documentation entry. These are statements of the following form:

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
* Definition names can be arbitrary. E.g. I used `DefinitionDoc Symbol.Fun as "fun x ↦ x" "(missing)"` once.

Moreover, the lemmas are in sorted in tabs (the `in "Pow`) part. In each level file, you
can define which tab is open when the level is loaded by adding `LemmaTab "Pow"`.

There will be features added to get automatic information from mathlib!

# Running Games Locally

Install `nvm`:
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
```
then reopen bash and test with `command -v nvm` if it is available (Should print "nvm").

Now install node:
```
nvm install node
```

Clone the game (e.g. `NNG4` here):
```
git clone git@github.com:hhu-adam/NNG4.git
```

Download dependencies and build the game:
```
cd NNG4
lake update
lake build
```

Clone the game repository into a directory next to the game:
```
cd ..
git clone git@github.com:leanprover-community/lean4game.git
```
The folders `NNG4` and `lean4game` must be in the same directory!

In `lean4game`, install dependencies:
```
cd lean4game
npm install
```

If you are developing a game other than `Robo` or `NNG4`, adapt the
code at the beginning of `lean4game/server/index.mjs`:
```
const games = {
    "g/hhu-adam/robo": {
        dir: "../../../../Robo",
        queueLength: 5
    },
    "g/hhu-adam/nng4": {
        dir: "../../../../NNG4",
        queueLength: 5
    }
}
```

Run the game:
```
npm start
```

This takes a little time. Eventually, the server is available on http://localhost:3000/
and the game is available on http://localhost:3000/#/g/hhu-adam/NNG4.
