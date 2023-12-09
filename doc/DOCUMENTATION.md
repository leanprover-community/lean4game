**NOTE! This document is deprecated! The current documentation is [How To Create A Game](create_game.md)**

# Creating a game.

Ideally one takes the [GameSkeleton template](https://github.com/hhu-adam/GameSkeleton) to create a new game.

## Game Structure

A game consist of worlds which have multiple levels each. In the following we describe how to create a level file and how to combine these into a game.

### Level

A level file is a lean file that imports at least `import GameServer.Commands` and starts with the following Lean commands.

```lean
Game "NNG"
World "Addition"
Level 1
Title "The rfl tactic"
```

Note that the levels inside a world must have consecutive numbering starting with `1`. The `Game`
and `World` strings can be anything, see below.

#### Statement

The core of a level is the `Statement`, which is the exercise that should be proven.

```lean
/-- For all natural numbers $n$, we have $0 + n = n$. -/
@[simp]
Statement MyNat.zero_add
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

##### Proof

The proof must always be a tactic proof, i.e. `:= by` is a mandatory part of the syntax.

There are a few extra tactics that help you structuring the proof:

- `Hint`: You can use `Hint "text"` to display text if the goal state in-game matches
  the one where `Hint` is placed. For more options about hints, see below.
- `Branch`: In the proof you can add a `Branch` that runs an alternative tactic sequence, which
  helps setting `Hints` in different   places. The `Branch` does not affect the main
  proof and does not need to finish any goals.
- `Template`/`Hole`: Used to provide a sample proof template. Anything inside `Template`
  will be copied into the editor with all `Hole`s replaced with `sorry`. Note that
  having a `Template` will force the user to use Editor-mode for this level.

##### Statement Name (optional)

If you specify a name (`MyNat.zero_add`), this lemma will be available in future levels.
(Note that a future level must also import this level,
so that Lean knows about the added statement).

The name must be *fully qualified*. (TODO: is that still true? Did we implement namespaces?)

##### Doc Comment (optional)

There are three places where the documentation comment appears:

1. as doc comment when hovering over the theorem
2. as exercise description at the top of the level: ``Theorem `zero_add`: yada yada.``
3. in the inventory. This can be overwritten by using
  `LemmaDoc MyNat.zero_add "different yada yada"` as one might want to add a more detailed
  description there including examples etc.

Both latter points support Markdown (including katex).

##### Attributes (optional)

the `@[ attributes ]` prefix should work just like you know it from the `theorem` keyword.

#### Introduction/Conclusion

Optionally, you can add an `Introduction "some text"` and `Conclusion "some text"` to your level.
The introduction will be shown at the beginning, the conclusion is displayed once the level
is solved.

#### Theorems/Tactics/Definitions

Only enabled theorems/tactics/definitions (called "items" here) are available in a level.

To add a new item in a level, you can add

```lean
NewTactic rfl simp
NewLemma MyNat.add_zero MyNat.add_succ
NewDefinition Nat Pow Mul
```

Once added, items will be available in all future levels/worlds,
unless you disable them for a particular level with

```lean
DisabledTactic tauto
DisabledLemma MyNat.add_zero
```

or specify explicitly which items should be available with

```lean
OnlyTactic rw rfl apply
OnlyLemma MyNat.add_zero
```

Lastly, all items need documentation entries (which are imported in the level),
see more about that below. There is also explains the `LemmaTab` keyword.

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
Note that all levels of a world should be imported by the world file.

BUG: A level **must not** be imported in a different world's level. Instead, you have to import an entire world there: `import NNG.Levels.Addition`

### Game

The Game itself (i.e. the main file of you lake project, `NNG.lean`) should import all worlds and have the following layout, concluding with `MakeGame`:

```lean
import NNG.Levels.Addition
import NNG.Levels.Multiplication
import NNG.Levels.Power

Game "NNG"
Title "Natural Number Game"
Introduction "some text"

MakeGame
```

The game will automatically compute the order of the worlds depending on the sample proofs of the Levels (ignoring anything inside a `Branch`). You can add additional dependencies manually by adding `Dependency PowerWorld → ImpossibleWorld` before `MakeGame`.
The order of worlds influences which tactics and lemmas will be unlocked in a given level.

`MakeGame` will display warnings about things in the game that need to be fixed, like missing
documentation or if a tactic is never introduced.

### Documentation

Each tactic, theorem, or definition (all called items here) that is introduced in the game
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

## Escaping
(TODO: Move)


Inside the doc comment you don't need to escape the backslashes:

```lean
/-- $\operatorname{succ}(n)$. notation for naturals is `\N`. -/
Statement ...
```

However, inside interpolated strings (e.g. in `Hint`, `Introduction` and `Conclusion`)
you do need to escape backslashes
with `\\` and `{` with `\{`:

```lean
Hint "This code has some $\\operatorname\{succ}(n)$ math. The value of `h` is {h}.
Notation for naturals is `\\N`."
```

## Game design
Here are some things you should consider designing a new game:

* A world with more than 16 levels will be displayed with the levels spiraling outwards,
  it might be desirable to stay below that bound. Above 22 levels the spiral start getting out
  of control.

# Running Games Locally

The installation instructions are not yet tested on Mac/Windows. Comments very welcome!

## VSCode Dev Containers

1.  **Install Docker and Dev Containers** *(once)*:<br/>
    See [official instructions](https://code.visualstudio.com/docs/devcontainers/containers#_getting-started).
    Explicitly this means:
    * Install docker engine if you have not yet: [Instructions](https://docs.docker.com/engine/install/).
      I followed the "Server" instructions for linux.
    * Note that on Linux you need to add your user to the `docker` group
      ([see instructions](https://docs.docker.com/engine/install/linux-postinstall/)) and probably reboot.
    * Open the games folder in VSCode: `cd NNG4 && code .` or "Open Folder" within VSCode
    * a message appears prompting you to install the "Dev Containers" extension (by Microsoft).

2.  **Open Project in Dev Container** *(everytime)*:<br/>
    Once you have the Dev Containers Extension installed, (re)open the project folder of your game in VSCode.
    A message appears asking you to "Reopen in Container".

    * The first start will take a while, ca. 2-10 minutes. After the first
      start this should be very quickly.
    * Once built, it should open a tab "Simple Browser" inside VSCode displaying
      the game. (Alternatively, open http://localhost:3000 in your browser).

3.  **Editing Files** *(everytime)*:<br/>
    After editing some files in VSCode, open VSCode's terminal (View > Terminal) and run `lake build`.
    Now you can reload your browser to see the changes.

### Errors

* If you don't get the pop-up, you might have disabled them and you can reenable it by
  running the `remote-containers.showReopenInContainerNotificationReset` command in vscode.
* If the starting the container fails, in particular with a message `Error: network xyz not found`,
  you might have deleted stuff from docker via your shell. Try deleting the container and image
  explicitly in VSCode (left side, "Docker" icon). Then reopen vscode and let it rebuild the
  container. (this will again take some time)


## Without Dev Containers
Install `nvm`:
```bash
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
```
then reopen bash and test with `command -v nvm` if it is available (Should print "nvm").

Now install node:
```bash
nvm install node
```

Clone the game (e.g. `NNG4` here):
```bash
git clone https://github.com/hhu-adam/NNG4.git
# or: git clone git@github.com:hhu-adam/NNG4.git
```

Download dependencies and build the game:
```bash
cd NNG4
lake update
lake exe cache get   # if your game depends on mathlib
lake build
```

Clone the game repository into a directory next to the game:
```bash
cd ..
git clone https://github.com/leanprover-community/lean4game.git
# or: git clone git@github.com:leanprover-community/lean4game.git
```
The folders `NNG4` and `lean4game` must be in the same directory!

In `lean4game`, install dependencies:
```bash
cd lean4game
npm install
```

TODO: This is outdated!
If you are developing a game other than `Robo` or `NNG4`, adapt the
code at the beginning of `lean4game/relay/index.mjs`:
```typescript
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
```bash
npm start
```

This takes a little time. Eventually, the server is available on http://localhost:3000/
and the game is available on http://localhost:3000/#/g/hhu-adam/NNG4.

### Modifying the GameServer

When modifying the game engine itself (in particular the content in `lean4game/server`) you can test it live with this
setup by setting `export NODE_ENV=development` inside your local game before building it:

```bash
cd NNG4
export NODE_ENV=development
lake update
lake build
```
This causes lake to search locally for the `GameServer` lake package instead of using the version from github.
