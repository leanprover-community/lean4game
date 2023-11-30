# Creating a new game

This tutorial walks you through creating a new game for lean4. It covers from writing new levels, over testing the game locally, to publishing the game online.

## 1. Create the project

1. Use the [GameSkeleton template](https://github.com/hhu-adam/GameSkeleton) to create a new github repo for your game: On github, click on "Use this template" > "Create a new repository".
2. Clone the game repo.
3. Call `lake update && lake exe cache get && lake build` to build the Lean project.

Note that you need to host your game's code on github to publish it online later on. If you only
want to play it locally, you can simply clone the NNG repo and start modifying that one.


## 2. Game.lean

The file `Game.lean` is the backbone of the game putting everything together.

1. `MakeGame`: This command is where the game gets built. If there are things to fix, they will be shown here as warnings or errors (orange/red squigglies in VSCode). Note that you might have to call "Lean: Restart File" (Ctrl+Shift+X) to reload the file and see changes made in other files.
1. `Title`: Set the display title of your game.
1. `Introduction`: This is the text displayed at the beginning next to the world selection tree.
1. `Info`: This will be displayed in the game's menu as "Game Info". Use it for credits, funding and other meta information about the game.
1. Imports: The file needs to import all world files, which we look at in a second. If you add a new world, remember to import it here!
1. `Dependency`: (optional) This command adds another edge in the world tree. The game computes them automatically based on used tactics/theorems. However, sometimes you need a dependency the game can't compute, for example you explained `≠` in one world and in another world, the user is expected to know it already. The syntax is `Dependency World₁ → World₂ → World₃`.

So the `Game.lean` has the following structure:

```lean
import GameServer.Commands

-- import all worlds
import Game.Levels.Tutorial

Title "My Game"

Introduction "
Hi, nice you're here! Click on a world to start.
"

Info "
This game has been developed by me.
"

-- Dependency World₁ → World₂ -- because of `≠`

MakeGame
```

## 3. Creating a Level

In this tutorial we first learn about Levels. A game consists of a tree of worlds, each world has
a number of levels, enumerated 1 to n. Here we create level 1 of a world `MyWorld`. We add this world to the game in the next section.

A minimal level file looks like the following. There are many options to add, which we will dive
into in a later section

```lean
import GameServer.Commands

World "MyWorld"
Level 1
Title "Hello World"

Introduction "
A message shown at the beginning of the level. Use it to explain any new concepts.
"

/-- The exercise statement in natural language using latex: $\iff$. -/
Statement (n : Nat) : 0 + n = n := by
  sorry

Conclusion "
The message shown when the level is completed
"
```

1. Create a folder `Game/Levels/MyWorld`
1. Create a file `Game/Levels/MyWorld/L01_hello.lean`
1. Copy the above inside your first level.

## 4. Creating a World

Now we create a world. For that we create a file `MyWorld.lean` that imports all levels of this world:

```lean
import Game.Levels.MyWorld.L01_hello

World "MyWorld"
Title "My First World"

Introduction
"
This introduction text is shown when one first enters a world.
"
```

1. Create a file `Game/Levels/MyWorld.lean`
1. Use the template above and make sure you import all levels of this world.
1. In `Game.lean` import the world with `import Game.Levels.MyWorld`

Now you created a world with one level and added it🎉 The command `MakeGame` in `Game.lean` shows you any problems you might need to fix. Currently it shows

```text
No world introducing sorry, but required by MyWorld
```

which means that the world `MyWorld` uses the tactic `sorry` in a proof, but `sorry` has not been
introduced anywhere.

## 5. Testing the Game Locally

Now it's time to test the game locally and play it.

There are multiple ways how you can start the game locally to test-play it described at [How to Run the Game Locally](running_locally.md). If you have problems getting one of the setups to work, please get in contact!


## 6. Dive into Level creation

Now that you have a running game, we have a closer look at the level files and all the options
you have to design your game.

### 6. a) Inventory

The player has an inventory with tactics, theorems, and definitions that unlock during the game. You can unlock/introduce such items in a Level by adding one of the following below the `Statement`.

```lean
NewTactic induction simp
NewLemma Nat.zero_mul
NewDefinition Pow
```

#### Doc entries

You'll see a warning about a missing Lemma documentation. You can fix it by adding doc-entries like the following somewhere above it.

```lean
LemmaDoc Nat.zero_mul as "zero_mul" in "Mul"
"some description"

TacticDoc simp
"some description"

DefinitionDoc Pow as "^"
"some description"
```

(e.g. you could also create a file `Game/Doc/MyTheorems.lean`, add there your documentation and import it)

If you do not provide any content for the inventory, the game will try to find a docstring of that item and display that docstring.

#### Inventory management

You have a few options to disable inventory items that have been unlocked in previous levels:

```lean
DisableTactic, DisableLemma, OnlyTactic, OnlyLemma
```

have the same syntax as above. The former two disable items for this level, the latter two
disable all items except the ones specified.

#### Theorem Tab

Theorems are sorted into tabs. with `LemmaTab "Mul"` you specify which tab should be open by default in this level.

#### HiddenTactic

`NewHiddenTactic` lets you add a tactic without adding it to the inventory. This can be useful for variants of tactics. E.g. you could do

```lean
NewTactic rw
NewHiddenTactic rewrite nth_rewrite rwa
```

and only `rw` would show up in the inventory.

### 6. b) Statement

The statement is the exercise of the level. the basics work the same as they would in `example` or `theorem`. Note however, that you **must** do a tactic proof, i.e. the `:= by` is a hard-coded part of the syntax

#### Name

You can give your exercise a name: `Statement my_first_exercise (n : Nat) ...`. If you do so, it will be added to the inventory and be available in future levels.

#### Doc String / Exercise statement

Add a docstring that contains the exercise statement in natural language. If you do this, it will appear at the top of the exercise. It supports Latex.

```lean
/-- The exercise statement in natural language using latex: $\iff$. -/
Statement ...
  sorry
```

#### Attributes

You can add attributes as you would for a `theorem`. Most notably, you can make your named exercise a `simp` lemma:

```lean
@[simp]
Statement my_simp_lemma ...
```

### 6. c) Proof

The proof must always be a tactic proof, i.e. `:= by` is a mandatory part of the syntax.

There are a few extra tactics that help you structuring the proof:

- `Hint`: You can use `Hint "text"` to display text if the goal state in-game matches
  the one where `Hint` is placed. For more options about hints, see below.
- `Branch`: In the proof you can add a `Branch` that runs an alternative tactic sequence, which
  helps setting `Hints` in different places. The `Branch` does not affect the main
  proof and does not need to finish any goals.
- `Template`/`Hole`: Used to provide a sample proof template. Anything inside `Template`
  will be copied into the editor with all `Hole`s replaced with `sorry`. Note that
  having a `Template` will force the user to use Editor-mode for this level.

One thing to keep in mind is that the game will look at the main proof to figure out which tactics and theorems are needed, but it ignores any `Branch`es.

### 6. d) Hints

Most important for game development are probably the `Hints`.

The hints will be displayed whenever the player's current goal matches the goal the hint is
placed at inside the sample proof. You can use `Branch` to place hints in dead ends or alternative proof strands. If you specify

```
Hint (strict := true) "some hidden hint"
```

a hint only matches iff the assumptions match exactly one-to-one. (Otherwise, it does not care if there are additional assumptions in context)

Further, you can choose to hide hints and only have them displayed when the player presses "More Help":
```
Hint (hidden := true) "some hidden hint"
```

Lastly, you should put variable names in hints inside brackets:

```
Hint "now use `rw [{h}]` to use your assumption {h}."
```
That way, the game will replace it with the actual name the assumption has in the player's proof state.

## 7. Update your game

In principle, it is as simple as modifying `lean-toolchain` to update your game to a new Lean version. However, you should read about the details in [Update An Existing Game](doc/update_game.md).

## 8. Publish your game

To publish your game on the official server, see [Publishing a game](doc/publish_game.md)

## Further Notes

Here are some random further things you should consider designing a new game:

* Inside strings, you need to escape backslashes, but not inside doc-strings, therefore you
  would write `Introduction "some latex here: $\\iff$."` but
  `/-- some latex here: $\iff$. -/ Statement ...`
* A world with more than 16 levels will be displayed with the levels spiraling outwards,
  it might be desirable to stay below that bound. Above 22 levels the spiral starts getting out
  of control.
