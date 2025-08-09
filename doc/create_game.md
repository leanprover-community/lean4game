# Creating a new game

This tutorial walks you through creating a new game for lean4. It covers from writing new levels, over testing the game locally, to publishing the game online.

## 1. Create the project

1. Use the [GameSkeleton template](https://github.com/hhu-adam/GameSkeleton) to create a new github repo for your game: On github, click on "Use this template" > "Create a new repository".
2. Clone the game repo.
3. Call `lake update -R && lake build` to build the Lean project.

### Running the game

Now you can open the game in VSCode (`cd YourGame/` and `code .`), and start modifying it like a regular Lean project. To run the game consult the section "**5. Testing the Game Locally**" below.

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
import GameServer

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
import GameServer

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

Now you created a world with one level and added it🎉 The command `MakeGame` in `Game.lean` shows you any problems you might need to fix. Currently, it shows

```text
No world introducing sorry, but required by MyWorld
```

which means that the world `MyWorld` uses the tactic `sorry` in a proof, but `sorry` has not been
introduced anywhere.

## 5. Refactoring an existing world

The [GameSkeleton template](https://github.com/hhu-adam/GameSkeleton)  contains a bash script `sofi.sh`
(`s`ort `o`ut `f`ilnames and `i`mports),
which can help restructure existing worlds, for example if you want to reorder or rename existing levels,
or add additional levels in the middle.  Say, for example, you have an “Arithmetic World” in the
folder

    Game/Levels/Arithmetic

consisting of the three levels listed in the leftmost column of the table below. Suppose you want to
switch the order of multiplication and addition, and insert an additional level on subtraction in
between.  Then you can simply edit the *file names* as in the second column, and add the additional
file for the level on substraction, so that the files are in the intended order when sorted
alphabetically (as displayed in the third column).

| existing levels    | manual changes           | files in alphabetical order | end result          |
|--------------------|--------------------------|-----------------------------|---------------------|
| L01\_hello.lean    | L01\_hello.lean          | L01\_hello.lean             | L01\_hello.lean     |
| L02\_multiply.lean | **L03**\_multiply.lean   | L02a\_add.lean              | L02\_add.lean       |
| L03\_add.lean      | **L02a**\_add.lean       | L02b\_substract.lean        | L03\_substract.lean |
|                    | **L02b\_substract.lean** | L03\_multiply.lean          | L04\_multiply.lean  |

Calling

    ./sofi.sh Game/Levels/Arithmetic

will then

- rename the files as in the last column,
- update the level number in each file,
- make a reasonable attempt to update the `import` statements in each of the
  level files, and
- update the imports in the base file `Game/Levels/Arithmetic.lean`.

More details are documented in the script itself.

Don't forget to add all your new/renamed files to git with

    git add Game/Levels/Arithmetic/

at the end.


## 6. Testing the Game Locally

Now it's time to test the game locally and play it.

There are multiple ways how you can start the game locally to test-play it described at [How to Run the Game Locally](running_locally.md). If you have problems getting one of the setups to work, please get in contact!


## 7. Dive into Level creation

Now that you have a running game, we have a closer look at the level files and all the options
you have to design your game.

### 8. a) Inventory

The player has an inventory with tactics, theorems, and definitions that unlock during the game. You can unlock/introduce such items in a Level by adding one of the following below the `Statement`.

```lean
NewTactic induction simp
NewTheorem Nat.zero_mul
NewDefinition Pow
```

**Important:** All commands in this section 6a) expect the `Name` they take as input
to be **fully qualified**. For example `NewTheorem Nat.zero_mul` and not `NewTheorem zero_mul`.

#### Doc entries

You'll see a warning about a missing Theorem documentation. You can fix it by adding doc-entries like the following somewhere above it.

```lean
/--
some description
-/
TheoremDoc Nat.zero_mul as "zero_mul" in "Mul"

/--
some description
-/
TacticDoc simp

/--
some description
-/
DefinitionDoc Pow as "^"
```

(e.g. you could also create a file `Game/Doc/MyTheorems.lean`, add there your documentation and import it)

If you do not provide any content for the inventory, the game will try to find a docstring of that item and display that docstring.

#### Inventory management

You have a few options to disable inventory items that have been unlocked in previous levels:

```lean
DisabledTactic, DisabledTheorem, OnlyTactic, OnlyTheorem
```

have the same syntax as above. The former two disable items for this level, the latter two
disable all items except the ones specified.

#### Theorem Tab

Theorems are sorted into tabs. With `TheoremTab "Mul"` you specify which tab should be open by default in this level.

#### HiddenTactic

`NewHiddenTactic` lets you add a tactic without adding it to the inventory. This can be useful for variants of tactics. E.g. you could do

```lean
NewTactic rw
NewHiddenTactic rewrite nth_rewrite rwa
```

and only `rw` would show up in the inventory.

### 6. b) Statement

The statement is the exercise of the level. The basics work the same as they would in `example` or `theorem`. Note however, that you **must** do a tactic proof, i.e. the `:= by` is a hard-coded part of the syntax

#### Name

You can give your exercise a name: `Statement my_first_exercise (n : Nat) …`. If you do so, it will be added to the inventory and be available in future levels.
You can but a `Statement` inside namespaces like you would with `theorem`.

#### Doc String / Exercise statement

Add a docstring that contains the exercise statement in natural language. If you do this, it will appear at the top of the exercise. See [LaTeX in Games](latex.md) for more details on formatting.

```lean
/-- The exercise statement in natural language using latex: $\iff$. -/
Statement ...
  sorry
```

For more details and features, read [Writing Exercises](writing_exercises.md)

### 6. c) Proof

The proof must always be a tactic proof, i.e. `:= by` is a mandatory part of the syntax.

There are a few extra tactics that help you with structuring the proof:

- `Hint`: You can use `Hint "text"` to display text if the goal state in-game matches
  the one where `Hint` is placed. For more options about hints, see below.
- `Branch`: In the proof you can add a `Branch` that runs an alternative tactic sequence, which
  helps to set `Hints` in different places. The `Branch` does not affect the main
  proof and does not need to finish any goals.
- `Template`/`Hole`: Used to provide a sample proof template. Anything inside `Template`
  will be copied into the editor with all `Hole`s replaced with `sorry`. Note that
  having a `Template` will force the user to use Editor-mode for this level.

One thing to keep in mind is that the game will look at the main proof to figure out which tactics and theorems are needed, but it ignores any `Branch`es.

### 6. d) Hints

Most important for game development are probably the `Hints`.

The hints will be displayed whenever the player's current goal matches the goal the hint is
placed at inside the sample proof. You can use `Branch` to place hints in dead ends or alternative proof strands.

Read [More about Hints](hints.md) for how they work and what the options are.

### 6. e) Extra: Images
You can add images on any layer of the game (i.e. game/world/level). These will be displayed in your game.

The images need to be placed in `images/` and you need to add a command like `Image "images/path/to/myWorldImage.png"`
in one of the files you created in 2), 3), or 4) (i.e. game/world/level).

NOTE: At present, only the images for a world are displayed. They appear in the introduction of the world.

## 7. Update your game

In principle, it is as simple as modifying `lean-toolchain` to update your game to a new Lean version. However, you should read about the details in [Update An Existing Game](update_game.md).

## 8. Add translation

See [Translating a game](translate.md).

## 9. Publish your game

To publish your game on the official server, see [Publishing a game](publish_game.md)

There are a few more options you can add in `Game.lean` before the `MakeGame` command, which describe the tile that is visible on the server's landing page:

```lean
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
Prerequisites "NNG"
CoverImage "images/cover.png"
```
* `Languages`: Currently only a single language (capital English name). The tile will show a corresponding flag.
* `CaptionShort`: One catchphrase. Appears above the image.
* `CaptionLong`: 2-4 sentences to describe the game.
* `Prerequisites` a list of other games you should play before this one, e.g. `Prerequisites "NNG" "STG"`. The game names are free-text.
* `CoverImage`: You can create a folder `images/` and put images there for the game to use. The maximal ratio is ca. 500x200 (W x H) but it might be cropped horizontally on narrow screens.

## 10. Advanced Topics

### Escaping

Inside strings, you need to escape backslashes, but not inside doc-strings, therefore you
  would write `Introduction "some latex here: $\\iff$."` but
  `/-- some latex here: $\iff$. -/ Statement ...`

### LaTeX support

LaTeX is rendered using the [KaTeX library](https://katex.org/),
see [Using LaTeX in the Game](latex.md) for details.

### Number Of Levels Limit

A world with more than 16 levels will be displayed with the levels spiraling outwards,
it might be desirable to stay below that bound. Above 22 levels the spiral starts getting out
of control.
