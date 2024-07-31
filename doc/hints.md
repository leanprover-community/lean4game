# Hints

Most important for game development are probably the "Hints". You can add Hints at any place in your proof using the `Hint` tactic

```
Statement .... := by
  Hint "Hint to show at the start"
  rw [h]
  Hint "some tip after using rw"
  ...
```

Note that hints are only **context-aware but not history-aware**. In particular, they only look at the assumptions and the current goal. Player's might encounter hints in a different order - or not at all - if they decide to go for a unique proof idea. The `Branch` tactic helps to place hints outside the sample solution's proof.

## 1. When do hints show?

A hint will be displayed if the player's goal matches the one where the hint was placed in the
sample solutions and the entire context from the sample solutions is present in the
player's context. The player's context may contain additional items.

This means if you have multiple identical
subgoals, you should only place a single hint in one of them, and it will be displayed in
all of them.

However, identical (non-hidden) hints which where already present in the step
before are omitted. This is to allow a player to add new assumptions to context, for example
with `have`, without seeing the same hint over and over again.
Hidden hints are not filtered.

## 2. Alternative Proofs / `Branch`

You can use `Branch` to place hints
in dead ends or alternative proof strands.

A proof inside a `Branch`-block is normally evaluated by lean, but it's discarded at the end
so that no progress has been made on proving the goal.

```
Statement .... := by
  Hint "use `rw` or `rewrite`."
  Branch
    rewrite [h]
    Hint "now you still need `rfl`"
  rw [h]
```

## 3. Variables names

Put variables in the hint text inside brackets like this: `{h}`! This way the server can replace
the variable's name with the one the user actually used.

*Note*: This means you need to escape any other uses of **opening** curly brackets (i.e. `\{`). See also [LaTeX in Games](latex.md) for
examples of this.

For example, if the sample proof contains

```
have h : True := trivial
Hint "Now use `rw [{h}]` to use your assumption `{h}`."
```

but the player writes `have g : True := trivial`, they will see a hint saying
"Now use `rw [g]` to use your assumption `g`."

## 4. Hidden hints

Some hints can be hidden, and only show after the user clicks on a button to get additional
help. You mark a hint as hidden with `(hidden := true)`:

```
Hint (hidden := true) "some hidden hint"
```

## 5. Strict context matching

If you use the attribute `(strict := true)` a hint is only shown if the entire context
matches exactly the one where the hint is placed. With `(hint := false)`, which is the default,
it does not matter if additional assumptions are present in the player's context.

```
Hint (strict := true) "now use `have` to create a new assumption."
```

You should probably use `(strict := true)` if you want to give fine-grained details about
tactics like `have` which do not modify the goal or any existing assumptions, but only
create new assumptions.

## 6. Formatting

You can use Markdown to format your hints and you can
use LaTeX. See [LaTeX in Games](latex.md) for more details.

### Images

Hints and introductions/conclusions can also contain images.

For remote images, simply add:

```
<img src=\"https://url.com/to/image\"/>
```

Local images can currently only be included with a hack:

Images in the game's `images/` folder will be accessible at `data/g/[user]/[repo]/[image].[png|jpg|…]` and thus can be included as if they were external images.
