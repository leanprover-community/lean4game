# Writing exercises

This page deals in more details with the `Statement` command and all the options you have
to write better exercises/levels.


## Local `let` definitions

If you want to make a local definition/notation which only holds for this exercise (e.g.
a function `f : ℤ → ℤ := fun x ↦ 2 * x`) the recommended way is to use a `let`-statement:

```lean
Statement (a : ℤ) (h : 0 < a) :
    let f : ℤ → ℤ := fun x ↦ 2 * x
    0 < f a := by
  sorry
```

The game automatically `intros` such `let`-statements, such that you and the player will see
the following initial proof state:

```
a: ℤ
h: 0 < a
f: ℤ → ℤ := fun x => 2 * x
⊢ 0 < f a
```

## "Preample" & non-`Prop`-valued exercises

You can use the following syntax with `(preample := tac)` where `tac` is a tactic sequence.

```
Statement my_statement (preample := dsimp) (a : ℤ) (h : 0 < a) :
    0 < f a := by
  sorry
```

This tactic sequence will be executed before the exercise is handed to the player.

For example, if your exercise is to construct a structure, you could use `preample` to fill
all data fields correctly, leaving all `Prop`-valued fields of the structure as separate goals
for the player to proof.

Note: `(preample := tac)` always has to be written between the optional name and the first
hypothesis. Nevertheless, you can use all hypotheses in the tactic sequence, because it is
only evaluated at the beginning of the proof.

## Attributes

You can add attributes as you would for a `theorem`. Most notably, you can make your named exercise a `simp` lemma:

```lean
@[simp]
Statement my_simp_lemma ...
```
