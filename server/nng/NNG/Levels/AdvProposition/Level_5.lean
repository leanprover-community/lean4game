import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 5
Title "Easter eggs."

open MyNat

Introduction
"
Let's try this again. Try proving it in other ways. (Note that `rcases` is temporarily disabled.)

### A trick.

Instead of using `rcases` on `h : P ↔ Q` you can just access the proofs of `P → Q` and `Q → P`
directly with `h.1` and `h.2`. So you can solve this level with

```
intro hpq hqr
constructor
intro p
apply hqr.1
…
```

### Another trick

Instead of using `rcases` on `h : P ↔ Q`, you can just `rw [h]`, and this will change all `P`s to `Q`s
in the goal. You can use this to create a much shorter proof. Note that
this is an argument for *not* running the `rcases` tactic on an iff statement;
you cannot rewrite one-way implications, but you can rewrite two-way implications.


"
-- TODO
-- ### Another trick
-- `cc` works on this sort of goal too.

Statement --iff_trans
"If $P$, $Q$ and $R$ are true/false statements, then `P ↔ Q` and `Q ↔ R` together imply `P ↔ R`.
"
    (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  Hint "Make a choice and continue either with `constructor` or `rw`.

  * if you use `constructor`, you will use `{hqr}.1, {hqr}.2, …` later.
  * if you use `rw`, you can replace all `P`s with `Q`s using `rw [{hpq}]`"
  Branch
    rw [hpq]
    Branch
      exact hqr
    rw [hqr]
    Hint "Now `rfl` can close this goal.

    TODO: Note that the current modification of `rfl` is too weak to prove this. For now, you can
    use `simp` instead (which calls the \"real\" `rfl` internally)."
    simp
  constructor
  intro p
  Hint "Now you can directly `apply {hqr}.1`"
  apply hqr.1
  apply hpq.1
  assumption
  intro r
  apply hpq.2
  apply hqr.2
  assumption

DisabledTactic rcases

Conclusion
"

"
