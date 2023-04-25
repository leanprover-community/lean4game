import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 8
Title "(P → Q) → (¬ Q → ¬ P)"

open MyNat

Introduction
"
There is a false proposition `False`, with no proof. It is
easy to check that $\\lnot Q$ is equivalent to $Q\\implies {\\tt False}$.

In lean, this is true *by definition*, so you can view and treat `¬A` as an implication
`A → False`.
"

Statement
"If $P$ and $Q$ are propositions, and $P\\implies Q$, then
$\\lnot Q\\implies \\lnot P$. "
    (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  Hint "However, if you would like to *see* `¬ Q` as `Q → False` because it makes you help
  understanding, you can call

  ```
  repeat rw [Not]
  ```

  to get rid of the two occurences of `¬`. (`Not` is the name of `¬`)

  I'm sure you can take it from there."
  Branch
    repeat rw [Not]
    Hint "Note that this did not actually change anything internally. Once you're done, you
    could delete the `rw [Not]` and your proof would still work."
    intro f
    intro h
    intro p
    -- TODO: It is somewhat cumbersome to have these hints several times.
    -- defeq option in hints would help
    Hint "Now you have to prove `False`. I guess that means you must be proving something by
    contradiction. Or are you?"
    Hint (hidden := true) "If you `apply {h}` the `False` magically dissappears again. Can you make
    mathematical sense of these two steps?"
    apply h
    apply f
    exact p
  intro f
  intro h
  Hint "Note that `¬ P` should be read as `P → False`, so you can directly call `intro p` on it, even
  though it might not look like an implication."
  intro p
  Hint "Now you have to prove `False`. I guess that means you must be proving something by
  contradiction. Or are you?"
  Hint "If you're stuck, you could do `rw [Not] at {h}`. Maybe that helps."
  Branch
    rw [Not] at h
    Hint "If you `apply {h}` the `False` magically dissappears again. Can you make
    mathematical sense of these two steps?"
  apply h
  apply f
  exact p

-- TODO: It this the right place? `repeat` is also introduced in `Multiplication World` so it might be
-- nice to introduce it earlier on the `Function world`-branch.
NewTactic «repeat»
NewDefinition False Not

Conclusion "If you used `rw [Not]` or `rw [Not] at h` anywhere, go through your proof in
the \"Editor Mode\" and delete them all. Observe that your proof still works."