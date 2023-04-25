import NNG.Metadata

Game "NNG"
World "Function"
Level 8
Title "(P → Q) → ((Q → empty) → (P → empty))"

open MyNat

Introduction
"
Level 8 is the same as level 7, except we have replaced the
set $F$ with the empty set $\\emptyset$. The same proof will work (after all, our
previous proof worked for all sets, and the empty set is a set).
"

Statement
"Whatever the sets $P$ and $Q$ are, we
make an element of $\\operatorname{Hom}(\\operatorname{Hom}(P,Q),
\\operatorname{Hom}(\\operatorname{Hom}(Q,\\emptyset),\\operatorname{Hom}(P,\\emptyset)))$."
    (P Q : Type) : (P → Q) → ((Q → Empty) → (P → Empty)) := by
  Hint (hidden := true) "Maybe start again with `intro`."
  intros f h p
  Hint "
  Note that now your job is to construct an element of the empty set!
  This on the face of it seems hard, but what is going on is that
  our hypotheses (we have an element of $P$, and functions $P\\to Q$
  and $Q\\to\\emptyset$) are themselves contradictory, so
  I guess we are doing some kind of proof by contradiction at this point? However,
  if your next line is

  ```
  apply {h}
  ```

  then all of a sudden the goal
  seems like it might be possible again. If this is confusing, note
  that the proof of the previous world worked for all sets $F$, so in particular
  it worked for the empty set, you just probably weren't really thinking about
  this case explicitly beforehand. [Technical note to constructivists: I know
  that we are not doing a proof by contradiction. But how else do you explain
  to a classical mathematician that their goal is to prove something false
  and this is OK because their hypotheses don't add up?]
  "
  apply h
  apply f
  exact p

Conclusion ""
