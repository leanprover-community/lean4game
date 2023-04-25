import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "Proposition"
Level 6
Title "(P → (Q → R)) → ((P → Q) → (P → R))"

open MyNat

Introduction
"
You can solve this level completely just using `intro`, `apply` and `exact`,
but if you want to argue forwards instead of backwards then don't forget
that you can do things like `have j : Q → R := f p` if `f : P → (Q → R)`
and `p : P`.
"

Statement
"If $P$ and $Q$ and $R$ are true/false statements, then
$$
(P\\implies(Q\\implies R))\\implies((P\\implies Q)\\implies(P\\implies R)).
$$"
    (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  Hint "I recommend that you start with `intro f` rather than `intro p`
  because even though the goal starts `P → ...`, the brackets mean that
  the goal is not the statement that `P` implies anything, it's the statement that
  $P\\implies (Q\\implies R)$ implies something. In fact you can save time by starting
  with `intro f h p`, which introduces three variables at once, although you'd
  better then look at your tactic state to check that you called all those new
  terms sensible things. "
  intro f
  intro h
  intro p
  Hint "
  If you try `have j : {Q} → {R} := {f} {p}`
  now then you can `apply j`.

  Alternatively you can `apply ({f} {p})` directly.

  What happens if you just try `apply {f}`?
  "
  -- TODO: This hint needs strictness to make sense
  -- Branch
  --   apply f
  --   Hint "Can you figure out what just happened? This is a little
  --   `apply` easter egg. Why is it mathematically valid?"
  --   Hint (hidden := true) "Note that there are two goals now, first you need to
  --   provide an element in ${P}$ which you did not provide before."
  have j : Q → R := f p
  apply j
  Hint (hidden := true) "Is there something you could apply? something of the form
  `_ → Q`?"
  apply h
  exact p
