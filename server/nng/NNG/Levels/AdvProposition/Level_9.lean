import NNG.Metadata
import NNG.MyNat.Addition

Game "NNG"
World "AdvProposition"
Level 9
Title "`exfalso` and proof by contradiction. "

open MyNat

Introduction
"
It's certainly true that $P\\land(\\lnot P)\\implies Q$ for any propositions $P$
and $Q$, because the left hand side of the implication is false. But how do
we prove that `False` implies any proposition $Q$? A cheap way of doing it in
Lean is using the `exfalso` tactic, which changes any goal at all to `False`.
You might think this is a step backwards, but if you have a hypothesis `h : ¬ P`
then after `rw not_iff_imp_false at h,` you can `apply h,` to make progress.
Try solving this level without using `cc` or `tauto`, but using `exfalso` instead.
"

Statement --contra
"If $P$ and $Q$ are true/false statements, then
$$(P\\land(\\lnot P))\\implies Q.$$"
  (P Q : Prop) : (P ∧ ¬ P) → Q := by
  Hint "Start as usual with `intro ⟨p, np⟩`."
  Branch
    exfalso
    -- TODO: This hint needs to be strict
    -- Hint "Not so quick! Now you just threw everything away."
  intro h
  Hint "You should also call `rcases` on your assumption `{h}`."
  rcases h with ⟨p, np ⟩
  -- TODO: This hint should before the last `exact p` step again.
  Hint "Now you can call `exfalso` to throw away your goal `Q`. It will be replaced with `False` and
  which means you will have to prove a contradiction."
  Branch
    -- TODO: Would `contradiction` not be more useful to introduce than `exfalso`?
    contradiction
  exfalso
  Hint "Recall that `{np} : ¬ P` means `np : P → False`, which means you can simply `apply {np}` now.

  You can also first call `rw [Not] at {np}` to make this step more explicit."
  Branch
    rw [Not] at np
  apply np
  exact p

-- TODO: `contradiction`?
NewTactic exfalso
-- DisabledTactic cc
LemmaTab "Prop"
