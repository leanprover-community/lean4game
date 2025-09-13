import GameServer.Tactic.LetIntros

set_option linter.unusedVariables false in

example (f : Nat) :
    let f := fun x ↦ x + 1
    let g : Nat → Nat := fun y ↦ y
    ∀ x : Nat, x ≤ f x := by
  let_intros
  /-
  f✝ : Nat
  f : Nat → Nat := fun x => x + 1
  g : Nat → Nat := fun y => y
  ⊢ ∀ (x : Nat), x ≤ f x
  -/
  intro x
  exact Nat.le_succ x
