import Adam.Metadata
import Mathlib

Game "Adam"
World "Function"
Level 10

Title "Inverse"

Introduction
"
Eigentlich hast du nur beiläufig Robo gefragt, ob bijektiv nicht auch bedeute, dass
eine Inverse Funktion bestehe. Jetzt steht ihr aber schon seit einer halben Stunde rum
und der Gelehrte möchte wissen, wie das den genau ginge.

Offensichtlich kennt er diese Aussage als `Function.bijective_iff_has_inverse` aus seinen Büchern,
aber er möchte, dass Du ihm das hier und jetzt nochmals von Grund auf zeigst.
"

open Function
set_option pp.rawOnError true
Statement bijective_iff_has_inverse "" {A B : Type} (f : A → B) :
    Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f := by
  Branch
    exfalso
    Hint "Das war eine blöde Idee
    dd

    ddds
    "
  Hint (hidden := true) "constructor"
  constructor
  Hint "intro h" -- does not show
  intro h
  Hint "rcases h with ⟨h₁, h₂⟩" -- shows too late: 1, 2 after
  rcases h with ⟨h₁, h₂⟩
  Hint (strict := true) "let g := fun x => (h₂ x).choose" -- shows correct + 1 after
  let g := fun x => (h₂ x).choose
  Hint "use g"
  use g
  Hint "constructor" -- does not show
  constructor
  Hint "intro x" -- does not show
  intro x
  Hint "simp" -- Error updating: Error fetching goals: Rpc error: InternalError: unknown universe metavariable '?_uniq.286465'. Try again.
  simp
  Hint "apply h₁"
  apply h₁
  Hint "apply Exists.choose_spec (h₂ (f x))"
  apply Exists.choose_spec (h₂ (f x))
  Hint "intro y" -- Error updating: Error fetching goals: Rpc error: InternalError: unknown universe metavariable '?_uniq.286465'. Try again.
  intro y
  Hint "simp"
  simp
  Hint "apply Exists.choose_spec (h₂ y)"
  apply Exists.choose_spec (h₂ y)
  Hint "intro ⟨g, h₁, h₂⟩"
  intro ⟨g, h₁, h₂⟩
  Hint "constructor"
  constructor
  Hint "intro a b hab"
  intro a b hab
  Hint (strict := true) "have h : g (f a) = g (f b)"
  have h : g (f a) = g (f b)
  Hint "apply congrArg"
  apply congrArg
  Hint "assumption"
  assumption
  Hint "rw [h₁, h₁] at h"
  rw [h₁, h₁] at h
  Hint "assumption"
  assumption
  Hint "intro x"
  intro x
  Hint "use g x"
  use g x
  Hint "rw [h₂]"
  rw [h₂]

-- NewDefinition LeftInverse RightInverse
-- NewLemma Exists.choose Exists.choose_spec congrArg congrFun
-- DisabledLemma Function.bijective_iff_has_inverse

Hint (A B: Type) (f : A → B) (h : Bijective f) :
  (∃ g, LeftInverse g f ∧ RightInverse g f) → Bijective f =>
  "Test"

Conclusion
"Endlich entkommt ihr dem Tempel.

**Robo**: Da würden mich keine zehn Pferde nochmals hineinbringen!

**Du**: Von wegen Pferden, wie viele PS hat eigentlich unser Raumschiff?"
