import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 9

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

--TODO: This is a really hard proof
Statement bijective_iff_has_inverse "" {A B : Type} (f : A → B) :
    Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f := by
  constructor
  intro h
  use fun x => (h.2 x).choose
  constructor
  · intro x
    simp
    apply h.1
    apply Exists.choose_spec (h.2 (f x))
  · intro x
    simp
    apply Exists.choose_spec (h.2 x)
  intro ⟨g, h₁, h₂⟩
  constructor
  · intro a b hab
    have h : g (f a) = g (f b)
    · apply congrArg
      assumption
    rw [h₁, h₁] at h
    assumption
  · intro x
    use g x
    rw [h₂]

NewDefinition LeftInverse RightInverse
NewLemma Exists.choose Exists.choose_spec congrArg congrFun
DisabledLemma Function.bijective_iff_has_inverse

Hint {A B : Type} (f : A → B) : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f =>
"**Du**: Nah da sagt mir so manches nichts, aber ich kann ja mal mit dem `↔` anfangen, das kenn
ich ja schon."

Conclusion
"Endlich entkommt ihr der Bibliothek.

**Robo**: Da würden mich keine zehn Pferde nochmals hineinbringen!

**Du**: Von wegen Pferden, wie viele PS hat eigentlich unser Raumschiff?"
