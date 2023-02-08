import TestGame.Metadata
import Mathlib

Game "TestGame"
World "TestWorld"
Level 1

Title "Annahmen"

Introduction "yadaa yadaa"

class MyClass (n : ℕ) where

Statement name
"Beweise dieses Lemma."
(n m : ℕ) : CommSemigroup ℕ where
  mul := fun i j => 0
  mul_comm := sorry
  mul_assoc := sorry

--@[exercise]
instance instTest (n m : ℕ) : CommSemigroup ℕ where
  mul := fun i j => 0
  mul_comm := by
    sorry
  mul_assoc := by
    sorry

--@[exercise]
lemma asdf (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rewrite [h₁]
  rw [←h₂]
  assumption


Conclusion ""

NewTactics assumption
