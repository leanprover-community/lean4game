import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 3

Title ""

Introduction
"
Komposition von Funktionen kann als `g ∘ f` geschrieben werden.

TODO
"

Statement
"TODO: Find an exercise."
    (U T V : Type _) (f : U → V) (g : V → T) (x : U) : (g ∘ f) x = g (f x)  := by
  simp only [Function.comp_apply]

NewLemmas Function.comp_apply
