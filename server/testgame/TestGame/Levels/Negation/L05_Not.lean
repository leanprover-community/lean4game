import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Contradiction"
Level 5

Title "Widerspruch"

Introduction
"
"


Statement
    (A : Prop) : A := by
  not_not


Tactics contradiction
