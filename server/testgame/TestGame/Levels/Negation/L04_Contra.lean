import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Contradiction"
Level 4

Title "Widerspruch"

Introduction
"
"


Statement
    (A : Prop) : A := by
  by_contradiction


Tactics contradiction
