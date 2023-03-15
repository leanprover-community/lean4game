import TestGame.Metadata

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false

Game "TestGame"
World "SetTheory"
Level 2

Title "leere Menge"

Introduction
"
Ihr zieht also durch die Gegend und redet mit den Leuten. Ein Junge rennt zu euch und fragt:
"

open Set

Statement not_mem_empty "" {A : Type} (x : A) :
    x ∉ (∅ : Set A) := by
  tauto

NewLemma mem_univ

Hint (A : Type) (x : A) : x ∉ (∅ : Set A) =>
"**Du**: Kein Element ist in der leeren Menge enthalten? Das ist ja alles tautologisches Zeugs...

**Robo**: Dann behaupte das doch. (`\\empty`)"

Conclusion "Der Junge rennt weiter.

**Du**: So wird das ganze schon angenehmer."
