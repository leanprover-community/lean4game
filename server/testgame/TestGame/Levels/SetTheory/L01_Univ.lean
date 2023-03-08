import TestGame.Metadata

import Mathlib.Init.Set
import Mathlib.Tactic.Tauto

set_option tactic.hygienic false
set_option autoImplicit false

Game "TestGame"
World "SetTheory"
Level 1

Title "Mengen"

Introduction
"
In diesem Kapitel schauen wir uns Mengen an.

Zuerst ein ganz wichtiger Punkt: Alle Mengen in Lean sind homogen. Das heisst,
alle Elemente in einer Menge haben den gleichen Typ.

Zum Beispiel `{1, 4, 6}` ist eine Menge von natürlichen Zahlen. Aber man kann keine
Menge `{(2 : ℕ), {3, 1}, \"e\", (1 : ℂ)}` definieren, da die Elemente unterschiedliche Typen haben.

Für einen Typen `{X : Type*}` definiert damit also `set X` der Type aller Mengen mit Elementen aus
`X`.  `set.univ` ist dann ganz `X` also Menge betrachtet, und es ist wichtig den Unterschied
zu kennen: `(univ : set X)` und `(X : Typ*)` haben nicht den gleichen Typ und sind damit auch nicht
austauschbar!

Um zu beweisen, dass etwas in `univ` ist, kannst du verschiedenste deiner Taktiken anwenden,
zum Beispiel `tauto`.
"

open Set

Statement mem_univ
    "4 ist ein Element der Menge aller natürlichen Zahlen." {A : Type _} (x : A) :
    x ∈ (univ : Set A) := by
  trivial
  -- tauto

NewTactic tauto trivial
