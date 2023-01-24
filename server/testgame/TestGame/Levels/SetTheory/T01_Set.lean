import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

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

Am anderen Ende sitzt die leere Menge `(∅ : set X)` (`\\empty`). Bei `univ` und `∅` versucht Lean
automatisch den Typ zu erraten, in exotischen Beispielen muss man wie oben diesen explizit angeben.

Als erste Operationen schauen wir uns `∪` (`\\union` oder `\\cup`), `∩`
(`\\inter` oder `\\cap`) und `\\` (`\\\\` oder `\\ `)

"

open Set

Statement
    "Wenn $B$ wahr ist, dann ist die Implikation $A \\Rightarrow (A ∧ B)$ wahr."
    {X : Type _} {A B : Set X} : univ \ (A ∩ B) ∪ ∅ = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  rw [Set.diff_inter]
  rw [Set.union_empty]
  rw [Set.union_assoc]
  rw [←Set.union_diff_distrib]
  rw [Set.univ_union]

Tactics rw
