import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 1

Title "Typen"

Introduction
"
Dieses Kapitel führt ein paar Lean-spezifische Sachen ein, die du wissen solltest.

Mathematisch haben diese Sachen keinen Inhalt, aber es ist wichtig, dass du etwas
verstehst wie Lean manche Sachen macht.

Als erstes geht es um Typen.

Oft sieht man Argumente von der Form `(U : Type)` was heisst \"sei $U$ ein Typ.\"
Als Mathematiker kann man sich Typen ein bisschen wie Mengen vorstellen, in dem Sinn
dass sie die Grundlage der Mathematik bilden: Alles sind Typen.

Zum Beispiel ist `ℕ` der Typ der natürlichen Zahlen, `Prop` der Typ der logischen
Aussagen, und ein Ring ist ein Typ `(R : Type)` zusammen mit einer Instanz `[Ring R]`,
die sagt, dass auf diesem Typ eine Ringstruktur besteht.

**Achtung**: Wie du aber gleich sehen wirst sind Typen und Mengen in Lean unterschiedliche
Sachen.

Hier ein kleines Beispiel zu Typen und Instanzen:
"

Statement
""
    (R : Type) [CommRing R] (a b : R) : a + b = b + a := by
  ring

Hint (R : Type) (h : CommRing R) (a : R) (b : R) : a + b = b + a =>
"
Die Taktik `ring` funktioniert in jedem Typen,
ist aber stärker, je nach Instanz auf dem Typen.

In Mathlib sind Instanzen `[CommSemiring ℕ]`, [CommRing ℤ]`, `[Field ℚ]`, etc. definiert.
Die Taktik `ring` muss eine dieser Instanzen finden, die sagen, dass die Addition kommutative ist,
damit das Lemma `add_comm` angewendet und die Aussage bewiesen werden kann.
"
