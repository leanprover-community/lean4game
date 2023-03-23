import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "Lean"
Level 1

Title "Typen"

Introduction
"
**Du**: Also, wieso schreib ich denn sowohl `(n : ℕ)` für eine natürliche Zahl wie
auch `(h : A ∧ ¬ B)` für eine Aussage?

**Robo**: Alles in Lean sind Objekte von einem *Typen*, man nennt das auch
\"dependent type theory\". Rechts vom `:` steht immer der Typ der dieses Objekt hat.

**Du**: Verstehe, dann war `ℕ` der Typ der natürlichen Zahlen, `Prop` der Typ
aller logischen Aussagen, und so weiter. Un wenn `R` einfach irgendein Typ ist, dann…

**Robot: …würdest du das als `(R : Type)` schreiben.

**Du**: Also sind Typen ein bisschen jene Grundlage, die in meinem Studium die
Mengen eingenommen haben?

**Robo**: Genau. Ein Ring ist dann zum Beispiel als `(R : Type) [Ring R]` definiert,
also als Typen, auf dem eine Ringstruktur besteht.

**Robo**: Hier ein Beispiel. Die Taktik `ring` funktioniert in jedem Typen, der
genügend Struktur definiert hat, zum Beispiel in einem kommutativen Ring:
"

Statement (R : Type) [CommRing R] (a b : R) : a + b = b + a := by
  ring

Conclusion "**Robo**: `[CommRing R]` nennt man übrigens eine Instanz und die
eckigen Klammern sagen Lean, dass es automatisch suchen soll, ob es so eine Instanz
findet, wenn man ein Lemma anwenden will."
