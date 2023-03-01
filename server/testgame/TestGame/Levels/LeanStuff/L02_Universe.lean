import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 2

Title "Universen"

Introduction
"
Ein weitere Syntax, den man in Lean abundzu sieht sind Universen.

Diese sind für Mathematiker erst einmal nicht so wichtig, und es reicht zu wissen,
dass diese existieren.

Da alle Objekte in Lean einen Typ haben, kann man sich fragen, welchen Typ hat eigentlich `Type`
selber? Die Anwort darauf ist dass `Type` vom Typ `Type 1` ist und dieses wiederum vom Typ `Type 2`
usw.

Da Lemmas in Lean gerne so algemein wie möglich formuliert werden, sieht man oft `(R : Type _)`
anstatt `(R : Type)`, wobei `_` einfach ein Platzhalter für eine Zahl ist.

Alternativ kann man auch explizit Universum-Levels definieren, so sind die folgenden beiden
Aussdrücke äquivalent:

```
variable (R : Type _)

universe u
variable (R : Type u)
```

In der Praxis kann man immer ohne bedenken `Type _` verwendenen und wenn man auf
(mengentheoretische)
Probleme stösst, muss man dan eventuell die Universen spezifizieren.

*Die Normalform ist eigentlich `(R : Type _)` zu schreiben solange man kein Grund hat
das Universum einzuschränken.*
"

Statement
""
    (R : Type _) [CommRing R] (a b : R) : a + b = b + a := by
  ring

-- Hint (R : Type) (h : CommRing R) (a : R) (b : R) : a + b = b + a =>
-- ""
