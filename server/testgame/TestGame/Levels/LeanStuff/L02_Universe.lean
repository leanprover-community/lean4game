import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 2

Title "Universen"

Introduction
"
In der Mathematik stösst man manchmal an Mengentheoretische Grenzen, und so auch in Lean.

Klassisch ist bekannt dass die \"Menge aller Mengen\" nicht existieren kann.

Falls man an diese Grenzen stösst (z.B. in der Mengenlehre oder Kategorientheorie) hat Lean
Universen bereit: `Type` ist eigentlich `Type 0` und es gibt auch `Type 1, Type 2, ...`

Deshalb sieht man oft in Lean-Code `(R : Type _)` wenn es keine mengentheoretischen
Probleme gibt (`_` ist ein Platzhalter) oder `universe u` am Anfang und dann `(R : Type u)`
falls man diese mengentheoretischen Probleme kontrollieren muss.

In der Praxis kommt man aber relativ weit, wenn man sich erst mal nicht mit Universen
beschäftigt, und lediglich weiss, dass es sowas gibt.
"

Statement
"TODO"
    (R S : Type _) [CommRing R] (a b : R) : a + b = b + a := by
  ring

Hint (R : Type _) (h : CommRing R) (a : R) (b : R) : a + b = b + a =>
"Die Taktik `ring` funktioniert in jedem Typen,
der mindestens eine Instanz `[Ring R]` hat."
