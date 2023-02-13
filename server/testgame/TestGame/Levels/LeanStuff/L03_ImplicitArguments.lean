import TestGame.Metadata

import Mathlib

set_option tactic.hygienic false

Game "TestGame"
World "LeanStuff"
Level 3

Title "Implizite Argumente"

Introduction
"

Auch wichtiger Syntax ist der Unterschied zwischen
impliziten und expliziten Argumenten von Lemmas. **Explizite Argumente**
schreibt man mit runden Klammern `()`, **impliziete Argumente** mit geschweiften `{}`.

Als implizit werden alle Argumente markiert, die Lean selbständig aus dem Kontext
erschliessen und einfüllen kann.

Als Beispiel hier zweimal das gleiche Lemma, einmal ohne impliziten Argumenten und einmal mit
```
lemma not_or_of_imp' (A B : Prop) (h : A → B) : ¬A ∨ B := sorry

lemma not_or_of_imp {A B : Prop} (h : A → B) : ¬A ∨ B := sorry
```

Hat man nun `g : C → D` dann braucht man diese Lemmas mit
`have := not_or_of_imp g` oder `have := not_or_of_imp' C D g`.

Wie man sieht erschliesst Lean die impliziten Argumente automatisch und es wäre deshalb
unnötig, diese jedes Mal explizit angeben zu müssen.

TODO
(Trick mit `@not_or_of_imp` kann man sagen, dass man **alle** Argumente angeben möchte und mir
`not_or_of_imp g (B := D)` könnte man ein spezifisches implizites Argument spezifizieren.
Wenn man diese Tricks braucht, heisst das aber meistens, das etwas nicht optimal definiert
ist.)


Nebenbemerkung: Es gibt auch noch implizite **Klassen-Elemente** mit eckigen Klammern `[]`
wie zum Beispiel `[CommRing R]` im vorigen Beispiel. Diese werden später behandelt,
und sagen Lean, dass es für dieses Argument eine **Instanz** suchen gehen soll. Diese
Instanzen werden mehrheitlich dafür verwendet, mathematische Strukturen auf Typen zu
definieren, aber das kommt alles später.
"

Statement
"TODO"
    (R S : Type _) [CommRing R] (a b : R) : a + b = b + a := by
  ring

Hint (R : Type _) (h : CommRing R) (a : R) (b : R) : a + b = b + a =>
"Die Taktik `ring` funktioniert in jedem Typen,
der mindestens eine Instanz `[Ring R]` hat."
