import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 1

Title ""

Introduction
"
Funktionen werden in Lean mit `ℕ → ℕ` geschrieben (`\\to`), also dem gleichen
Pfeil wie Implikationen.

Eine abstrakte Funktion ist ein entsprechendes Element `(f : ℕ → ℕ)` oder `(g : ℕ → ℝ)`.
Dies sagt aber gar nichts darüber, wie `f` tatsächlich definiert ist.

Hat man eine Funktion `(f : A → B)` und ein Element `(x : A)` dann ist `f x` der
Bildpunkt in `B`. In Lean braucht man also keine Klammern um $f(x)$ zu schreiben.

Eplizite, anonyme Funktionen kann man mit dem Syntax `fun (n : ℕ) ↦ n ^ 2` definieren
(entweder `↦` (`\\map`) oder `=>` als Pfeil in der Mitte).
"

Statement
"Zeige, dass es eine Funktion $\\mathbb{N} \\to \\mathbb{Z}$ gibt, für die $f(x) < x$ gilt."
    : ∃ f : ℕ → ℤ, ∀ x, f x < x := by
  use (fun x ↦ x - 1)
  simp

Hint : ∃ f : ℕ → ℤ, ∀ x, f x < x =>
"
Benütze eine anonyme Funktion `use (fun n ↦ _)` wobei `_` durch einen Ausdruck ersetzt
werden muss, so dass die Aussage erfüllt wird.
"
