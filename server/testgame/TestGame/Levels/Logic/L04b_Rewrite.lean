import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Predicate"
Level 4

Title "Rewrite"

Introduction
"
Mit `rw` kann man nicht nur das Goal sondern auch andere Annahmen umschreiben:

Wenn `(h : X = Y)` ist, dann ersetzt `rw [h] at g` in der Annahme
`g` das `X` durch `Y`.
"

Statement umschreiben
"Angenommen man hat die Gleichheiten

$$
\\begin{aligned} a &= b \\\\ a + a ^ 2 &= b + 1 \\end{aligned}
$$

Zeige dass $b + b ^ 2 = b + 1$."
(a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  rw [h] at g
  assumption

Message (a : ℕ) (b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 =>
"`rw [ ... ] at g` schreibt die Annahme `g` um."

Message (a : ℕ) (b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : a + a ^ 2 = a + 1 =>
"Sackgasse. probiers doch mit `rw [h] at g` stattdessen."

Conclusion "Übrigens, mit `rw [h] at *` kann man im weiteren `h` in **allen** Annahmen und
dem Goal umschreiben."

Tactics assumption rw
