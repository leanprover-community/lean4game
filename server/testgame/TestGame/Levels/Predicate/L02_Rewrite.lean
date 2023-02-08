import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Predicate"
Level 2

Title "Rewrite"

Introduction
"
Wir haben gesehen, dass man mit `rw` Äquivalenzen wie `A ↔ B` brauchen kann, um im Goal
$A$ durch $B$ zu ersetzen.

Genau gleich kann man auch Gleichungen `a = b` mit `rw` verwenden.
"

Statement umschreiben
"Angenommen man hat die Gleichheiten

$$
\\begin{aligned} a &= b \\\\ a &= d \\\\ c &= d \\end{aligned}
$$

Zeige dass $b = c$."
(a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rw [h₁]
  rw [←h₂]
  assumption

HiddenHint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c =>
"Im Goal kommt `c` vor und `h₁` sagt `c = d`.
Probiers doch mit `rw [h₁]`."

HiddenHint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : a = c =>
"Im Goal kommt `C` vor und `h₁` sagt `C ↔ D`.
Probiers doch mit `rw [h₁]`."

HiddenHint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = d =>
" Man kann auch rückwärts umschreiben: `h₂` sagt `a = b` mit
`rw [←h₂]` ersetzt man im Goal `b` durch `a` (`\\l`, also ein kleines L)"

HiddenHint (a : ℕ) (b : ℕ) (h : a = b) : a = b =>
"Schau mal durch die Annahmen durch."



-- These should not be necessary if they don't use `rw [] at`.
HiddenHint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = c) : b = c =>
"Auch eine Möglichkeit... Kannst du das Goal so umschreiben,
dass es mit einer Annahme übereinstimmt?"

HiddenHint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : b = d) : b = c =>
"Auch eine Möglichkeit.. Kannst du das Goal so umschreiben, dass es mit einer Annahme übereinstimmt?"

Hint (a : ℕ) (b : ℕ) (h : b = a) : a = b =>
"Naja auch Umwege führen ans Ziel... Wenn du das Goal zu `a = A` umschreibst, kann man es mit
`rfl` beweisen (rsp. das passiert automatisch.)"

Hint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : d = b) (h₃ : d = a) : b = c =>
"das ist nicht der optimale Weg..."

Hint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : d = b) (h₃ : a = d) : b = c =>
"das ist nicht der optimale Weg..."



Conclusion "Übrigens, mit `rw [h₁, ←h₂]` könnte man mehrere `rw` zusammenfassen."

NewTactics assumption rw
