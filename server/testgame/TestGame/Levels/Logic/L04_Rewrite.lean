import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Predicate"
Level 3

Title "Rewrite"

Introduction
"
Oft sind aber die Annahmen nicht genau das, was man zeigen will, sondern man braucht
mehrere Schritte im Beweis.

Wenn man eine Annahme `(h : X = Y)` hat,
kann die Taktik `rw [h]` im Goal $X$ durch $Y$ ersetzen.
(`rw` steht für *rewrite*)
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

Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c =>
"Die kleinen Zahlen `h₁ h₂ h₃` werden in Lean oft verwendet und man tippt diese mit
`\\1`, `\\2`, `\\3`, …"

Hint (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c =>
"Im Goal kommt `c` vor und `h₁` sagt `c = d`.
Probiers doch mit `rw [h₁]`."

Message (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = d =>
" Man kann auch rückwärts umschreiben: `h₂` sagt `a = b` mit
`rw [←h₂]` ersetzt man im Goal `b` durch `a` (`\\l`, also ein kleines L)"

Hint (a : ℕ) (b : ℕ) (h : a = b) : a = b =>
"Schau mal durch die Annahmen durch."

Conclusion "Übrigens, mit `rw [h₁, ←h₂]` könnte man mehrere `rw` zusammenfassen."

Tactics assumption rw
