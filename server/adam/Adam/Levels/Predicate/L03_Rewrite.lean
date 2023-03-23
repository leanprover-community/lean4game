import Adam.Metadata
import Mathlib

Game "Adam"
World "Predicate"
Level 3

Title "Rewrite"

Introduction
"
**Evenine**: Mit diesem neuen Wissen, könnt ihr mir bei folgendem helfen:
"

Statement
"
$$
\\begin{aligned}
  a &= b \\\\
  a + a ^ 2 &= b + 1 \\\\
  \\vdash b + b ^ 2 = b + 1
\\end{aligned}
$$
"
(a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  Hint "**Du**: Ah da ersetzt man ja einfach `{a}` durch `{b}` in der anderen Annahme!

  **Robo**: Genau! Das machst du mit `rw [{h}] at {g}`."
  rw [h] at g
  Hint (hidden := true) "**Robo**: Schau mal durch die Annahmen."
  assumption

Conclusion "
**Robo**: Noch ein Trick: Mit `rw [h] at *` kann man im weiteren `h` in **allen** Annahmen und
dem Goal umschreiben.
"
