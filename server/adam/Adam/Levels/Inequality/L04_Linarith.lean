import Adam.Metadata
import Adam.Options.MathlibPart

Game "Adam"
World "Inequality"
Level 4

Title "Linarith"

Introduction
"
**Robo**: Die Taktik kann aber noch viel mehr.

**weitere Person**: Hier, probier mal!

$$
\\begin{aligned}
  5 * y &\\le 35 - 2 * x \\\\
  2 * y &\\le x + 3
\\end{aligned}
$$
"

Statement (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
  linarith

Conclusion "**Du**: Boah, das ist schon gar nicht schlecht.

Und damit endet auch deine Erinnerung und wer weiss was du anschließend gemacht hast…"
