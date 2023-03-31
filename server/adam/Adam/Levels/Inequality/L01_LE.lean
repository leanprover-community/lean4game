import Adam.Metadata

Game "Adam"
World "Inequality"
Level 1

Title "Kleinergleich"

Introduction
"
*(Gespräch)*

**Robo** (*lallend*, oder war's fröhlich proklamierend?):
…und deshalb sind `≥` und `>` eigentlich nur Notationen für `≤`,
welches man übrigens `\\le` schreibt, was für Less-Equal (also Kleinergleich) steht…

**Du**: Wir haben's verstanden, man benützt also Standartmässig lieber `≤` und `<`,
aber damit weiß ich eh nichts anzufangen.

**dritte Person**: Komm schon, das kannst du ja sicher:
"

Statement
  (n m : ℕ) : m < n ↔ m.succ ≤ n := by
  Hint "**Robo**: Du Narr! Das ist doch eine Kuriosität, dass `m < n` auf `ℕ` per Definition
  als `m + 1 ≤ n` definiert ist!

  **dritte Person**: Du verdirbst den Witz! Ich wollte ihn doch nur testen."
  rfl

OnlyTactic rfl

Conclusion "**Du**: Ha. ha… Na aber jetzt mal ehrlich, könnt ihr mir ein bisschen mehr
erzählen?"
