import TestGame.Metadata

import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Algebra.Module.Pi          -- definiert `Module ℚ (fin 2 → ℚ)`
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option tactic.hygienic false

Game "TestGame"
World "Module"
Level 2

Title "Konkrete Vektorräume"

Introduction
"
Häufig in der linearen Algebra hat man ganz einfach Vektoren über `ℚ` oder `ℝ`
und möchte diese explizit definieren.

Reele Vektorräume definiert man in Lean am besten als Funktion von einem Indexset.

So ist `Fin 2` eine Menge, die nur `0` und `1` enthält
und `ℚ²` wird als `Fin 2 → ℚ` definiert. Hier machen wir uns eine
lokale notation dafür:

```
notation `ℚ²` := Fin 2 → ℚ
```

Das mag auf den ersten Blick etwas unintuitiv erscheinen, hat aber den Vorteil,
dass man die ganze
Infrastruktur für Funktionen einfach direkt für Vektoren und
Matrizen mitgebrauchen kann.

Wir können uns auch noch ein paar andere standardmässige `ℚ`-Vektorräume definieren.

```
notation \"ℚ³\" => Fin 3 → ℚ
notation \"ℚ^(\" n \")\" => (Fin n) → ℚ
```

Die schreibweise für einen Vektor ist `![ _, _ ]`. Zu beachten ist,
dass man bei Zahlen explizit einen Typ angeben muss, sonst denkt sich
Lean, man arbeite über `ℕ`.

Um direkt Vektoroperationen über `ℚ` auszurechnen, kann man oft
`#eval` benützen:

```
#eval ![ (2 : ℚ), 5 ] + ![ 1/2, -7 ]
```
zeigt `![5/2, -2]` an.

Um eine Gleichheit in einem Beweis zu verwenden, muss man andere Taktiken
benützen.

Am hilfreichsten ist die kombination `funext i, fin_cases i`, die
Dann eine Vektorgleichung komponentenweise aufteilt.

Für jede Komponente kann man dann mit `simp` und `ring` weiterkommen.
"

notation "ℚ³" => Fin 3 → ℚ
notation "ℚ^(" n ")" => (Fin n) → ℚ

Statement
""
    : ![ (2 : ℚ), 5 ] + ![ 1/2, -7 ] = ![5/2, -2] := by
  funext i
  fin_cases i <;>
  simp <;>
  ring

NewTactic fin_cases funext
