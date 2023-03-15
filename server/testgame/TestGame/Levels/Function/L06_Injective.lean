import TestGame.Metadata
import Mathlib

Game "TestGame"
World "Function"
Level 6

Title "Injektive"

Introduction
"
Weiterirrend kommt ihr an eine Verzweigung.

**Robo**: Sieht beides gleich aus.

Ein paar Schritte in den linken Korridor hinein seht ihr auf dem Boden ein Blatt mit Gekritzel:

```
def f : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1
```

**Du**: Hier haben wir wieder eine stückweise Funktion

$$
f(n) = \\begin{cases}
    n^2 & \\text{falls } n \\text{ gerade} \\\\
    n+1 & \\text{andernfalls.}
\\end{cases}
$$


Darunter steht in leicht leuchtender Schrift:
"

namespace FunctionLvl7

open Function

def f : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1

Statement "" : ¬ (f + f).Injective := by
  unfold Injective
  push_neg
  use 2
  use 3
  simp

Hint : ¬ (Injective (f + f)) =>
"
**Robo**: Das ist sicher ein Hinweis.

**Du**: Aber `¬ Injective` sagt mir nichts…

**Robo**: Könntest du etwas mit `¬ ∀` anfangen? Dann könntest du ja `Injektive` zuerst öffnen.

**Du**: Darüber haben wir doch mal was gelernt…
"

HiddenHint : ¬ (Injective (f + f)) =>
"
**Robo**: Das war `push_neg`.
"

Hint : ∃ a b, (f + f) a = (f + f) b ∧ a ≠ b =>
"**Du** Jetzt muss ich einfach ein Gegenbeispiel nennen, oder?

**Robo** Genau! Welche beiden Zahlen möchtest du denn verwenden?"

Conclusion
"
Als ihr das Problem gelöst habt, erschleicht euch ein starkes
Gefühl, dass dies der falsche Weg ist.
Also geht ihr zurück und nehmt die rechte Gabelung.
"

end FunctionLvl7
