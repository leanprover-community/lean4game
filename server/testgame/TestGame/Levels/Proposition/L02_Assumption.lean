import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 3

Title "Annahmen"

Introduction
"
Während der erste Untertan noch rfl, rfl, rfl murmelt, tritt schon der nächste nach vorne. Es ist schüchtern und schreibt bloß.  
"

Statement
    (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) (h₃ : n ≠ 5) : 1 < n := by
  assumption

Hint
"
**Robo** `n : ℕ` bedeutet, `n` ist eine natürliche Zahl.

**Du** Warum schreibt er dann nicht `n ∈ ℕ`??

**Robo** Weil das hier alles komische Typen sind …  Ich kann Dir das später mal in Ruhe erklären.  Jetzt will ich erst einmal die Frage entschlüsseln.  

**Robo** Also, `h₁`, `h₂`, `h₃` sind einfach nur Namen für verschiedene Annahmen, und zwar für die Annahme `n < 10`, `1 < n` und `n ≠ 5`. Beweisen sollen wir:  `1 < n`.

**Du** Aber das war doch gerade eine der Annahmen.

**Robo** Ja, stimmt.

**Du** ???

**Robo** Du musst ihm das halt explizit sagen.  Probiers mal mit `assumption`.
"


Conclusion 
"
**Untertan** Ja richtig! Wenn Ihr nur wüsstet, was ich mir an dieser Frage schon den Kopf zerbrochen habe!
"

NewTactics assumption
DisabledTactics tauto
