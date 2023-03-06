import TestGame.Metadata

Game "TestGame"
World "Proposition"
Level 2

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
In der Zwischenzeit hat bereits sich eine lange Schlange Untertanen gebildet, die gern ihren Fragen stellen würden.  Logisinde winkt den ersten nach vorn.  Er räuspert sich.

**Untertan** Warum ist $42 = 42$?

Du schaust ihn fassungslos an.
Er schreibt es Dir wieder auf.
"

Statement "
**Robo** Ist doch klar.  Du musst ihn einfach daran erinnern, dass Gleichheit *reflexiv* ist.  Probier mal `rfl`.
" :
  42 = 42 := by
  rfl

Conclusion
"
**Untertan** Ah, richtig. Ja, Sie haben ja so recht.  Das vergesse ich immer.  Rfl, rfl, rfl …
"

NewTactics rfl
DisabledTactics tauto
