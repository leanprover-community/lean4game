import Adam.Metadata

Game "Adam"
World "Proposition"
Level 2

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
In der Zwischenzeit hat bereits sich eine lange Schlange Untertanen gebildet, die gern ihren
Fragen stellen würden. Logisinde winkt den ersten nach vorn. Er räuspert sich.

**Untertan** Warum ist $42 = 42$?

Du schaust ihn fassungslos an.
Er schreibt es Dir wieder auf.
"

Statement "" :
  42 = 42 := by
  Hint " **Robo** Ist doch klar.  Du musst ihn einfach daran erinnern,
    dass Gleichheit *reflexiv* ist. Probier mal `rfl`."
  rfl

Conclusion
"
**Untertan** Ah, richtig. Ja, Sie haben ja so recht.  Das vergesse ich immer.  Rfl, rfl, rfl …
"

NewTactic rfl
DisabledTactic tauto
