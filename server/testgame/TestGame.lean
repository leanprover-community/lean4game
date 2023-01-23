import TestGame.Metadata

import TestGame.Levels.Proposition
import TestGame.Levels.Implication
import TestGame.Levels.Predicate
import TestGame.Levels.Contradiction
import TestGame.Levels.Prime

import TestGame.Levels.Naturals.L31_Sum

Game "TestGame"

Title "Lean 4 game"

Introduction
"Work in progress. Hier sind die Kommentare, aufgeteilt in drei Kategorien

### Levels / Spielinhalt
Levels, die spielbar sind:

- Logic
- Contradiction

Die anderen Levels gehen noch grössere Veränderungen durch.
Kommentare zu den spielbaren Levels:

- Taktik-Beschreibungen sind nicht gemacht, aber es sollten die richtigen
Taktiken & Lemmas angezeigt werden
- Noch mehr kurze Aufgaben?
- Mehr zur Implikation `→`?
- Ringschluss (noch nicht in Lean4)
- `tauto` (noch nicht in Lean4). Am Anfang?
- `trivial`: wann einführen? Ist ja ein Mix von verschiedenen Taktiken.
- Wann führen wir `have h : f ha` ein? (ist jetzt mal in `by_contra` reingequetscht, sollte
aber eigenständig sein)
- Nicht erklärt, wann `rw` nur eines umschreibt und wann mehrere Male. Sollten wir das tun?

### Spieler-Führung

- Keine Möglichkeit zurück zu gehen
- Fehlermeldungen sind nicht besonders Benutzerfreundlich: Ganz unverständliche sammeln,
damit wir diese später modifizieren können.
- Kann man Taktiken blockieren?
- Ich (J) bin kein Fan von der Autoergänzung, da diese im Moment viel unrelevantes anbietet.
- BUG: Kann `suffices` & `have` nicht als Taktik anzeigen.
- BUG: `¬ odd n` wird als Objekt gelistet, nicht als Assumption.
- FEAT: Brauche ein `Message'` das nur aktiv ist, wenn keine zusätzlichen Annahmen vorhanden
sind.




### Benutzerinterface
Das graphische wurde noch nicht wirklich angegangen, hier sind vorallem gröbere
Ideen wie Seitenaufteilung hilfreich. Details werden dann aber später angegangen.

- Spielstand wir noch nicht gespeichert.
- Die Lean-Version der Aufgaben sieht rudimentär aus: Syntax highlighting?

"

Conclusion
"There is nothing else so far. Thanks for rescuing natural numbers!"


Path Proposition → Implication → Predicate → Contradiction
Path Predicate → Prime
Path Predicate → Nat2
