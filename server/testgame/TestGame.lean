import TestGame.Metadata
import TestGame.Levels.Logic.L01_Rfl
import TestGame.Levels.Logic.L02_Rfl
import TestGame.Levels.Logic.L03_Assumption
import TestGame.Levels.Logic.L03b_Assumption
import TestGame.Levels.Logic.L04_Rewrite
import TestGame.Levels.Logic.L04b_Rewrite
import TestGame.Levels.Logic.L05_Apply
import TestGame.Levels.Logic.L05b_Apply
import TestGame.Levels.Logic.L05c_Apply
import TestGame.Levels.Logic.L06_Iff
import TestGame.Levels.Logic.L06b_Iff
import TestGame.Levels.Logic.L06c_Iff
import TestGame.Levels.Logic.L06d_Iff
import TestGame.Levels.Logic.L07_And
import TestGame.Levels.Logic.L08_Or
import TestGame.Levels.Logic.L08b_Or
import TestGame.Levels.Logic.L08c_Or
import TestGame.Levels.Naturals.L01_Ring
import TestGame.Levels.Naturals.L02_Ring
import TestGame.Levels.Naturals.L03_Exists
import TestGame.Levels.Naturals.L04_Forall
import TestGame.Levels.Naturals.L31_Sum
import TestGame.Levels.Naturals.L32_Induction
import TestGame.Levels.Naturals.L33_Prime
import TestGame.Levels.Naturals.L34_ExistsUnique
import TestGame.Levels.Negation.L01_False
import TestGame.Levels.Negation.L02_Contra
import TestGame.Levels.Negation.L03_Contra
import TestGame.Levels.Negation.L04_Contra
import TestGame.Levels.Negation.L05_Not
import TestGame.Levels.Negation.L06_ByContra
import TestGame.Levels.Negation.L07_Contrapose
import TestGame.Levels.Negation.L08_Contrapose
import TestGame.Levels.Negation.L09_PushNeg

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


Path Logic → Nat → Contradiction
Path Nat → Nat2
