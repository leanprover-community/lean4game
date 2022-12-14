import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 1

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
Willkommen zum Lean-Crashkurs wo du lernst wie man mathematische Beweise vom Computer
unterstützt und verifiziert schreiben kann.

Ein Beweis besteht in Lean aus verschiedenen **Taktiken**, welche ungefähr einem
logischen Schritt entsprechen, den man auf Papier aufschreiben würde.

Rechts im **Infoview** siehst den Status des aktuellen Beweis.
Du siehst ein oder mehrere offene **Goals** (mit einem `⊢` davor), die du noch zeigen musst.
Wenn du eine Taktik hinschreibst, dann versucht Lean diesen Schritt beim
ersten offenen Goal zu machen.
Wenn der Beweis komplett ist, erscheint \"goals accomplished\".
"

Statement "Zeige $ 42 = 42 $." : 42 = 42 := by
  rfl

Message : 42 = 42 =>
"Die erste Taktik ist `rfl`, die ein Goal von der Form `A = A` beweist."

Hint : 42 = 42 =>
"Man schreibt eine Taktik pro Zeile, also gib 'rfl' ein gefolgt von ENTER."

Conclusion "Bravo!"
