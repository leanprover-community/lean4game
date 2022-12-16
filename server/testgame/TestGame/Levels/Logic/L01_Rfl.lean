import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 1

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
Willkommen zum Lean-Crashkurs wo du lernst wie man mathematische Beweise vom Computer
unterstützt und verifiziert schreiben kann.

*Rechts* siehst den Status des Beweis. Unter **Main Goal** steht, was du im Moment am Beweisen
bist. Falls es mehrere Subgoals gibt, werden alle weiteren darunter unter **Further Goals**
aufgelistet, diese musst du dann später auch noch zeigen.

Ein Beweis besteht aus mehreren **Taktiken**. Das sind einzelne Beweisschritte, ähnlich wie
man auf Papier argumentieren würde. Manche Taktiken können ganz konkret etwas kleines machen,
andere sind stark und lösen ganze Probleme automatisiert. Du findest die Taktiken *Links* an der
Seite.

Wenn der Beweis komplett ist, erscheint \"Level Completed! 🎉\".

Deine erste Taktik ist `rfl`, welche dazu da ist, ein Goal der Form $X = X$ zu schliessen.
Gib die Taktik ein gefolgt von Enter ⏎.
"

Statement "Zeige $ 42 = 42 $." : 42 = 42 := by
  rfl

Message : 42 = 42 =>
"Die Taktik `rfl` beweist ein Goal der Form `X = X`."

Hint : 42 = 42 =>
"Man schreibt eine Taktik pro Zeile, also gib `rfl` ein und geh mit Enter ⏎ auf eine neue Zeile."

Conclusion "Bravo!"

Tactics rfl
