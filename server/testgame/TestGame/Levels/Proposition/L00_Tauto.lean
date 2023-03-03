import TestGame.Metadata
import Mathlib.Tactic.Tauto

Game "TestGame"
World "Proposition"
Level 1

Title "Atomatisierung"

Introduction
"
Willkommen zum Lean-Crashkurs wo du lernst wie man mathematische Beweise vom Computer
unterstützt und verifiziert schreiben kann.

*Rechts* siehst den Status des Beweis. Unter **Main Goal** steht, was du im Moment am beweisen
bist. Falls es mehrere Subgoals gibt, werden alle weiteren darunter unter **Further Goals**
aufgelistet, diese musst du dann später auch noch zeigen.

Ein Beweis besteht aus mehreren **Taktiken**. Das sind einzelne Beweisschritte, ähnlich wie
man auf Papier argumentieren würde. Manche Taktiken können ganz konkret etwas kleines machen,
andere sind stark und lösen ganze Probleme automatisiert. Du findest die Taktiken *Links* an der
Seite.

Wenn der Beweis komplett ist, erscheint \"Level completed! 🎉\".

Als erstes ein kleiner Preview, dass Lean auch vieles automatisch kann. So gibt es eine
Taktik `tauto`, die alle wahren Aussagen der Prädikaten-Logik beweisen kann.

Dieses Beispiel würde von Hand etwas Zeit in Anspruch nehmen. Lean ist da viel schneller.

Gib also `tauto` gefolgt von Enter ⏎ ein um deinen ersten automatisierten Beweis zu führen!
"

Statement
"Zeige dass folgende Aussage wahr ist:

$$
  \\neg ((\\neg B\\textrm{ oder }\\neg C) \\textrm{ oder } (A \\Rightarrow B)) \\Rightarrow
  (\\neg A \\textrm{ oder } B) \\textrm{ und } \\neg (B \\textrm{ und } C)
$$
"
    (A B C : Prop) :
    ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

Hint (A B C : Prop): ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) =>
"Man schreibt eine Taktik pro Zeile, also gib `tauto` ein und geh mit Enter ⏎ auf eine neue Zeile."

Conclusion ""

NewTactics tauto
