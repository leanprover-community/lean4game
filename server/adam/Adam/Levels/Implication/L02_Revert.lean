import Adam.Metadata

set_option tactic.hygienic false

Game "Adam"
World "Implication"
Level 2

Title "Revert"

Introduction
"Der Operationsleiter holt aus einem Container einen Stapel Papier hervor.  

**Operationsleiter:** Hier hat sich echt einiges angesammelt.  Wäre echt super, wenn Ihr mir noch ein bisschen helfen könntet. 

Er übergibt Euch das oberste Blatt."

Statement (A B : Prop) (ha : A) (h : A → B) : B := by
  Hint "**Operationsleiter:** Das ist von einem Kollegen.

  **Robo**:  Oh, das hab ich schon einmal irgendwo gelesen.  Warte mal … Richtig!  Das war damals, als ich Wikipedia gecrawlt habe: `Der Modus ponens ist eine schon in der antiken Logik geläufige Schlussfigur, die in vielen logischen …`

  **Du**:  Robo!  Gefragt ist ein Beweis und kein historischer Aufsatz!   Oder komme ich hier etwa mit `mopo` oder so etwas weiter?

  **Robo**:  Ok, nein, sorry.  `mopo` gibt es nicht.  Probier lieber `revert {ha}`."
  revert ha
  Hint "**Du**:  Aha.  `revert` ist qausi `intro` rückwärts.  

  **Robo:** Genau.  `intro` nimmt die Prämisse aus einer Implikation `{A} \\to {B}` im Beweisziel und macht daraus eine Annahme.  `revert` nimmt umgekehrt eine Annahme und setzt sie als Implikationsprämisse vor das Beweisziel.  Aber nun mach schon fertig."
  assumption

Conclusion "Der Operationsleiter nimmt erfreut Eure Lösung entgegen, und greift zum Telefon."

NewTactic revert
DisabledTactic tauto
