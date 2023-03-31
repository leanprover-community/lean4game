import Adam.Metadata

Game "Adam"
World "Proposition"
Level 5

Title "True/False"

Introduction
"
Der nächste Untertan in der Reihe ist ein Schelm.
"

Statement "" : True := by
  Hint "
**Robo**  Dieses `True` ist eine spezielle Aussage, nämlich die Aussage, die immer und
bedingungslos wahr ist.

**Du** Und was genau ist dann zu beweisen?

**Robo** Ich glaube, nichts. Ich glaube, du kannst einfach `trivial` schreiben.
"
  trivial

Conclusion
"
**Schelm**  Wollte nur mal sehen, dass Ihr nicht auf den Kopf gefallen seid …

**Du** *(zu Robo)*  Können wir nicht einfach immer dieses `trivial` verwenden?
Wie in einer Mathe-Vorlesung?

**Robo** Nein, das `trivial` hier hat eine ziemlich spezielle Bedeutung.
Das funktioniert nur in einer Handvoll Situationen.
"

NewTactic trivial
DisabledTactic tauto
