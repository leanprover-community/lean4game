import TestGame.Metadata

set_option tactic.hygienic false

Game "TestGame"
World "Implication"
Level 2

Title "Revert"

Introduction
"
Mit `intro` kann man also eine Implikation aus dem Goal entfernen, indem man
die Implikationsprämisse zu den *Annahmen* hinzufügt:

```
example : A → B :=
  [Beweis]
```

wird zu

```
example (ha : A) : B :=
  [Beweis]
```

Seltener kann auch die andere Richtung nützlich sein. Mit `revert ha` kann man die Annahme
`ha` entfernen und als Implikationsprämisse vor's Goal hängen.
"

Statement
"Angenommen $A$ ist eine wahre Aussage und man hat eine Implikation $A \\Rightarrow B$, zeige
dass $B$ wahr ist."
    (A B : Prop) (ha : A) (h : A → B) : B := by
  revert ha
  assumption

HiddenHint (A : Prop) (B : Prop) (ha : A) (h : A → B): B =>
"Mit `revert ha` kann man die Annahme `ha` als Implikationsprämisse vorne ans Goal anhängen."

NewTactic revert assumption
