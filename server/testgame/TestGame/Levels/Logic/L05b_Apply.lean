import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 7

Title "Implikation"

Introduction
"
Angenommen man hat folgende Implikationen und weiss dass Aussage `A` wahr ist.
```
A → B ← C
    ↓   ↓
D → E → F
```
Beweise Aussage `F`.
"

Statement
    "
    Seien `A`, `B` logische Aussagen, wobei `A` wahr ist und `A` impliziert `B`.
    Zeige, dass `B` wahr ist.
    "
    (A B C D E F : Prop) (hA : A) (f : A → B) (g : C → B) (h : B → E)
     (i : D → E) (k : E → F) (m : C → F) : F := by
  apply k
  apply h
  apply f
  assumption

Message  (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : C =>
"Sackgasse. Probier doch einen anderen Weg."

Message  (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : D =>
"Sackgasse. Probier doch einen anderen Weg."

Tactics apply
Tactics assumption
