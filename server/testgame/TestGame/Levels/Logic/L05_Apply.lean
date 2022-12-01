import TestGame.Metadata

Game "TestGame"
World "TestWorld"
Level 6

Title "Implikation"

Introduction
"
Wie wir schon gesehen haben, wir eine logische Aussage als `(A : Prop)` geschrieben, und
die Annahme, dass `A` wahr ist als `(hA : A)`, also `hA` ist sozusagens ein Beweis der
Aussage `A`.

Logische Aussagen können einander implizieren. Wir kennen hauptsächlich zwei Zeichen dafür:
`A ↔ B` (`\\iff`) bedeutet \"Genau dann wenn\" und `A → B` (`\\to`) bedeutet \"`A` impliziert `B`\".

Wenn man Aussage `B` beweisen will und eine Implikationsannahme `(h : A → B)` hat, dann kann man
diese mit `apply h` anwenden.
Auf Papier würde man schreiben, \"es genügt zu zeigen, dass `A` stimmt, denn `A` impliziert `B`\".
"

Statement
    "
    Seien `A`, `B` logische Aussagen, wobei `A` wahr ist und `A` impliziert `B`.
    Zeige, dass `B` wahr ist.
    "
    (A B : Prop) (hA : A) (g : A → B) : B := by
  apply g
  assumption

Message (A : Prop) (B : Prop) (hA : A) (g : A → B) : A =>
"Nachdem du die Implikation `A → B` angewendet hast, musst du nur noch `A` zeigen,
dafür hast du bereits einen Beweis in den Annahmen."

Tactics apply
Tactics assumption
