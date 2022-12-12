import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 10

Title "Genau dann wenn"

Introduction
"
Als nächstes will man oft ein Iff-Statement `A ↔ B` wie zwei einzelne Implikationen
`A → B` und `B → A` behandeln.

Wenn das Goal `A ↔ B` ist, kann man mit der `constructor` Taktik, dieses in die Einzelteile
`A → B` und `B → A` zerlegen.

"

Statement
    "
    Zeige dass `B ↔ C`.
    "
    (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  constructor
  assumption
  assumption


Conclusion
"
Die Taktik `constructor` heisst so, weil `↔` als \"Struktur\" definiert ist, die
aus mehreren Einzelteilen besteht: `⟨A → B, B → A⟩`. Man sagt also Lean, es soll versuchen,
ob das Goal aus solchen Einzelteilen \"konstruiert\" werden kann.
"

Tactics constructor assumption

-- TODO : `case mpr =>` ist mathematisch noch sinnvoll.
