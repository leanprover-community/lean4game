import TestGame.Metadata

Game "TestGame"
World "Implication"
Level 6

Title "Genau dann wenn"

Introduction
"
Genau-dann-wenn, $A \\Leftrightarrow B$, wird als `A ↔ B` (`\\iff`) geschrieben.
`A ↔ B` ist eine Struktur (ähnlich wie das logische UND), die aus zwei Teilen besteht:

- `mp`: die Implikation $A \\Rightarrow B$.
- `mpr`: die Implikation $B \\Rightarrow A$.

Hat man ein $\\Leftrightarrow$ im Goal, nimmt man dieses ebenfalls mit der Taktik
`constructor` auseinander und zeigt dann beide Richtungen einzeln.
"

Statement
    "Zeige dass `B ↔ C`."
    (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  constructor
  assumption
  assumption

HiddenHint (A : Prop) (B : Prop) : A ↔ B =>
"Eine Struktur wie `A ↔ B` kann man mit `constructor` zerlegen."

HiddenHint (A : Prop) (B : Prop) (h : A → B) : A → B =>
"Such mal in den Annahmen."

Conclusion
"
Die Taktik `constructor` heisst so, weil `↔` als \"Struktur\" definiert ist, die
aus mehreren Einzelteilen besteht: `⟨A → B, B → A⟩`. Man sagt also Lean, es soll versuchen,
ob das Goal aus solchen Einzelteilen \"konstruiert\" werden kann.
"

NewTactics constructor assumption

-- TODO : `case mpr =>` ist mathematisch noch sinnvoll.
