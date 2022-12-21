import TestGame.Metadata

Game "TestGame"
World "Logic"
Level 11

Title "Genau dann wenn"

Introduction
"
Ein $A \\iff B$ besteht intern aus zwei Implikationen, $\\textrm{mp} : A \\Rightarrow B$
und $\\textrm{mpr} : B \\Rightarrow A$.

Wenn man ein `A ↔ B` zeigen will (im Goal), kann man dieses mit `constructor` in die
Einzelteile zerlegen.
"

Statement
    "Zeige dass `B ↔ C`."
    (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  constructor
  assumption
  assumption

Message (A : Prop) (B : Prop) : A ↔ B =>
"Eine Struktur wie `A ↔ B` kann man mit `constructor` zerlegen."

Hint (A : Prop) (B : Prop) (h : A → B) : A → B =>
"Such mal in den Annahmen."

Conclusion
"
Die Taktik `constructor` heisst so, weil `↔` als \"Struktur\" definiert ist, die
aus mehreren Einzelteilen besteht: `⟨A → B, B → A⟩`. Man sagt also Lean, es soll versuchen,
ob das Goal aus solchen Einzelteilen \"konstruiert\" werden kann.
"

Tactics constructor assumption

-- TODO : `case mpr =>` ist mathematisch noch sinnvoll.
