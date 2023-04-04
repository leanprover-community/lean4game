import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Function"
Level 4

Title ""

Introduction
"
Ihr läuft durch verschiedenste Gänge der Bibliothek, allesamt mit Büchern entlang der Wände.

**Du**: Wenn wir wüssten, dass nur ein möglicher Weg hierhin führt, könnten wir
ausschliessen, dass wir im Kreis laufen.

Plötzlich begegnet ihr einem älteren Wesen mit Fakel. Auf die Frage antwortet es mit
"
open Set Function

Statement "" : Injective (fun (n : ℤ) ↦ n + 3) := by
  Hint "**Robo**: `Injective` ist als `∀ \{a b : U}, f a = f b → a = b`
  definiert, also kannst du mit `intro` anfangen."
  intro a b
  Branch
    intro h
    Hint "**Robot**: Jetzt musst du wohl `{h}` vereinfachen."
  Hint (hidden := true) "**Du**: Kann man das wohl vereinfachen?"
  simp

NewDefinition Injective
LemmaTab "Function"

Conclusion "**Du** Woa das war ja einfach!"
