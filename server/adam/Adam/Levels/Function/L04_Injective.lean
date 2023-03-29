import Adam.Metadata
import Mathlib

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
  intro a b
  simp

NewDefinition Injective

Hint : Injective (fun (n : ℤ) ↦ n + 3) =>
"**Robo**: `Injective` ist als `∀ \{a b : U}, f a = f b → a = b`
definiert, also kannst du mit `intro` anfangen.
"

Hint (a b : ℤ) : (fun n => n + 3) a = (fun n => n + 3) b → a = b =>
"**Du**: Kann man das wohl vereinfachen?"

Hint (a b : ℤ) (hab : (fun n => n + 3) a = (fun n => n + 3) b) : a = b =>
"**Robot**: Jetzt musst du wohl `{hab}` vereinfachen."

Conclusion "**Du** Woa das war ja einfach!"
