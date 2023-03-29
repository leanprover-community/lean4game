import Adam.Metadata
import Mathlib

set_option tactic.hygienic false

Game "Adam"
World "Function"
Level 5

Title ""

Introduction
"
Sofort hackt die ältere Gestalt nach:
"
open Set Function

example (f : ℤ → ℤ) (h : StrictMono f) : Injective f := by
  apply StrictMono.injective
  assumption

-- Odd.strictMono_pow

Statement "" : Injective (fun (n : ℤ) ↦ n^3 + (n + 3)) := by
  apply StrictMono.injective
  apply StrictMono.add
  apply Odd.strictMono_pow
  trivial
  intro a b
  simp

NewDefinition Injective
NewLemma StrictMono.injective StrictMono.add Odd.strictMono_pow


Hint : Injective fun (n : ℤ) => n ^ 3 + (n + 3) =>
"**Du**: Hmm, das ist etwas schwieriger…

**Robo**: Aber ich hab einen Trick auf Lager:
Das Lemma `StrictMono.injective` sagt, dass jede strikt monotone Funktion injektive ist,
und ich habe das Gefühl Monotonie ist hier einfacher zu zeigen."

HiddenHint : Injective fun (n : ℤ) => n ^ 3 + (n + 3) =>
"**Robo**: `apply` ist wonach du suchst."

Hint : StrictMono fun (n : ℤ) => n ^ 3 + (n + 3) =>
"**Du**: Jetzt möchte ich strikte Monotonie von `n ^ 3` und `n + 3` separat zeigen,
schliesslich scheint es mir als wär das zweite wieder einfach.

**Robo**: Dafür hab ich `StrictMono.add` bereit!"

Hint : StrictMono fun (x : ℤ) => x ^ 3 =>
"**Du**: Hmm, darauf hab ich jetzt wenig Lust. Gibt's dafür auch was? Das gilt ja nur
wenn der Exponent ungerade ist.

**Robo**: Du könntest mal `Odd.strictMono_pow` versuchen…"

HiddenHint : Odd 3 =>
"**Du**: Ist das nicht ne Trivialität? Warte mal!"

Hint : StrictMono fun (x : ℤ) => x + 3 =>
"**Du**: Ha! Und dieser Teil funktioniert sicher gleich wie Injektivität vorhin!"






Hint (a b : ℤ) : a ^ 3 + (a + 3) = b ^ 3 + (b + 3) → a = b =>
"**Robo**: Ich glaube, dieser Weg ist zu steinig. Fang doch nochmals von vorne an!
"

Hint (a b : ℤ) (h : a ^ 3 + (a + 3) = b ^ 3 + (b + 3)) : a = b =>
"**Robo**: Ich glaube, dieser Weg ist zu steinig. Fang doch nochmals von vorne an!
"

Conclusion "**Du**: Danke vielmals!

Und damit lässt das Wesen mitten im Gang stehen, wo es weiter über Injektivität nachdenkt."
