import Adam.Metadata
import Mathlib

Game "Adam"
World "Function"
Level 2

Title "let"

Introduction
"
Ihr macht euch auf Richtung Bibliothek entlang kleiner Pfade zwischen verschiedenster Behausungen.

**Du**: Sag mal, ich weiss jetzt dass ich eine Funktion als `fun x ↦ x - 1` definieren kann,
aber wie kann ich der einen Namen geben?

**Robo**: Wenn jemand hier eine Funktion definiert, werden die dir
`def f (x : ℤ) : ℤ := x - 1` oder `def f : ℤ → ℤ := (fun x ↦ x - 1)` geben.

**Du**: Und das bedeutet beides das gleiche?

**Robo**: Praktisch, ja. Aber! Wenn du eine Funktion in einer Aufgabe benennen willst,
schreibst du `let f := fun (x : ℤ) ↦ x - 1`!

**Du**: Und was ist der Unterschied?

**Robo**: Deines mit `let` ist für innerhalb von einem Beweis, das andere mit `def`
ist für ausserhalb von einem Beweis. Hier, ich geb dir mal eine Aufgabe:

```
def f (x : ℤ) : ℤ := (x + 4)
```
und:
"

def f (x : ℤ) : ℤ := (x + 4)

Statement "" (x : ℤ) : ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 1 := by
  let g := fun (x : ℤ) ↦ x - 3
  use g
  simp
  unfold f
  ring

NewTactic «let»
NewLemma Function.comp_apply
LemmaTab "Function"

Hint (x : ℤ) : ∃ g, (g ∘ f) x = x + 1 =>
"**Du**: Ist `g ∘ f` Komposition von Funktionen?

**Robo**: Richtig! Das schreibt man mit `\\comp`.

  **Du** Und hier könnte ich also zuerst
`let g := fun (x : ℤ) ↦ _` definieren, anstatt direkt
`use fun (x : ℤ) ↦ _`?

**Robo**: Genau! Das ist zwar praktisch das gleiche, aber kann manchmal nützlich sein.
"

-- TODO: Make some hints work here
Hint (x : ℤ) : ((fun (x : ℤ) ↦ x - 3) ∘ f) x = x + 1 =>
"**Robo**: Manchmal must du nachhelfen und Funktionen mit `unfold f` öffnen, manchmal nicht.
Um erlich zu sein, sagt mein Programm nicht genau wann man das machen muss…"

-- TODO : Make this work
Hint (x : ℤ) (g := (fun (x : ℤ) ↦ x - 3)) : (g ∘ f) x = x + 1 =>
"**Robo**: `(g ∘ f) x` ist per Definition `g (f x)`, aber mit
`rw [Function.comp_apply]` kann man das explizit umschreiben, aber `simp` kennt das
Lemma auch."

Hint (x : ℤ) : f x - 3 = x + 1 =>
"**Robo**: Manchmal must du nachhelfen und Definitionen mit `unfold f` öffnen, mamchmal klappts
ohne.
Um erlich zu sein, sagt mein Programm nicht genau wann man das machen muss…"

-- TODO: Block simp-Lemma

Conclusion "**Du**: Dann verstehst du etwas Mathe?

**Robo**: Ich hatte ja keine Ahnung ob die generierte Aufgabe beweisbar ist…

Und damit erreicht ihr den Hügel mit der Bibliothek."
