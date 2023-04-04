import Adam.Metadata

import Adam.Options.MathlibPart

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

open Function

def f (x : ℤ) : ℤ := (x + 4)

Statement "" (x : ℤ) : ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 1 := by
  Hint
  "**Du**: Ist `g ∘ f` Komposition von Funktionen?

  **Robo**: Richtig! Das schreibt man mit `\\comp`.

    **Du** Und hier könnte ich also zuerst
  `let g := fun (x : ℤ) ↦ _` definieren, anstatt direkt
  `use fun (x : ℤ) ↦ _`?

  **Robo**: Genau! Das ist zwar praktisch das gleiche, aber kann manchmal nützlich sein."
  Branch
    use fun (x : ℤ) ↦ x - 3
    Hint "**Robo**: `((fun (x : ℤ) ↦ x - 3) ∘ f) x` ist per Definition `(fun (x : ℤ) ↦ x - 3) (f x)`, aber mit
    `rw [comp_apply]` kann man das explizit umschreiben, aber `simp` kennt das
    Lemma auch."
  let g := fun (x : ℤ) ↦ x - 3
  Hint "**Robo**: gute Wahl! Jetzt kannst du diese mit `use g` benützen."
  use g
  Hint "**Robo**: `({g} ∘ f) x` ist per Definition `{g} (f x)`, aber mit
  `rw [comp_apply]` kann man das explizit umschreiben, aber `simp` kennt das
  Lemma auch."
  simp
  Hint "**Robo**: Wie schon gehabt hat `ring` Schwierigkeiten, Definitionen zu öffnen.
  Du kannst mit `unfold f` oder `rw [f]` nachhelfen."
  unfold f
  ring

NewTactic «let»
NewLemma Function.comp_apply
LemmaTab "Function"

Conclusion "**Du**: Dann verstehst du etwas Mathe?

**Robo**: Ich hatte ja keine Ahnung ob die generierte Aufgabe beweisbar ist… aber offenbar
hatte ich Glück.

Und damit erreicht ihr den Hügel mit der Bibliothek."
