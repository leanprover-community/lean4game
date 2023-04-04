import Adam.Metadata

import Adam.Options.MathlibPart

set_option tactic.hygienic false

Game "Adam"
World "Lean"
Level 2

Title "Universen"

Introduction
"**Du**: Aber wenn alles Typen sind, welcher Typ hat dann `Type`?

**Robo**: `Type 1` und dieser hat Typ `Type 2`, etc.

**Robo**: Die Zahl nennt man *Universum*. Manchmal führt man Universen explizit
mit `universum u` ein, öfter siehst du `(R : Type _)`, was einfach ein Platzhalter
für irgend ein Universum ist.

**Du**: Das klingt ein bisschen nach Mengentheoretische Probleme, die man normalerweise
ignoriert.

**Robo**: Genau! Deshalb schreibt man eigentlich immer einfach `Type _` und ist glücklich.
Spezifischer muss man erst werden wenn man sowas wie Kategorientheorie anschaut, wo
man die Universen tatsächlich kontrollieren muss.

**Du**: Oke, hier rein, da raus. Aber hast du mir noch eine Aufgabe?
"

universe u

Statement
    (R : Type u) [CommRing R] (a b : R) : a + b = b + a := by
  Hint "**Robo**: Naja, Aufgaben zu Universen sind nicht so natürlich,
  aber vorige Aufgabe würde man eigentlich besser so schreiben, da
  kannst du mindestens das Uniersum beobachten.

  **Du**: Ah ich sehe, `(R: Type u)` anstatt `(R : Type)`. Muss mich
  das interessieren?

  **Robo**: Nicht wirklich…"
  ring

Conclusion "**Du**: Na dann. Aber gut dass ich's mal gesehen hab."

-- Hint (R : Type) (h : CommRing R) (a : R) (b : R) : a + b = b + a =>
-- ""
