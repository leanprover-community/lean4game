import TestGame.Metadata

Game "Introduction"
World "Tactic"
Level 3

Title "Annahmen"

Introduction
"
Um Aussagen zu formulieren braucht man Annahmen. Zum einen sind das Objekte, von denen
eine Aussage handelt, wie zum Beispiel \"sei `n` eine natürliche Zahl\", oder
\"seien `A`, `B` logische Aussagen\", zum anderen sind dass Annahmen wie \"angenommen
dass `n` nicht Null ist\" oder \"angenommen `A` ist wahr\".

In Lean schreibt man beides mit der gleichen Notation: `(n : ℕ)` ist eine natürliche Zahl,
`(A B : Prop)` sind Aussagen, `(h : n ≠ 0)` ist eine Annahme, dass `n` nicht Null ist, und
`(hA : A)` ist die Annahme, dass `A` wahr ist (`hA` ist ein Beweis von `A`).

Die Annahmen kommen dann vor den Doppelpunkt.

Wenn eine Annahme `h` genau dem Goal entspricht, kannst du `exact h` verwenden.
"

Statement theorem not_or (n : ℕ) (h : n = 0) : n = 0 := by
  assumption

-- TODO: In Lean3 hatten wir ein Lemma-Text. Können wir den wieder haben?

-- TODO: Macht es Sinn mehrere Aufgaben auf einer Seite zu haben?
Statement (A : Prop) (hA : A) : A := by
  assumption

@[description "halli hallo"]
Statement instance hallo : Hallo Nat where
  mul_eq_add := by
    $editor {
    rfl
    rw }
  add_comm := by
    rfl
    apply

Statement "halli hallo" instance hallo : Hallo Nat where
  mul_eq_add := by
    $editor {
    rfl
    rw }
  add_comm := by
    rfl
    apply



Conclusion ""

Tactics assumption
