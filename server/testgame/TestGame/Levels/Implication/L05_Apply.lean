import TestGame.Metadata

Game "TestGame"
World "Implication"
Level 5

Title "Implikation"

Introduction
"
Noch eine Übung: Angenommen man hat folgende Implikationen:
$$
\\begin{CD}
  A  @>{f}>> B       @<{g}<< C       \\\\
  @. @V{h}VV @V{m}VV \\\\
  D  @>{i}>> E       @>{k}>> F
\\end{CD}
$$
"

Statement
    "Beweise $A \\Rightarrow F$."
    (A B C D E F : Prop) (f : A → B) (g : C → B) (h : B → E)
     (i : D → E) (k : E → F) (m : C → F) : A → F := by
  intro ha
  apply k
  apply h
  apply f
  assumption

HiddenHint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : A → F =>
"Wieder ist es schlau, mit `intro` anzufangen."

HiddenHint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : F =>
"Versuch mit `apply` den richtigen Weg zu finden."

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : C =>
"Sackgasse. Probier doch einen anderen Weg."

Hint (A : Prop) (B : Prop) (C : Prop) (D : Prop) (E : Prop) (F : Prop)
    (hA : A) (f : A → B) (g : C → B) (h : B → E)
    (i : D → E) (k : E → F) (m : C → F) : D =>
"Sackgasse. Probier doch einen anderen Weg."

NewTactics apply assumption revert intro

-- https://www.jmilne.org/not/Mamscd.pdf
