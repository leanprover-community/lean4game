import Adam.Metadata

Game "Adam"
World "Implication"
Level 5

Title "Implikation"

Introduction
"
Die nächste Seite sieht ein bisschen komplizierter aus.  Damit Ihr nicht die Übersicht verliert, fasst Robo sofort die verschiedenen Implikationen in einem Diagramm zusammen.
  $$
  \\begin{CD}
    A  @>{f}>> B       @<{g}<< C       \\\\
    @. @V{h}VV @V{m}VV \\\\
    D  @>{i}>> E       @>{k}>> F       \\\\
    @A{m}AA @A{n}AA @V{p}VV \\\\
    G  @<{q}<< H       @>{r}>> I
  \\end{CD}
  $$
"
Statement
    (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : B → E) (i : D → E) (k : E → F) (m : G → D)
    (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  Hint "**Du**: Also ich muss einen Pfad von Implikationen $A \\Rightarrow I$ finden.

  **Robo**: Dann fängst du am besten wieder mit `intro` an."

  intro ha
  Branch
    apply r
    Hint "**Robo**: Das sieht nach einer Sackgasse aus …"
  Hint (hidden := true) "**Robo**: Na wieder `apply`, was sonst."
  apply p
  apply k
  apply h
  Branch
    apply g
    Hint "**Robo**: Nah, da stimmt doch was nicht …"
  apply f
  assumption

Conclusion
"Der Operationsleiter bedankt sich wieder artig.  Er drückt wieder auf ein paar Knöpfe, und mit einem lauten Ratteln springen mehrere Förderbänder gleichzeitig wieder an."

DisabledTactic tauto

-- https://www.jmilne.org/not/Mamscd.pdf
