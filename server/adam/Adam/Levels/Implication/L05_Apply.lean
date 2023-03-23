import Adam.Metadata

Game "Adam"
World "Implication"
Level 5

Title "Implikation"

Introduction
"
Selbstsicher folgt ihr den Anweisungen und geht nach draußen zum
defekten Kontrollelement. Dieses zeigt ein kompliziertes Diagram:
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

  **Robo**: Und dann fängst du am besten wieder mit `intro` an."
  intro ha
  Branch
    apply r
    Hint "**Robo**: Das sieht nach einer Sackgasse aus…"
  Hint (hidden := true) "**Robo**: Na wieder `apply`, was sonst."
  apply p
  apply k
  apply h
  Branch
    apply g
    Hint "**Robo**: Nah, da stimmt doch was nicht…"
  apply f
  assumption

Conclusion
"Mit einem lauten Ratteln springen die Förderbänder wieder an.

**Operationsleiter**: Vielen Dank euch! Kommt ich geb euch eine Führung und stell euch den
Technikern hier vor."

DisabledTactic tauto

-- https://www.jmilne.org/not/Mamscd.pdf
