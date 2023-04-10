import Adam.Metadata

import Adam.Options.MathlibPart

Game "Adam"
World "Inequality"
Level 5

Title "Drinker's Paradox"

set_option tactic.hygienic false

Introduction
"
**weitere Person**: Jetzt aber zu einem anderen Thema. Kennt ihr eigentlich das
Drinker-Paradoxon?

**Robo**: Das ist in meinem System. *In dieser Bar gibt es eine Person, so dass
falls diese Person jetzt am drinken ist, dann sind alle am trinken*.

**weitere Person**: Genau! Könnt ihr mir das beweisen?
"

open Function

Statement {People : Type} [Inhabited People] (isDrinking : People → Prop) :
    ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  Hint "**Du**: Wenn `p` eine Person ist, dann ist also `isDrinking p` eine Aussage,
  die wahr oder falsch ist. Soweit so gut.
  Wieso hat er aber `Inhabited People` hinzugefügt?

  **Robo**: Die Aussage ist falsch, wenn die Bar leer wäre, da dann keine solche
  Person existieren kann. Jedenfalls kannst du dadurch jederzeit `default`, oder lang
  `(default : Person)`, schreiben, wenn du einfach irgendeine Person brauchst.

  **Du**: Und wie fang ich jetzt an?

  **Robo**: Du könntest eine Fallunterscheidung machen, ob die Aussage
  `∀ (y : People), isDrinking y` wahr oder falsch ist."
  Hint (hidden := true) "**Robo**: Schau mal `by_cases` an."
  by_cases ∀ y, isDrinking y
  Hint (hidden := true) "**Du**: Und wen nehm ich jetzt?

  **Robo**: Wie gesagt, `default` ist eine x-beliebige Person."
  use (default : People)
  intro
  assumption
  Hint (hidden := true) "**Robo**: Du könntest hier mit `push_neg at {h}` weitermachen."
  push_neg at h
  rcases h with ⟨p, hp⟩
  use p
  intro hp'
  Hint (hidden := true) "**Robo**: Was siehst du, wenn du `{hp}` und `{hp'}` anschaust?"
  contradiction

LemmaTab "Logic"
NewDefinition Inhabited

Conclusion
"**weitere Person**: Fantastisch! Zum wohl!

…und damit endet auch deine Erinnerung und wer weiss was du anschließend gemacht hast…"
