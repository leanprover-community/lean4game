import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

Game "TestGame"
World "Proposition"
Level 7

Title "Widerspruch beweist alles."

Introduction
"
Als nächstes kommen drei Querulanten.  Der erste hat folgendes Problem:
"

Statement ""
    (A : Prop) (h : False) : A := by
  Hint "**Du** Wenn ich das jetzt richtig lese, ist `{A}` eine Aussage,
und wir haben außerdem eine Annahme names `{h}`, die besagt …

**Robo** … die besagt, dass `False` gilt.

**Du** Ich dachte, `False` gilt nie?

**Robo** Ja, genau.  Die Annahme ist `False`, also falsch.
Und aus einer falschen Annahme kann man bekanntlich alles beweisen!
Insbesondere die gesuchte Aussage `{A}`.

**Du** Und wie erkläre ich das jetzt diesem Formalosophen?

**Robo** Ich glaube, Du musst ihn darauf hinweisen, dass zwischen der allgemeingültigen
Annahme `True` und seiner Annahme `False` ein Widerspruch besteht.  Probier mal `contradiction`."
  contradiction

Conclusion
"Der erste Querulant ist offenbar zufrieden.

**Du** War das jetzt ein Widerspruchsbeweis?

**Robo** Nein, nein, ein Widerspruchsbeweis sieht anders aus. Das Argument hier war:
 wir haben eine `contradiction` in unserem Annahmen, also folgt jede beliebige Aussage.
"

NewTactic contradiction
DisabledTactic tauto
