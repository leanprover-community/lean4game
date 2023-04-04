import Adam.Metadata
import Adam.Options.MathlibPart

Game "Adam"
World "Predicate"
Level 5

Title "Definitionally equal"

Introduction
"
Beim nächsten Problem bekommt ihr ausnahmsweise Hilfe vom Publikum.

**Alle**: `rfl`, `rfl`, …
"

Statement : 1 + 1 = 2 := by
  Hint "**Du**: Wieso nicht `ring`?

  **Robo**: Klar, `ring` würde normalerweise auch funktioneren.  Aber ich würde mich hier dem Mehrheitswillen beugen …"
  rfl

OnlyTactic rfl

Conclusion
"
**Robo**:  Der Grund, warum hier ausnahmsweise auch mal `rfl` funktioniert hat, ist, dass auf beiden Seiten tatsächlich *per Definition* dasselbe steht.  Das soll heißen, wenn man links in `1 + 1` die Definition von `1` und `+ 1` einsetzt, und rechts die Definition von `2`, dann erhält man *buchstäblich* dasselbe (nämlich `(0.succ).succ`).

**Du**: Na schön. Muss ich mir jetzt diese Definition von `2` merken?

**Robo**: Ich glaube eher nicht.
"
