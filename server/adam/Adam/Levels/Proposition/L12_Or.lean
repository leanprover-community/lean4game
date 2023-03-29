import Adam.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight

set_option tactic.hygienic false

--set_option autoImplicit false


Game "Adam"
World "Proposition"
Level 13

Title "Oder"

Introduction
"
Der nächste bitte …
"

Statement ""
    (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  Hint "**Robo** Schau mal, wenn du mit dem Finger eine Annahme berührst, zeigt es dir,
wie die Klammern gesetzt sind. Irre…

**Du** Ah ich sehe, also `({A} ∧ {B}) ∨ {A}`!

**Du** Ich glaube den ganzen Zircus hier langsam nicht mehr:
Zuerst ein \"Und\" im Ziel, dann \"Und\" in der Annahme, dann \"Oder\" im Ziel und jetzt
\"Oder\" in der Annahme, die haben sich doch abgesprochen!

**Robo** Lass ihnen doch ihren Spaß.
Wir sind ja gleich hier fertig, und können zu einem interessanteren Planeten weiterfliegen.

**Du** Also, wieder `rcases …`?

**Robo** Ja, aber diesmal nicht `rcases {h} with ⟨h₁, h₂⟩`, sondern `rcases {h} with h | h`."
  rcases h with h | h
  Hint "**Robo**
Jetzt musst Du Dein Ziel zweimal beweisen:
Einmal unter Annahme der linken Seite `{A} ∨ {B}`,
und einmal unter Annahme der rechten Seite `{A}`.
Hier haben nehmen wir an, die linke Seite
sei wahr."
  Hint (hidden := true) " **Robo** Wie man mit einem Und in den Annahmen umgeht,
weißt Du doch schon:
`rcases h with ⟨h₁, h₂⟩`.  Zur Erinnerung: Für die Klammern schreibst Du `\\<>`."
  rcases h with ⟨h₁, h₂⟩
  Hint "**Robo** Jetzt musst Du Dein Ziel zweimal beweisen:
Einmal unter Annahme der linken Seite `{A}`,
und einmal unter Annahme der rechten Seite `{A} ∨ {B}`. Hier haben nehmen wir an, die linke Seite
sei wahr."
  assumption
  assumption

Conclusion
"**Du**  Ok, das scheint ihn zufriedenzustellen. Nur noch eine Seele…
Kannst Du mir vorher noch einmal kurz alles Leansch zusammenfassen,
das Du mir bis hierher beigebracht hast?

Robo strahlt überglücklich.  Noch *nie* warst Du so auf ihn angewiesen.

**Robo** Na klar, schau her!

## Notationen / Begriffe

|               | Beschreibung                                                             |
|:--------------|:-------------------------------------------------------------------------|
| *Goal*        | Was aktuell zu beweisen ist.                                             |
| *Annahme*     | Objekte & Resultate, die man zur Verfügung hat.                          |
| *Taktik*      | Befehl im Beweis. Entspricht einem Beweisschritt.                        |
| `ℕ`           | Typ aller natürlichen Zahlen.                                            |
| `0, 1, 2, …`  | Explizite natürliche Zahlen.                                             |
| `=`           | Gleichheit.                                                              |
| `≠`           | Ungleichheit. Abkürzung für `¬(·=·)`.                                    |
| `Prop`        | Typ aller logischen Aussagen.                                            |
| `True`        | Die logische Aussage `(True : Prop)` ist bedingungslos wahr.             |
| `False`       | Die logische Aussage `(False : Prop)` ist bedingungslos falsch.          |
| `¬`           | Logische Negierung.                                                      |
| `∧`           | Logisch UND.                                                             |
| `∨`           | Logisch ODER.                                                            |
| `(n : ℕ)`     | Eine natürliche Zahl.                                                    |
| `(A : Prop)`  | Eine logische Aussage.                                                   |
| `(ha : A)`    | Ein Beweis, dass die logische Aussage `(A : Prop)` wahr ist.             |
| `(h : A ∧ B)` | Eine Annahme, die den Namen `h` bekommen hat.                            |
| `⟨·,·⟩`       | Schreibweise für Struktur mit mehreren Feldern (kommt später im Detail). |
| `h.1, h.2, …` | Die einzelnen Felder der Stuktur. Auch `h.[Name des Feldes]`             |


## Taktiken

Die Worte, die Du aktiv gebrauchen musst, heißen zusammengefasst `Taktiken`.  Hier sind alle Taktiken, die wir auf diesem Planeten gebraucht haben:

|    | Taktik                    | Beispiel                                          |
|:---|:--------------------------|:--------------------------------------------------|
| 1  | `rfl`                     | Beweist `A = A`.                                  |
| 2  | `assumption`              | Sucht das Goal in den Annahmen.                   |
| 3  | `contradiction`           | Sucht einen Widerspruch.                          |
| 4  | `trivial`                 | Kombiniert die obigen drei Taktiken (und mehr).   |
| 5  | `constructor`             | Teilt ein UND im Goal auf.                        |
| 6  | `left`/`right`            | Beweist eine Seite eines ODER im Goal.            |
| 7ᵃ | `rcases h with ⟨h₁, h₂⟩`  | Teilt ein UND in den Annahmen auf.                |
| 7ᵇ | `rcases h with h \\| h`   | Teilt ein ODER in den Annahmen in zwei Fälle auf. |

**Du** Woher weißt Du das eigentlich alles?

**Robo** Keine Ahnung.  War, glaube ich, vorinstalliert.
"


NewTactic assumption rcases
DisabledTactic tauto
