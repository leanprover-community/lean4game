import GameServer.Commands
import Adam.Tactics

TacticDoc assumption
"
`assumption` sucht nach einer Annahme, die genau dem Goal entspricht.

## Beispiel

`assumption` sucht durch die Annahmen und merkt dass `h` genau mit dem Goal übereinstimmt.

```
Objekte
  a b c d : ℕ
  h : a + b = c
  g : a * b = 16
  t : c = 12
Goal
  a + b = c
```
"

TacticDoc apply
"
`apply my_lemma` Versucht das Goal mit der Aussage des Lemmas zu unifizieren
und erstellt ein neues Goal pro Annahme des Lemmas, die noch zu zeigen ist.

## Details
`apply` funktioniert gleichermassen für Lemmas wie für Implikationen
wie z.B. `(h : A → B)`.

## Beispiel

Gegeben folgendes Lemma:
```
lemma Nat.eq_zero_of_le_zero {n : ℕ} (h : n ≤ 0) : n = 0 := by sorry
```

Und folgendes Problem:

```

Objekte
  n : ℕ
  ...
Goal
  n = 0
```

Hier ändert `apply Nat.eq_zero_of_le_zero` das Goal zu `n ≤ 0` durch Anwendung
des Lemmas.
"

TacticDoc by_cases
"
`by_cases h : P` macht eine Fallunterscheidung. Im ersten Goal wird eine Annahme
`(h : P)` hinzugefügt, im zweiten `(h : ¬P)`.

## Details

`P` kann eine beliegige Aussage sein, die als entweder wahr oder falsch angenommen wird.

## Beispiel

```
example (A : Prop) : A ∨ ¬ A := by
  by_cases h : A
  · left
    assumption
  · right
    assumption
```
"

TacticDoc by_contra
"
`by_contra h` startet einen Widerspruchsbeweis.

## Details
Sei `P` das aktuelle Goal. `by_contra h` fügt eine neue Annahme `(h : ¬P)` hinzu
und setzt das Goal auf `False`.

Oft will man `by_contra` nutzen wenn das Goal von der Form `¬ P` ist.

## Hilfreiche Resultate

* `contradiction` schliesst den Widerspruchsbeweis wenn sich (zwei) Annahmen
widersprechen.
* `contrapose` führt einen Beweis durch Kontraposition und ist entsprechend
in ähnlichen Situationen nutzbar wie `by_contra`
"

TacticDoc change
"
`change t` ändert das Goal zu `t`. Voraussetzung ist, dass `t` und das alte Goal defEq sind.

## Details

Dies ist insbesonder hilfreich wenn eine Taktik nicht merkt, dass das Goal defEq ist zu einem
Term, der eigentlich gebraucht würde.

## Beispiel

Aktuelles Goal:

```
b: ℝ
⊢ 1 • b = b
```
Wobei die Skalarmultiplikation als `fun (a : ℚ) (r : ℝ) => ↑a * r` definiert war. Dann
kann man mit `change (1 : ℚ) * b = b` das Goal umschreiben und anschliessend mit Lemmas
über die Multiplikation beweisen.
"

TacticDoc constructor
"
`constructor` teilt ein Goal auf, wenn das Goal eine Struktur ist

## Detail
Wenn das Goal eine Struktur ist, wie z.B. `A ∧ B` welches zwei Felder hat `⟨A, B⟩`, dann
erzeugt `constructor` ein Goal pro Feld der Struktur.

## Hilfreiche Resultate

* Das Gegenteil von `constructor` ist `⟨_, _⟩` (`\\<>`), der *anonyme Konstructor*.
Dieser enspricht ungefähr der Tupel-Notation in
\"eine Gruppe ist ein Tupel $(G, 0, +)$, sodass …\".

## Beispiel

```
example {A B : Prop} (h : A) (g : B) : A ∧ B := by
  constructor
  · assumption
  · assumption
```
"

TacticDoc contradiction
"
`contradiction` schliesst den Beweis wenn es einen Widerspruch in den Annahmen findet.

## Details
Ein Widerspruch in den Annahmen kann unter anderem folgendermassen aussehen:

* `(h : n ≠ n)`
* `(h : A)` und `(h' : ¬A)`
* `(h : False)` (i.e. ein Beweis von `False`)

## Beispiel

Folgenes Goal wird von `contradiction` bewiesen

## Hilfreiche Resultate

* Normalerweise wird `contradiction` gebraucht um einen Widerspruchsbeweis zu
  schliessen, der mit `by_contra` eröffnet wurde.
* Ein Beweis von `False` representiert in Lean einen Widerspruch.

```
Objekte:
  (n m : ℕ)
  (h : n = m)
  (g : n ≠ m)
Goal
  37 = 60
```
nach dem Motto \"ein Widerspruch beweist alles.\"
"

TacticDoc contrapose
"
`contrapose` ändert ein Goal der Form `A → B` zu `¬B → ¬A` und führt damit
eine Beweis durch Kontraposition.

## Hilfreiche Resultate

* `revert h` kann nützlich sein um eine Annahme als Implikationsprämisse zu schreiben bevor man
  `contrapose` verwendet.
"

TacticDoc exact
"
`exact h` schliesst das Goal wenn der Term `h` mit dem Goal übereinstimmt.
"

TacticDoc fin_cases
"
`fin_cases i` führt eine Fallunterscheidung wenn `i` ein endlicher Typ ist.

## Details
`fin_cases i` ist insbesondere nützlich für `(i : Fin n)`, zum Beispiel als Index in
endlich dimensionalen Vektorräumen.

In diesem Fall bewirkt `fin_cases i` dass man Komponentenweise arbeitet.
"

TacticDoc funext
"
`funext x` wird bei Gleichungen von Funktionen `f = g` gebraucht. Das Goal wird zu
`f x = g x`.

## Details
Nach dem Motto `f = g ↔ ∀ x, f x = g x` sind zwei Funktionen dann identisch, wenn sie
angewendet auf jedes Element identisch sind. `funext x` benützt dieses Argument.
"

TacticDoc «have»
"
`have h : P` führt ein Zwischenresultat ein.

## Details
Anschliessend muss man zuerst dieses Zwischenresultat beweisen bevor man mit dem Beweis
weitermachen und das Zwischenresultat verwenden kann.

## Hilfreiche Resultate

* `suffices h : P` funktioniert genau gleich, aussert das die beiden entstehenden Beweise
  vertauscht sind.
* `let h : Prop := A ∧ B` ist verwandt mit `have`, mit Unterschied, dass man mit `let`
  eine temporäre Definition einführt.
"

TacticDoc induction
"
`induction n` führt einen Induktionsbeweis über `n`.

## Detail

Diese Taktik erstellt zwei Goals:
* Induktionsanfang, wo `n = 0` ersetzt wird.
* Induktionsschritt, in dem man die Induktionshypothese `n_ih` zur Verfügung hat.

Der volle Syntax mit Option zum umbenennen der Induktionshypothes und -variable ist

```
induction n with
| zero =>
  sorry
| succ m m_ih =>
  sorry
```

da dieser sich über mehrere Zeilen erstreckt wird er im Spiel nicht eingeführt.

## Hifreiche Resultate

* `Nat.succ_eq_add_one`: schreibt `n.succ = n + 1` um.
* `Nat.zero_eq`: schreibt `Nat.zero = 0` um.

Beide sind DefEq, aber manche Taktiken können nicht damit umgehen

* Siehe Definition `∑` für Hilfe mit Induktion über Summen.
* `rcases n` ist sehr ähnlich zu `induction n`. Der Unterschied ist, dass bei
`rcases` keine Induktionshypothese im Fall `n + 1` zur Verfügung steht.

## Beispiel

```
example (n : ℕ) : 4 ∣ 5^n + 7 := by
  induction n
  sorry      -- Fall `n = 0`
  sorry      -- Fall `n + 1`
```
"

TacticDoc intro
"
`intro x` wird für Goals der Form `A → B` oder `∀ x, P x` verwendet.
Dadurch wird die Implikationsprämisse (oder das Objekt `x`) den Annahmen hinzugefügt.

## Hilfreiche Resultate

* `revert h` macht das Gegenteil von `intro`.
"

TacticDoc left
"
Wenn das Goal von der Form `A ∨ B` ist, enscheidet man mit `left` die linke Seite zu zeigen.

## Hilfreiche Resultate

* `right` entscheidet sich für die linke Seite.
"

TacticDoc «let»
"
`let x : ℕ := 5 ^ 2` führt eine neue temporäre Definition ein.

## Hilfreiche Resultate

* `have x : ℕ := 5 ^ 2` führt ebenfalls eine neue natürliche Zahle `x` ein, aber
  Lean vergisst sofort, wie die Zahl definiert war. D.h. `x = 25` wäre dann nicht
  beweisbar. Mit `let x : ℕ := 5 ^ 2` ist `x = 25` durch `rfl` beweisbar.
"

TacticDoc linarith
"
`linarith` löst Systeme linearer (Un-)Gleichungen.

## Detail
`linarith` kann lineare Gleichungen und Ungleichungen beweisen indem
es das Gegenteil vom Goal annimmt und versucht einen Widerspruch in den
Annahmen zu erzeugen (Widerspruchsbeweis). Es braucht ein `≤` definiert um
zu funktionieren.

## Beispiel

Folgendes kann `linarith` beweisen.
```
Objekte
  x y : ℤ
  h₁ : 5 * y ≤ 35 - 2 * x
  h₂ : 2 * y ≤ x + 3
Goal
  y ≤ 5
```
"

TacticDoc push_neg
"
`push_neg` schreibt `¬∀ x, _` zu `∃ x, ¬ _` und `¬∃ x, _` zu `∀x, ¬ _` um.

## Details

`psuh_neg` schiebt das `¬` soweit nach innen wie möglich.

## Hilfreiche Resultate

* Die beiden Lemmas heissen `not_forall` und `not_exists` und können mit `rw` einzeln angewendet
  werden.
"

TacticDoc rcases
"
`rcases h` teilt eine Annahme `h` in ihre Einzelteile auf.

## Details
Für Annahmen die Strukturen sind, wie z.B. `h : A ∧ B` (oder `∃x, P x`) kann man die
Einzelteile mit  `rcases h with ⟨a, b⟩` (oder `rcases h with ⟨x, hx⟩`) benennen.

Für eine Annahme der Form `h : A ∨ B` kann man mit `rcases h with ha | hb` zwei Goals
erzeugen, einmal unter Annahme der linken Seite, einmal unter Annahme der Rechten.

## Hilfreiche Resultate

* Für `n : ℕ` hat `rcases n` einen ähnlichen Effekt wie `induction n` mit dem Unterschied,
  dass im Fall `n + 1` keine Induktionshypothese zur Verfügung steht.
* In Lean gibt es auch die Taktik `cases`, die gleich funktioniert wie `rcases` aber
  einen mehrzeiligen Syntax hat:
  ```
  cases h with
  | inl ha =>
    sorry
  | inr hb =>
    sorry
  ```
  Hier sind `inl`/`inr` die Namen der Fälle und `ha`/`hb` sind frei gewählte Namen für die
  freien Variablen
"

TacticDoc refine
"
`refine { ?..! }` wird benötigt um eine Struktur (z.B. ein $R$-Modul) im Taktikmodus in einzelne
Goals aufzuteilen. Danach hat man ein Goal pro Strukturfeld.

(*Bemerkung*: Es gibt in Lean verschiedenste bessere Varianten dies zu erreichen,
z.B. \"Term Modus\" oder \"anonyme Konstruktoren\", aber für den Zweck des Spieles bleiben wir
bei diesem Syntax.)
"

TacticDoc revert
"
`revert h` fügt die Annahme `h` als Implikationsprämisse vorne ans Goal an.

## Hilfreiche Resultate

* `revert` ist das Gegenteil von `intro`.
* `revert` kann insbesondere nützlich sein, um anschliessend `contrapose` zu verwenden.

## Beispiel

```
Objekte
  A P : Prop
  h : P
Goal
  A
```

hier ändert `revert h` den Status zu

```
Objekte
  A P : Prop
Goal
  P → A
```
"

TacticDoc rfl
"
`rfl` beweist ein Goal der Form `X = X`.

## Detail

`rfl` beweist jedes Goal `A = B` wenn `A` und `B` per Definition das gleiche sind (DefEq).
Andere Taktiken rufen `rfl` oft am Ende versteckt
automatisch auf um zu versuchen, den Beweis zu schliessen.


## Beispiel
`rfl` kann folgende Goals beweisen:

```
Objekte
  a b c : ℕ
Goal:
  (a + b) * c = (a + b) * c
```

```
Objekte
  n : ℕ
Goal
  1 + 1 = 2
```
denn Lean liest dies intern als `0.succ.succ = 0.succ.succ`.
"

TacticDoc right
"
Wenn das Goal von der Form `A ∨ B` ist, enscheidet man mit `right` die rechte Seite zu zeigen.

## Hilfreiche Resultate

* `left` entscheidet sich für die linke Seite.
"

TacticDoc ring
"
Löst Gleichungen mit den Operationen `+, -, *, ^`.

## Details
Insbesondere funktioniert `ring` in Ringen/Semiringen wie z.B. `ℕ, ℤ, ℚ, …`
(i.e. Typen `R` mit Instanzen `Ring R` oder `Semiring R`).
Die Taktik ist besonders auf kommutative Ringe (`CommRing R`) ausgelegt.

## Hilfreiche Resultate

* `ring` kann nicht wirklich mit Division (`/`) oder Inversen (`⁻¹`) umgehen. Dafür ist die
  Taktik `field_simp` gedacht, und die typische Sequenz ist
  ```
  field_simp
  ring
  ```
* Wenn `ring` nicht abschliesst, sagt es man solle `ring_nf` verwenden. Normalerweise heisst
  das aber, dass man was falsch gemacht hat und die Seiten der Gleichung noch nicht gleich sind.
"

TacticDoc rw
"
Wenn man eine Annahme `(h : X = Y)` hat, kann man mit
`rw [h]` alle `X` im Goal durch `Y` ersetzen.

## Details

* `rw [←h]` wendet `h` rückwärts an und ersetzt alle `Y` durch `X`.
* `rw [h, g, ←f]`: Man kann auch mehrere `rw` zusammenfassen.
* `rw [h] at h₂` ersetzt alle `X` in `h₂` zu `Y` (anstatt im Goal).

`rw` funktioniert gleichermassen mit Annahmen `(h : X = Y)` also auch
mit Theoremen/Lemmas der Form `X = Y`
"

TacticDoc simp
"
`simp` versucht alle Vereinfachungslemmas anzuwenden, die in der `mathlib` mit `@[simp]`
gekennzeichnet sind.

## Details

* `simp?` zeigt welche Lemmas verwendet wurden.
* `simp [my_lemma]` fügt zudem `my_lemma` temporär zur Menge der `simp`-Lemmas hinzu.
* ein `simp`, das nicht am Ende des Beweis steht sollte durch eine entsprechende
  `simp only [...]` Aussage ersetzt werden, um den Beweis stabiler zu machen.
"

TacticDoc simp_rw
"
`simp_rw [h₁, h₂, h₃]` versucht wie `rw` jedes Lemma der Reihe nach zu Umschreiben zu verwenden,
verwendet aber jedes Lemma so oft es kann.

## Details

Es bestehen aber drei grosse Unterschiede zu `rw`:

* `simp_rw` wendet jedes Lemma so oft an wie es nur kann.
* `simp_rw` kann besser unter Quantifiern umschreiben als `rw`.
* `simp_rw` führt nach jedem Schritt ein `simp only []` aus und vereinfacht dadurch grundlegenste
  Sachen.
"

TacticDoc «suffices»
"
`suffices h : P` führt ein neues Zwischenresultat ein, aus dem das Goal direkt folgen soll.

## Details

Der einzige Unterschied zu `have h : P` ist, dass die beiden resultierenden Goals vertauscht sind.

Mathematisch braucht man diese in ein bisschen unterschiedlichen Fällen:

* `suffices h : P` : \"Es genügt zu zeigen, dass …\". Als erstes folgt die Erklärung wieso
  das genügt, danach muss man nur noch `P` beweisen.
* `have h : P` : Ein (kleines) Zwischenresultat. Als erstes folgt dann der Beweis dieses
Resultats, anschliessend setzt man den Beweis mit Hilfe des Zwischenresultats fort.
"

TacticDoc tauto
"
## Beschreibung

TODO
"

TacticDoc trivial
"
`trivial` versucht durch Kombination von wenigen simplen Taktiken das Goal zu schliessen.

## Details
Die Taktiken, die verwendet werden sind:

* `assumption`
* `rfl`
* `contradiction`
* und noch 3 andere, die hier nicht behandelt werden
  (`decide`, `apply True.intro`, `apply And.intro`).
"

TacticDoc unfold
"
`unfold myDef` öffnet eine Definition im Goal.

## Details
Bis auf DefEq (definitinal equality) ändert `unfold` nichts, manche Taktiken
(z.B. `push_neg`, `rw`) brauchen aber manchmal die Hilfe.

`unfold myDef at h` kann auch Definitionen in Annahmen öffnen

## Hilfreiche Resultate

* `change P` ist eine andere Taktik, die das aktuelle Goal in einen DefEq-Ausdruck umschreibt.
  Diese Taktik braucht man auch manchmal um zu hacken, wenn Lean Mühe hat etwas zu verstehen.
"

TacticDoc use
"
Wenn das Goal von der Form `∃x, P x` ist, kann man mit `use n` ein konkretes Element angeben
mit dem man das Goal beweisen möchte.

## Details

`use n` versucht zudem anschliessend `rfl` aufzurufen, und kann das Goal damit manchmal direkt
schließen.
"
