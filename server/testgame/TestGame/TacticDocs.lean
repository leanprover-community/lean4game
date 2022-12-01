import GameServer.Commands

import TestGame.Tactics

TacticDoc rfl
"
## Beschreibung

`rfl` beweist ein Goal der Form `X = X`.

## Detail

`rfl` beweist jedes Goal `A = B` wenn `A` und `B` genau das gleiche sind.
Wichtig ist nicht, ob diese im Infoview gleich aussehen, sondern ob sie in
Lean gleich definiert sind.

## Beispiel
`rfl` kann folgenes Goal beweisen:
```
Objects
  a b c : ℕ
Prove:
  (a + b) * c = (a + b) * c
```

`rfl` kann auch folgendes beweisen:
```
Objects
  n : ℕ
Prove:
  1 + 1 = 2
```
denn Lean liest dies intern als `0.succ.succ = 0.succ.succ`.
"

TacticDoc assumption
"
## Beschreibung

`assumption` sucht nach einer Annahme, die genau dem Goal entspricht.

## Beispiel
Wenn das Goal wie folgt aussieht:
```
Objects
  a b c d : ℕ
  h : a + b = c
  g : a * b = 16
  t : c = 12
Prove:
  a + b = c
```

dann findet `assumption` die Annahme `h`und schliesst den Beweis.
"

TacticDoc rewrite
"
## Beschreibung

Wie `rw` aber ruft `rfl` am Schluss nicht automatisch auf.
"

TacticDoc rw
"
## Beschreibung

Wenn man eine Annahme `(h : X = Y)` hat, kann man mit
`rw [h]` alle `X` im Goal durch `Y` ersetzen.

## Detail
- `rw [←h]` wendet `h` rückwärts an und ersetzt alle `Y` durch `X`.
- `rw [h, g, ←f]`: Man kann auch mehrere `rw` zusammenfassen.
- `rw [h] at h₂` ersetzt alle `X` in `h₂` zu `Y` (anstatt im Goal).

`rw` funktioniert gleichermassen mit Annahmen `(h : X = Y)` also auch
mit Theoremen/Lemmas der Form `X = Y`

## Beispiel

TODO
"


TacticDoc apply
"
## Beschreibung

TODO
"

TacticDoc constructor
"
## Beschreibung

TODO
"

TacticDoc rcases
"
## Beschreibung

TODO
"

TacticDoc left
"
## Beschreibung

TODO
"

TacticDoc right
"
## Beschreibung

TODO
"














TacticDoc induction_on
"
## Summary

If `n : ℕ` is in our objects list, then `induction_on n`
attempts to prove the current goal by induction on `n`, with the inductive
assumption in the `succ` case being `ind_hyp`.

### Example:
If your current goal is:
```
Objects
  n : ℕ
Prove:
  2 * n = n + n
```

then

`induction_on n`

will give us two goals:

```
Prove:
  2 * 0 = 0 + 0
```

and
```
Objects
  n : ℕ,
Assumptions
  ind_hyp : 2 * n = n + n
Prove:
  2 * succ n = succ n + succ n
```
"



TacticDoc intro
"Useful to introduce stuff"

TacticSet basics := rfl induction_on intro rewrite
