import Adam.Metadata

import Adam.ToBePorted

set_option tactic.hygienic false

Game "Adam"
World "Sum"
Level 1

Title "Simp"

Introduction
"
**Unbekannte**: Willkommen auf *Indu*, unserem Planeten! Bevor ich euch herumzeigen will,
sagt mir, ob ihr unsere Lebensweise zu verstehen und schätzen wisst:
In diesem Kapitel lernen wir endliche Summen und mehr Übungen zur Induktion.

"

-- Eine endliche Summe läuft erstmal immer über einen endlichen Index
-- `Fin n`, welcher $n$ Elemente
-- $\\{0, 1, \\ldots, n-1\\}$ beinhaltet.

-- Der Syntax für  $\\sum_{i=0}^n a_i$ ist `∑ i : Fin n, _` (\\sum)

-- Als erstes kann die Taktik `simp` (für \"simplification\") ganz viel Triviales vereinfachen.
-- `simp` ist eine der stärksten Taktiken in Lean und verwendet
-- ganz viele markierte Lemmas um das Goal zu vereinfachen.

-- Zum Beispiel kennt es ein Lemma das ungefähr so aussieht:

-- ```
-- @[simp]
-- lemma sum_const_add (n : ℕ) : (∑ i in Fin n, 0) = 0 := by
--   sorry
-- ```

-- Die Taktik `simp` benützt alle Lemmas, die mit `@[simp]` markiert sind.

-- (Tipp: `simp?` zeigt an, welche Lemmas `simp` benutzen würde.)

open BigOperators

Statement (n : ℕ) : (∑ i : Fin n, (0 + 0)) = 0 := by
  Hint "BUG"

  -- TODO (Bug): Invalid escape sequence:
  -- "**Du**: Oh das ist ganz schön viel neues… Mal sehen, das sagt wohl
  -- $( \\sum_i 0 + 0 ) = 0$. Dann ist das vielleicht doch nicht so komplex.

  -- **Robo**: Genau! Man schreibt `\\sum`. Beachte den Index:
  -- $( \\sum_\{i=0}^\{n-1} 0 + 0 ) = 0$, also `Fin n` ist ein Typ mit den Elementen
  -- $\\{0, \\ldots, n-1\\}$.

  -- **Du**: Oke, also `Fin n` hat `n` Elemente. Und was mach ich jetzt?

  -- **Robo**: `simp` ist eine ganz starke Taktik, die viele Terme vereinfacht, wir
  -- fangen besser an, diese zu benützen.

  -- Irgendwie hast du das Gefühl ein Déjà-vue zu haben…"
  simp

OnlyTactic simp

Conclusion "**Unbekannte**: Sehr gut, folgt mir!"
