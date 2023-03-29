import Adam.Metadata

import Mathlib.Tactic.Ring
import Mathlib

Game "Adam"
World "Prime"
Level 1

Title "Teilbarkeit"

Introduction
"
Ihr begenet einer Frau, die mit Vorschlaghammer und Schaufel anscheinend an einer Erweiterung
ihres Hauses baut. Im gespräch erzählt sie euch wie die Dornenwände gezüchtet wurden vor ihrer
Zeit, und über's Wetter und so.

**Handwerkerin**: (*langer Monolog*) …, und dann gestern habe ich zwei Herren überhört,
wie sie an folgender Aufgabe gesessen sind, könnt ihr mir das erklären?
"

-- Die Aussage \"$m$ teilt $n$.\" wird in Lean als `m | n` (`\\|`) geschrieben.

-- **Wichtig:** `∣` (Teilbarkeit) ist ein spezielles Unicode Symbol, das nicht dem
-- senkrechten Strich auf der Tastatur (`|`) entspricht. Man erhält es mit `\\|`.

-- `m ∣ n` bedeutet `∃ c, n = m * c`, das heisst, man kann damit genau gleich umgehen
-- wie mit einem `∃`-Quantifier.

Statement dvd_add (n m k : ℕ) (h : m ∣ n) (g : m ∣ k) : m ∣ n + k := by
  Hint "**Robo**: `n ∣ m` bedeutet \"$n$ teilt $m$\", der senkrechte Strich ist allerdings
  ein spezieller, den man mit `\\|` schreibt.
  Definiert ist dieses Symbol als `∃ c, n = m * c`.

  **Du**: Dann kann ich direkt `rcases` und `use` verwenden, wie wenns ein `∃` wäre?

  **Robo**: Genau!"
  Hint (hidden := true) "**Robo**: Fang doch damit an, mit `rcases _ with ⟨x ,hx⟩`
  alle Hyptothesen aufzuteilen."
  rcases h with ⟨x, h⟩
  rcases g with ⟨y, g⟩
  Hint (hidden := true) "**Robo**: Jetzt musst du mit `use _` eine Zahl angeben so dass
  `{n} + {k} = {m} * _` gilt."
  use x + y
  Hint (hidden := true) "**Du**: Mit ein bisschen umschreiben kann man sicer `ring` verwenden."
  rw [h, g]
  ring

DisabledLemma dvd_add
