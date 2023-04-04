import Adam.Metadata
import Adam.Options.MathlibPart

import Adam.ToBePorted

Game "Adam"
World "Prime"
Level 2

Title "Primzahlen"

Introduction
"
Als nächstes Begnet ihr einem Lehrer, der nachdenkend an der Sonne sitzt.

**Lehrer**: Sagt mal, mich hat heute einer meiner Schüler was gefragt,
und ich glaube einfach, der ist in so jungen Jahren bereits schlauer als ich.

Hier etwas Kontext:
"

Statement (p : ℕ) (h : Nat.Prime p) : ∀ (x : ℕ), (x ∣ p) → x = 1 ∨ x = p := by
  Hint "**Du**: Die einzigen Teiler einer Primzahl sind `1` und `p`, ist das
  nicht eine der möglichen Definitionen über `ℕ`?

  **Robo**: Doch, oder zumindest fast.
  Du kannst du mit `rw` und `Nat.prime_def_lt''` eine der Definitionen für `Nat.Prime` einsetzen

  **Du** Könnte ich nicht einfach `unfold Nat.Prime` sagen um mir das anzuschauen.

  **Robo**: Bloss nicht. Das ist so eine Definition, in die du besser nicht hineinschaust!
  `Nat.Prime p` ist als `Irreducible p` definiert, was wiederum anhand von Einheiten
  definiert ist… Da verlieren wir uns in Definition die wir im Moment gar nicht brauchen."
  rw [Nat.prime_def_lt''] at h
  rcases h with ⟨_, h₂⟩
  assumption

NewLemma Nat.prime_def_lt''

Conclusion "**Du**: Ich sehe, meine \"Definition\" hätte auch `1` als Primzahl deklariert. Gut,
dass wir das überprüft haben.

**Lehrer**: Und jetzt kommen wir zu dem, was mir Kopfschmerzen bereitet."
