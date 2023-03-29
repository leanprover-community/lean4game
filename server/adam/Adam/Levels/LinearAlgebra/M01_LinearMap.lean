import Adam.Metadata

import Mathlib.Data.Real.Basic           -- definiert `ℝ`
import Mathlib.Algebra.Module.LinearMap -- definiert `→ₗ`
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

Game "Adam"
World "Basis"
Level 1

notation "ℝ²" => Fin 2 → ℝ

Title "Lineare Abbildung"

Introduction
"
Sei `R` ein Ring und `V W` zwei `R`-Moduln. Eine `R`-lineare Abbildung wird in Lean
folgendermassen geschrieben: `V →ₗ[R] W` (`\\to` + `\\_l`).

Man erstellt eine lineare Abbildung aus einer Funktion `f : V → W` zusammen mit den beweisen,
dass `f` Addition und Skalarmultiplikation erhält,
i.e. `f (x + y) = f x + f y` und `f (r • x) = r • f x`.

Hier definieren wir zum Beispiel die Null-Abbildung, die einfach alles auf `0` sendet:

```
variables {R V W : Type*} [ring R] [add_comm_monoid V] [add_comm_monoid W]
[module R V] [module R W]

def my_zero_map : V →ₗ[R] W :=
  { to_fun := λ x, 0,
    map_add' :=
    begin
      intros,
      simp,
    end,
    map_smul' :=
    begin
      intros,
      simp,
    end }
```

"

Statement
"
Zeige dass die Abbildung

```
  ℝ² → ℝ²
  (x, y) ↦ (5x + 2y, x - y)
```

`ℝ`-linear ist.
"
    : ℝ² →ₗ[ℝ] ℝ² :=
  { toFun := fun v ↦ ![5 * (v 1) + 2 * (v 2), (v 1) - (v 2)]
    map_add' := by
      -- Wähle zwei beliebige Vektoren mit `intros` aus.
      intro x y
      -- Das Lemma `funext` sagt das zwei Funktionen identisch sind, wenn sie für jeden Wert ereinstimmen:
      -- `(∀ i, f i = g i) → f = g`. Da Vektoren einfach als Funktionen von einem Indexset codiert sind,
      -- kannst du mit `apply funext` komponentenweise rechnen.
      funext i
      -- Mit `fin_cases i` kannst du pro möglichem Wert von `i` ein Goal auftun. D.h. im ersten gilt dann
      -- `i = 0`, im zweiten Goal `i = 1`.
      fin_cases i
      -- Dies ist der Fall `i = 0`.
        -- Das Goal hat jetzt Terme der Form `![a, b] 0`, und du weisst was das sein sollte, nämlich
        -- einfach der erste Komponent `a`. Die Taktik `simp` ist für solche Vereinfachungnen gedacht.
      · simp
        -- Einfache Rechenaufgaben hast du ja bereits gemacht.
        -- `ring` oder `linarith` machen dies automatisch für dich.
        ring
      -- Und jetzt noch den Fall `i = 1`.
      · simp
        ring
    map_smul' := by
      intro r x
      funext i
      fin_cases i
        -- Bemerkung: Wenn du jetzt `simp` brauchst, macht es sogar noch mehr als vorher.
        -- Skalarmultiplikation ist einfach als komponentenweise Multiplikation definiert.
        -- Entsprechend braucht `simp` ein Lemma `smul_eq_mul : a • b = a * b`.
      · simp
        ring
      · simp
        ring
  }
