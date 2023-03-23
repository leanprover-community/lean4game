import TestGame.Metadata
import Std.Tactic.RCases
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring
import Mathlib

import TestGame.ToBePorted

Game "TestGame"
World "Contradiction"
Level 4

Title "Per Widerspruch"

Introduction
"
*Oddeus* Geht zu einem Regal mit vielen Dokumenten und beginnt zu suchen.

**Oddeus**: Ich hab's gleich. Hier ist eine Notiz meiner Gelehrter, die mir
mit solchen kryptischen Nachrichten helfen wollten.

Auf dem Pergament steht das ein Lemma mit dem Namen `not_imp_not`:
"

Statement not_imp_not (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  Hint "**Du**: Ich glaube, dafür kenn ich das meiste schon."
  Hint (hidden := true) "**Robo**: Fang doch mal mit `constructor` an."
  constructor
  intro h b
  by_contra a
  Hint "**Robo**: Zur Erinnerung, hier würde ich mit `suffices g : B` einen Widerspruch
  herbeiführen."
  suffices b : B
  contradiction
  apply h
  assumption
  intro h a
  Hint "**Robo**: Hier würde ich ebenfalls einen Widerspruch anfangen."
  by_contra b
  Hint (hidden := true) "**Robo**: `suffices g : ¬ A` sieht nach einer guten Option aus."
  suffices g : ¬ A
  contradiction
  apply h
  assumption

DisabledTactic rw
DisabledLemma not_not

Conclusion "**Du**: Und wie hilft uns das jetzt, was steht denn in dem Brief?"
