import TestGame.Metadata
import Mathlib.Tactic.Tauto

Game "TestGame"
World "Proposition"
Level 1

Title "Automatisierung"

Introduction
"
Durch eine unvorhergesehene und nicht-kanonische Singularität in der Raumzeit
bist Du ausversehen in ein Paralleluniversum gestolpert. Wie es aussieht, gibt es kein zurück.
Richte Dich besser darauf ein, hier bleiben und Dich zurechtzufinden zu müssen.

Wie es aussieht, gibt es hier viele nette kleine Planeten. Alle bewohnbar, und bis zu
sieben Sonnenuntergänge täglich inklusive. Nur werden sie allesamt von Formalosophen bewohnt,
seltsamen Wesen mit ausgefallenen mathematischen Obsessionen. Und dummerweise hat sich
herumgesprochen, dass Du in Deinem früheren Universum Mathematiker warst. Du wirst hier
keine Ruhe finden, solange Du nicht lernst, ihren unablässigen Wissensdurst zu stillen.

Es gibt nur zwei Schwierigkeiten: Erstens haben die Formalosophen allem Anschein nach
überhaupt kein tieferes mathematisches Verständnis, und zweitens kommunizieren Sie über Mathematik
exklusiv in einem Dir fremden Dialekt, den sie Leanish [liːnɪʃ] nennen. 

Zum Glück hat Robo mit Dir das Universum gewechselt.
Robo, das ist Dein kleiner SmartElf. Robo ist war auch nicht die mathematische Leuchte, die Du Dir in dieser Situation gewünscht hättest, aber es scheint, er hat irgendwo Leanish gelernt.  Und das ist Gold wert.

----

Gerade seid Ihr auf Königin Logisindes Planeten. Sie kommt ohne Umschweife zum Punkt:

**Logisinde**  Werte Wesen aus fremden Welten, gestatten Sie eine Frage.  Warum gilt …  

Und er kritzelt etwas auf ein Stück Papier:  oben ein paar Annahmen, unten eine Schlussfolgerung.  
Dazwischen sollst Du offenbar einen Beweis eintragen.  
Du siehst Robo hilflos an.  
"

Statement
    (A B C : Prop) :
    ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto


Hint
"**Robo**  Das ist ganz einfach.  Mit `A B C : Prop` meint er:  `A`, `B` und `C` sind irgendwelche Aussagen (*propositions*).  Und mit `→` meint er ⇒, also “impliziert”. Die anderen Symbole kennst Du, oder?  

**Du** Ehhm, ja.  Aber da muss ich jetzt trotzdem erst einmal überlegen.

**Robo** (flüsternd) Behaupte doch einfach, dass sei eine Tautologie.  

**Du** Ernsthaft? 

**Robo** Ja.  Schreib einfach `tauto`.

**Robo** Mach schon …
"

Conclusion
"
**Logisinde** (etwas konsterniert)  Ja, das ist streng genommen richtig.  Aber glaubt bloß nicht, dass Ihr damit auf *diesem* Planeten viel weiterkommt!  Meine Untertanen verstehen `tauto` nicht.  Da müsst Ihr Euch schon etwas mehr anstrengen.
"

NewTactics tauto
