import Mathlib
macro (name := ring) "ring" : tactic => `(tactic| first | ring1 | ring_nf)

/- # Implicacions

## Utilitzant implicacions

Lean denota la implicació amb el símbol `→` en lloc de `⇒` perquè considera una prova
de `P → Q` com una funció que envia qualsevol prova de `P` a una prova de `Q`

Per exemple, donat un nombre real `a`, el lema `sq_pos_of_pos` afirma `0 < a → 0 < a^2`.
Així, en la següent demostració s'aplica la "funció" `sq_pos_of_pos` a la hipòtesi `ha`.
-/

example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by
  exact sq_pos_of_pos ha

/-
Suposem que volem demostrar `0 < (a^2)^2`. Podem fer-ho aplicant `sq_pos_of_pos`
dues vegades.
-/
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  -- sorry
  exact sq_pos_of_pos (sq_pos_of_pos ha)
  -- sorry

/-
La demostració que hem fet s'anomena d'estil "directe":
del fet que `0 < a` en traiem `0 < a^2`, i d'aquí en traiem
el resultat final.

Però també podem fer-ho d'una altra manera, utilitzant la tàctica `apply`
-/

example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  apply sq_pos_of_pos -- Gràcies a `sq_pos_of_pos`, n'hi ha prou en demostrar `0 < a^2`
  apply sq_pos_of_pos -- Gràcies a `sq_pos_of_pos`, n'hi ha prou amb demostrar `0 < a`
  exact ha -- exactament, la hipòtesi `ha` ens ho garanteix.

/-
Intenteu fer el següent exercici utilitzant el lema `add_pos : 0 < x → 0 < y → 0 < x + y`.
Quan apliqueu `add_pos`, us apareixeran dos objectius, que haureu de demostrar per separat.
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  -- sorry
  apply add_pos
  . apply sq_pos_of_pos
    exact ha
  · apply sq_pos_of_pos
    exact hb
  -- sorry

/-
També podeu donar una demostració amb raonament directe, utilitzant la tàctica `have`.
Per anunciar una afirmació intermèdia utilitzem:

  `have un_nom : un_enunciat
   · demostració
     segona tàctica de la demostració
   continua la prova
  `

Això fa aparèixer un nou objectiu: demostrar l'afirmació que hem fet.
Un cop la demostració estigui feta, l'afirmació esdevé disponible
amb el nom `un_nom`.
Si la demostració és una única tàctica `exact`, llavors es pot seguir l'esquema

  `have un_nom : un_enunciat := demostració
   continua la prova
  `
-/

example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  have h2 : 0 < a^2    -- `0 < a^2` serà un nou subobjectiu
  · apply sq_pos_of_pos  -- comencem demostrant el subobjectiu
    exact ha             -- cal mantenir la indentació
  exact sq_pos_of_pos h2 -- un cop acabat el subobjectiu, seguim amb la demostració

/- Feu la següent prova amb raonament directe -/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  -- sorry
  have h2a : 0 < a^2
  · exact sq_pos_of_pos ha
  have h2b : 0 < b^2 := sq_pos_of_pos hb -- versió curta
  exact add_pos h2a h2b
  -- sorry


/- ## Demostrar implicacions

Per demostrar una implicació, necessitem assumir la premissa i demostrar la conclusió.
Això es fa utilitzant la tàctica `intro`.
L'exercici anterior també estava demostrant
la implicació `a > 0 → (a^2)^2 > 0`, però la premissa ja estava introduïda.
-/

example (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb -- Es poden escollir noms arbitraris
  exact add_pos ha hb

/- Demostreu ara el següent enunciat lògic.
**Important** `p → q → r` vol dir `p → (q → r)`.
-/
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by
  -- sorry
  intro h1 h2 h3
  apply h2 h3
  exact h1 h3
  -- sorry


/- # Equivalències

## Utilitzar equivalències per reescriure enunciats

L'operació anàloga a reescriure igualtats de predicats seria
reescriure utilitzant equivalències.
Això també es fa utilitzant la tàctica `rw`.
Lean utilitza `↔` per denotar equivalència en lloc de `⇔`.

En els següents exercicis utilitzarem el lema:

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`
-/

example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [← sub_nonneg]
  have clau : (c + b) - (c + a) = b - a := by ring -- versió curta
  rw [clau] -- Ara podem fer servir `clau`. Aquest `rw` és com el que ja sabíem.
  rw [sub_nonneg] -- Tornem a reescriure `sub_nonneg`.

/-
Fem una variant:
-/

example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  -- sorry
  rw [← sub_nonneg]
  ring
  rw [sub_nonneg]
  -- sorry

/-
Aquest lema ja és a Mathlib, s'anomena `add_le_add_iff_right`:

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

Ho hem de pensar així:
"`add_le_add_iff_right` és una funció que envia un nombre `c`
a la demostració de l'equivalència `a + c ≤ b + c ↔ a ≤ b`".

Fem-lo servir en la següent demostració:
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by /- inline sorry -/ring/- inline sorry -/
    _ ≤ a + b := by /- inline sorry -/rw [add_le_add_iff_right b] ; exact ha/- inline sorry -/

/-
## Una equivalència són dues implicacions

Podem fer una demostració alternativa fent servir una direcció de l'equivalència
anterior. Si `h : P ↔ Q`, llavors `h.1 : P → Q` i `h.2 : Q → P`.
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by /- inline sorry -/exact (add_le_add_iff_right b).2 ha/- inline sorry -/


/-
## Demostrar equivalences

Per demostrar una equivalència, podeu utilitzar `rw` fins que
l'objectiu sigui la tautologia `P ↔ P`,
de la mateixa manera que es pot fer amb igualtats.

També podeu demostrar per separat les dues implicacions utilitzant
la tàctica `constructor`.

A continuació hi ha un exemple.
Si poseu el cursor després de `constructor`, veureu dos objectius,
un per a cada direcció.

Lean fa el seguiment dels objectius per vosaltres,
assegurant-se que els resolgueu tots.
El punt volat `·` manté la demostració de cada objectiu separada.
-/

example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
          _ = b^2 + 0                  := by rw [h]
          _ = b^2                      := by ring
  · intro h
    calc
      (a-b)*(a+b) = a^2 - b^2  := by ring
                _ = b^2 - b^2  := by rw [h]
                _ = 0          := by ring


/- Proveu de fer aquest exercici final. -/

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  -- sorry
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    calc
      a = b - (b - a) := by ring
      _ = b - 0       := by rw [h]
      _ = b           := by ring
  -- sorry
