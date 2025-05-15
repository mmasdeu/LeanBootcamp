import Mathlib.Data.Complex.Exponential
macro (name := ring) "ring" : tactic => `(tactic| first | ring1 | ring_nf)
open Real


/-
# Càlcul

## La tàctica `ring`

Un dels primers tipus de demostracions que ens trobem és la "demostració per càlcul".
Potser no sona com una demostració, però en realitat s'estan utilitzant
lemes que expressen propietats de les operacions amb nombres
(commutativa, associativa, distributiva,...).
Evidentment, normalment no volem invocar aquests lemes explícitament,
així que la llibreria `mathlib` disposa d'una tàctica
anomenada `ring` que s'encarrega de demostrar igualtats que es poden deduir aplicant
les propietats dels anells commutatius.

També hi ha les tàctiques `abel` que només fa servir propietats de grups abelians, o
`noncomm_ring` per anells no commutatius...
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring

/- Substitueix la paraula `sorry` per una demostració. En aquest cas, la demostració és simplement `ring`.
Després de demostrar alguna cosa, veuràs un petit missatge "No goals", que indica que
la demostració ha finalitzat.
-/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  -- sorry
  ring
  -- sorry

/- En  l'exemple anterior, fixa't bé on Lean mostra els parèntesis (s'intenta evitar-ne l'ús innecessari).
La tàctica `ring` coneix la propietat associativa de la multiplicació, però de vegades
és útil entendre que les operacions binàries realment ho són, i una expressió com
`a*b*c` es llegeix com `(a*b)*c` per Lean, i el fet que això sigui igual a `a*(b*c)` és
una lemma que `ring` quan li cal.
-/

/-
## La tàctica de reescriptura (`rw`)

Ara veurem com calcular utilitzant hipòtesis que relacionen els nombres implicats.
Això utilitza la propietat fonamental de la igualtat: si dos
objectes matemàtics A i B són iguals, llavors en qualsevol enunciat que impliqui A, es pot substituir A
per B. Aquesta operació es diu reescriptura, i la tàctica bàsica de Lean per fer-ho és `rw`:
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  ring

/-
La tàctica `rw` necessita que se li indiqui cada pas de reescriptura. Més endavant veurem tàctiques
més potents que automatitzen els passos tediosos.

Es poden fer diverses reescriptures en una sola instrucció:
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h, h']
  ring

/-
Posant el cursor entre `h` i `h'` es veure l'estat de la demostració intermèdia.

Observeu el subtil canvi de color de fons a l'estat de la tàctica: en verd el que és nou,
i en vermell el que està a punt de canviar.

-/

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  -- sorry
  rw [h', h]
  ring
  -- sorry

/- ## Reescriure amb una lema

En els exemples anteriors, reescrivíem l'objectiu amb una hipòtesi local. Però també podem
utilitzar lemes que haguem demostrar prèviament, o que estiguin a la llibreria.
Per exemple, demostrarem una lema sobre l'exponenciació.
Com que `ring` només coneix axiomes dels anells,
no pot treballar amb exponenciació.
Pel següent resultat, reescriurem dues vegades amb el lema
`exp_add x y`, que és una demostració de `exp(x+y) = exp(x) * exp(y)`.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add (a + b) c]
  rw [exp_add a b]

/-
Observeu també que després de la segona `rw` l'objectiu esdevé
`exp a * exp b * exp c = exp a * exp b * exp c`, i Lean declara immediatament que la demostració ha finalitzat.

Si no proporcionem arguments als lemes, Lean reescriurà la primera subexpressió coincident.
En el nostre exemple això és suficient:
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add, exp_add]

/-
Però de vegades cal més control (TODO)
-/
example (a b c d : ℝ) : exp (a * c + b * c) * exp (c + d) = exp (a * c + b * c) * exp c * exp d := by
  rw [exp_add, exp_add]
  ring


/-
Fem un exercici, on també cal utilitzar
`exp_sub x y : exp(x-y) = exp(x) / exp(y)` i `exp_zero : exp 0 = 1`.

Recorda que `a + b - c` vol dir `(a + b) - c`.

Pots usar `ring` o reescriure amb `mul_one x : x * 1 = x` per simplificar el denominador
al costat dret.
-/

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  -- sorry
  rw [exp_sub, exp_add, exp_zero, mul_one]
  -- sorry

/-
## Reescriure d'esquerra a dreta

Com que la igualtat és simètrica, també podem substituir el costat dret d'una
i igualtat pel costat esquerre utilitzant `←`, com en l'exemple següent.
-/
example (a b c d e: ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']

/-
Quan vegis en un fitxer Lean un símbol que no tens al teclat, com `←`,
posa el cursor a sobre per veure un missatge emergent que t'indicarà com escriure'l.
En el cas de `←`, escriu `\l `, o sigui, barra invertida + l + espai.

Aquesta reescriptura d'esquerra a dreta fa referència al costat de la igualtat que volem
*utilitzar*, no al costat que volem *demostrar*. `rw [← h]` substituirà el costat dret
per l'esquerre, buscant `b + c` i canviant-lo per `a`.
-/

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  -- sorry
  rw [← h', ← h, ← h'']
  -- sorry

/- ## Reescriure en una hipòtesi local

També podem reescriure en una hipòtesi del context local, utilitzant per exemple
  `rw [exp_add x y] at h`
per substituir `exp(x + y)` per `exp(x) * exp(y)` a la hipòtesi `h`.

La tàctica `exact` et permet proporcionar un terme de prova explícit per demostrar l'objectiu actual.
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = d) : c = d*a + d := by
  rw [h'] at h
  -- La nostra hipòtesi `h` és ara exactament el que volem demostrar
  exact h

/- ## Presentació de càlculs amb `calc`

El que hem escrit a l'exemple anterior està molt allunyat del que escriuríem en
paper. Ara veurem com obtenir una presentació més natural (i també tornar a utilitzar `ring`
en lloc de lemas explícits).
Després de cada `:=`, l'objectiu és demostrar la igualtat amb la línia anterior
(o amb el costat esquerre de la primera línia).
Revisa amb cura i posa el cursor després de cada `by` per veure l'estat de la tàctica.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring

/-
Fem alguns exercicis utilitzant `calc`.
-/

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by /- inline sorry -/rw [h]/- inline sorry -/
              _ = exp ((b + b) + (c + c))           := by /- inline sorry -/ring/- inline sorry -/
              _ = exp (b + b) * exp (c + c)         := by /- inline sorry -/rw [exp_add]/- inline sorry -/
              _ = (exp b * exp b) * (exp c * exp c) := by /- inline sorry -/rw [exp_add, exp_add]/- inline sorry -/
              _ = (exp b) ^ 2 * (exp c)^2           := by /- inline sorry -/ring/- inline sorry -/

/-
En la pràctica, en escriure una prova com aquesta, pot ser convenient:
* Pausar l'actualització de l'estat de la tàctica a VScode clicant el botó de Pausa
dalt a la dreta del panell d'Infoview de Lean.
* Escriure tot el càlcul, acabant cada línia amb ":= ?_"
* Reprendre l'actualització clicant el botó de Reproduir i completar les proves.

Els guions baixos s'han de col·locar sota el costat esquerre de la primera línia del `calc`.
No cal alinear els signes igual i `:=` però fa que es vegi ordenat.
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by
  -- sorry
  calc
    c = d*a + b   := by rw [h]
    _ = d*a + a*d := by rw [h']
    _ = 2*a*d     := by ring
  -- sorry
