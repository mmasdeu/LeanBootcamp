import Mathlib
macro (name := ring) "ring" : tactic => `(tactic| first | ring1 | ring_nf)


open Function

/- # Quantificador universal (∀)

Sigui `P` un predicat sobre un tipus `X`. Això significa que per a cada objecte
matemàtic `x` de tipus `X`, obtenim un enunciat matemàtic `P x`.
En Lean, `P x` té tipus `Prop`.

Lean entén una demostració `h` de `∀ x, P x` com una funció que envia qualsevol
`x : X` a una demostració `h x` de `P x`.

Per tal de demostrar `∀ x, P x`, utilitzem `intro x` per fixar un objecte arbitrari
amb tipus `X`, i l'anomenem `x` (`intro` significa "introduir").

També cal notar que no necessitem donar el tipus de `x` en l'expressió `∀ x, P x`
sempre que el tipus de `P` sigui clar per a Lean, que llavors pot inferir el tipus de `x`.

Definim un predicat per jugar amb `∀`.
-/

def funcio_parell (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
La tàctica `unfold` serveix per substituir les definicions com la d'aquí a sobre.
La tàctica `rfl` (reflexivitat) demostra igualtats que són certes "per definició".
-/

example (f g : ℝ → ℝ) (hf : funcio_parell f) (hg : funcio_parell g) : funcio_parell (f + g) := by
  unfold funcio_parell at hf
  unfold funcio_parell at hg
  unfold funcio_parell
  intro x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl


/-
Algunes tàctiques, com `apply`, `exact`, `rfl` and `calc`
saben llegir a través de les definicions, i per tant no cal `unfold` en
aquests casos.

En canvi, altres tàctiques com ara `rw` and `ring`
no saben veure-hi a través de les definicions. És per això que cal una línia extra
en el bloc `calc` d'abans.

A més, quan se li demana de reescriure `hf`, no cal dir-li amb quin paràmetre.

Aquí tenim doncs una forma més compacta de la demostració anterior:
-/

example (f g : ℝ → ℝ) : funcio_parell f → funcio_parell g → funcio_parell (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]

/-
Exercicis
-/

example (f g : ℝ → ℝ) (hf : funcio_parell f) : funcio_parell (g ∘ f) := by
  -- sorry
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x))   := by rfl
               _ = g (f x)      := by rw [hf]
  -- sorry

def creixent (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

/- Demostració directa -/
example (f g : ℝ → ℝ) (hf : creixent f) (hg : creixent g) :
    creixent (g ∘ f) := by
  -- Siguin x₁ and x₂ tals que x₁ ≤ x₂
  intro x₁ x₂ h
  -- Com que f és creixent, f x₁ ≤ f x₂.
  have pas₁ : f x₁ ≤ f x₂ := hf x₁ x₂ h -- provem d'esborrar els paràmetres
  -- Com que g és creixent, tenim g (f x₁) ≤ g (f x₂).
  exact hg _ _ pas₁


/-
Ens hauríem pogut estalviar el `pas₁`:
-/
example (f g : ℝ → ℝ) (hf : creixent f) (hg : creixent g) :
    creixent (g ∘ f) := by
  intro x₁ x₂ h
  exact hg _ _ (hf x₁ x₂ h)

/-
Demostració inversa (fent servir `apply`):
-/

example (f g : ℝ → ℝ) (hf : creixent f) (hg : creixent g) :
    creixent (g ∘ f) := by
  -- Siguin x₁ and x₂ tal que x₁ ≤ x₂
  intro x₁ x₂ h
  -- Cal veure (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Com que g és creixent, n'hi ha prou amb veure f x₁ ≤ f x₂
  apply hg
  -- Com que f és creixent, n'hi ha prou amb veure x₁ ≤ x₂
  apply hf
  -- Acabem
  exact h

/- # Com trobar resultats a mathlib

Per aplicar els resultats que ja existeixen a Mathlib, Lean té algunes tàctiques
que ens ajuden a no haver-ne de recordar tots els noms.

* `simp` simplifica expressions complicades.
* `apply?` troba lemes a Mathlib.
-/

/- Fem servir `simp` per simplificar l'expressió inicial. -/
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  -- sorry
  simp
  exact hx
  -- sorry

/- Fem servir `apply?` per trobar un lema que creiem que hauria d'existir.
-/

example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  -- sorry
  -- fent servir `apply?` trobem:
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f
  -- sorry

/-
## Conjuncions

Amb Lean, la conjunció de predicats `P` i `Q` s'escriu `P ∧ Q`.

Es pot fer servir igual que amb el si i només si:
* Si `h : P ∧ Q`, llavors `h.1 : P` i `h.2 : Q`.
* Per demostrar `P ∧ Q` fem servir la tàctica `constructor`.

A més, podem decomposar les conjuncions i les equivalències amb `rcases`:
* Si `h : P ∧ Q`, la tàctica `rcases h with ⟨hP, hQ⟩`
  dona lloc a dues hipòtesis noves `hP : P` i `hQ : Q`.
* Si `h : P ↔ Q`, la tàctica `rcases h with ⟨hPQ, hQP⟩`
  dona lloc a les hipòtesis `hPQ : P → Q` i `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq

/- Si les dues demostracions són curtes, es poden posar a la vegada: -/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩

/- Exercici: -/

example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  -- sorry
  constructor
  · intro h h'
    rcases h' with ⟨hp, hq⟩
    exact h hp hq
  · intro h hp hq
    apply h
    constructor
    · exact hp
    · exact hq
  -- sorry

/- El Lean pot demostrar tot això automàticament, amb la tàctica `tauto`. -/
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  tauto

/- # Disjuncions

La disjunció de predicats s'escriu `P ∨ Q`.

Per demostrar `P ∨ Q`, haurem de decidir quin dels dos predicats volem
(o podem) demostrar. Aleshores les tàctiques `left` o `right` ens permeten
sel·leccionar un dels dos objectius.
-/

example (a b : ℝ) (h1 : a + b = 3) (h2 : a - b = 1) : a = 2 ∨ a = 1 := by
  sorry

/-
Si hi ha una disjunció en les hipòtesis, podem fer una demostració per casos.

`rcases h with hP | hQ`

trenca la hipòtesi `h : P ∨ Q` en dues branques. La primera branca
anomena la hipòtesi que `P` és certa com a `hP`, i la segona fa el mateix
amb `hQ : Q`.
-/

example (a b : ℝ) (h : a = 2 ∨ a = -2) : a^2 + 1 = 5 := by
  sorry



/- # Quantificadors existencials

Per tal de demostrar `∃ x, P x`, donem algun `x₀` fent servir la tàctica `use x₀` i
després demostrem `P x₀`. Aquest `x₀` pot ser un objecte del context local
o una expressió més complicada.n
-/
example (m : ℕ) : ∃ n : ℕ, 8 + 2*m = 2*n + m + m := by
  use 4
  ring


/-
Per utilitzar una hipòtesi del tipus `h : ∃ x, P x`, fem servir `rcases`
per obtenir un `x₀` amb la propietat indicada. També podem escriure
`obtain ⟨k₀, hk₀⟩ := h`.
n-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  -- Sigui k₀ tal que n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- Ara podem substituir k₀.
  rw [hk₀]
  -- I acabem amb un lema que ja existeix a Mathlib
  exact Nat.succ_pos k₀

/-
Practiquem amb la divisibilitat a ℤ **El símbol "∣" no és ASCII!**

Per definició, `a ∣ b ↔ ∃ k, b = a*k`, per tant es pot demostrar `a ∣ b` amb
la tàctica `use`.
-/

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  -- sorry
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  use k*l
  calc
    c = b*l   := hl
    _ = (a*k)*l := by rw [hk]
    _ = a*(k*l) := by ring
  -- sorry


/-
Podem fer més exercicis amb funcions injectives i exhaustives
-/

variable {X Y Z : Type}
def injectiva (f : X → Y) := ∀ x y, (f x = f y) → x = y
def exhaustiva (f: X → Y) := ∀ y, ∃ x, f x = y


example (f : X → Y) (g : Y → Z) (hf : injectiva f) (hg : injectiva g) :
  injectiva (g ∘ f) := by
  -- sorry
  intro x y h
  -- Com que f és injectiva, n'hi ha prou amb veure f x = f y
  apply hf
  -- Com que g és injectiva, n'hi ha prou amb veure x = y
  apply hg
  -- Acabem
  exact h
  -- sorry

example (f : X → Y) (g : Y → Z) (hf : exhaustiva f) (hg : exhaustiva g) :
  exhaustiva (g ∘ f) := by
  -- sorry
  intro z
  -- Com que g és exhaustiva, n'hi ha prou amb veure g x = z
  obtain ⟨y, hy⟩ := hg z
  -- Com que f és exhaustiva, n'hi ha prou amb veure f x = y
  obtain ⟨x, hx⟩ := hf y
  -- Acabem
  use x
  calc
    g (f x) = g y   := by rw [hx]
    _ = z          := by rw [hy]
  -- sorry

example (f : X → Y) (g : Y → Z) (hgf : injectiva (g ∘ f)) : injectiva f := by
  -- sorry
  intro x y h
  -- Com que hgf és injectiva, n'hi ha prou amb veure g (f x) = g (f y)
  apply hgf
  simp
  rw [h]
  -- sorry

example (f : X → Y) (g : Y → Z) (hgf : exhaustiva (g ∘ f)) : exhaustiva g := by
  -- sorry
  intro z
  -- Com que hgf és exhaustiva:
  obtain ⟨x, hx⟩ := hgf z
  use f x
  exact hx
  -- sorry

/- Acabem donant contraexemples coneguts dels recíprocs -/

def f : ℕ → ℕ := λ x ↦ x + 1
def g : ℕ → ℕ := λ x ↦ x - 1

#eval f 2
#eval g 2
#eval g 0 -- !!!


example : (injectiva (g ∘ f) ∧ ¬ injectiva g) := by
  -- sorry
  constructor
  · intro x y h
    simp [f, g] at h
    rw [h]
  · simp [injectiva]
    use 0
    use 1
    simp [g]
  -- sorry

example : (exhaustiva (g ∘ f) ∧ (¬ exhaustiva f)) := by
  -- sorry
  constructor
  · intro y
    simp [f, g]
  · intro h
    unfold exhaustiva at h
    obtain ⟨x, hx⟩ := h 0
    simp [f] at hx
  -- sorry
