import Mathlib
macro (name := ring) "ring" : tactic => `(tactic| first | ring1 | ring_nf)

/-
En aquest fitxer introduïm nocions elementals de límits de successions.
-/

/-
Ens serà molt útil la tàctica `linarith`, que demostra igualtats
i desigualtats en conjunts ordenats (com els reals).
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Practiquem una mica més:
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  sorry

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  sorry

/-
Una successió `u` és una funció de `ℕ` a `ℝ`, amb Lean ho escrivim
`u : ℕ → ℝ`
La definició que farem servir és:
-/

/-- Definició de "u tendeix a l" -/
def tendeix (u : ℕ → ℝ) (l : ℝ) := ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |u n - l| ≤ ε

variable {u v w : ℕ → ℝ}
variable {l l' : ℝ}

/- Si u és la successió constant l aleshores u tendeix a l.
Pista: `simp` simplifica `|l - l|` a `0` -/
example (h : ∀ n, u n = l) : tendeix u l := by
  sorry


/- Podem fer servir els lemes següents sobre el valor absolut:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

I sobre la desigualtat triangular

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
o
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
o la variant:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

/- Suposem `l > 0`. Si `u` tendeix `l`, aleshores
 `u n ≥ l/2` per `n` suficientment gran
 -/
example (h : tendeix u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  sorry


/-
Quan fem servir el màxim, tenim els lemes següents:

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

-/

-- Si `u` tendeix a `l` i `v` tendeix a `l'` aleshores `u+v` tendeix a `l+l'`
example (hu : tendeix u l) (hv : tendeix v l') :
    tendeix (u + v) (l + l') := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : N₁ ≤ n := by exact le_of_max_le_left hn
  rw [max_le_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]


/- El teorema del sàndvitx -/
example (hu : tendeix u l) (hw : tendeix w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    tendeix v l := by
  sorry


/- Per demostrar la unicitat del límit ens caldrà el següent lema:

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

-/

-- Demostrem la unicitat del límit amb un lema que podem reutilitzar.
lemma unique_limit : tendeix u l → tendeix u l' → l = l' := by
  sorry



/-
Afegim un parell de definicions més
-/

def no_decreixent (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def es_suprem (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : es_suprem M u) (h' : no_decreixent u) : tendeix u M := by
  sorry

/-
Considerem are subsuccessions. Ens cal definir una extracció, que no és més
que una successió estrictament creixent de naturals.
-/

def extraccio (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m


/-
Per demostrar el següent lema ens cal inducció.
-/

lemma id_le_extraccio' {φ : ℕ → ℕ} : extraccio φ → ∀ n, n ≤ φ n := by
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])



/-- Les extraccions tendeixen a infinit. -/
lemma extraccio_ge {φ : ℕ → ℕ} : extraccio φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  sorry

/- Un real `a` és un punt d'acumulació de la successió `u`
si `u` té una subsuccessió que tendeix a `a`
-/

def punt_acumulacio (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraccio φ ∧ tendeix (u ∘ φ) a

/-- Si `a` és un punt d'acumulació de `u` aleshores hi ha valors de
`u` arbitràriament propers a `a` per entrades arbitràriament grans. -/
lemma prop_punt_acumulacio {a : ℝ} :
  punt_acumulacio u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  sorry


/-- Si `u` tendeix a `l` aleshores les seves subsuccessions també. -/
lemma subseq_tendsto_of_tendsto' {φ : ℕ → ℕ} (h : tendeix u l) (hφ : extraccio φ) :
tendeix (u ∘ φ) l := by
  sorry

/-- Si `u` tendeix a `l` aleshores tot punt d'acumulació és igual a `l`. -/
lemma cluster_limit (a : ℝ) (hl : tendeix u l) (ha : punt_acumulacio u a) : a = l := by
  sorry

/-- Una successió de Cauchy -/
def esCauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, tendeix u l) → esCauchy u := by
  sorry

/-
Ara podem fer servir el lema
 prop_punt_acumulacio : punt_acumulacio u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : esCauchy u) (hl : punt_acumulacio u l) : tendeix u l := by
  sorry

