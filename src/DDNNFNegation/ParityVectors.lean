import DDNNFNegation.OuterMatrix
import TutorialBox

/-!
# Characters of the binary group

Parity signs define real characters of the finite binary group. Their
multiplication and orthogonality identities provide a basis for the
sum-dependent matrix. The local identities here also factor the
character sums used to calculate its eigenvalues.
-/

namespace DDNNFNegation

open scoped BigOperators

section ParityVectors

/-! ## Parity vectors on the alphabet -/

/-- The dot product `ξ·z = ξ₁z₁ + ξ₂z₂ + ξ₃z₃ + ξ₄z₄ mod 2` on the
four-bit alphabet. -/
def bilin (ξ t : GadgetVector) : ZMod 2 :=
  ξ.1.1 * t.1.1 + ξ.1.2 * t.1.2 + ξ.2.1 * t.2.1 + ξ.2.2 * t.2.2

/-- The integer sign `(-1)^{ξ·t}`. -/
def signZ (ξ t : GadgetVector) : ℤ :=
  if bilin ξ t = 0 then 1 else -1

private theorem signZ_zero : ∀ ξ : GadgetVector, signZ ξ 0 = 1 := by decide

private theorem signZ_add :
    ∀ ξ s t : GadgetVector, signZ ξ (s + t) = signZ ξ s * signZ ξ t := by
  decide

private theorem signZ_add_left :
    ∀ ξ η t : GadgetVector, signZ (ξ + η) t = signZ ξ t * signZ η t := by
  decide

private theorem signZ_comm : ∀ ξ t : GadgetVector, signZ ξ t = signZ t ξ := by
  decide

private def bitVector (k : Fin 4) : GadgetVector :=
  ![((1, 0), (0, 0)), ((0, 1), (0, 0)), ((0, 0), (1, 0)), ((0, 0), (0, 1))] k

private theorem exists_sign_flip : ∀ ξ : GadgetVector, ξ ≠ 0 →
    ∃ k : Fin 4, signZ ξ (bitVector k) = -1 := by decide

-- Pair each input with the input obtained by flipping one bit where ξ is 1.
private theorem sum_signZ :
    ∀ ξ : GadgetVector, (∑ t, signZ ξ t) = if ξ = 0 then 16 else 0 := by
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    decide
  · rw [if_neg hξ]
    obtain ⟨k, hk⟩ := exists_sign_flip ξ hξ
    have hcancel : (∑ t, signZ ξ t) = -(∑ t, signZ ξ t) := by
      calc
        (∑ t, signZ ξ t) = ∑ t, signZ ξ (t + bitVector k) :=
          (Equiv.sum_comp (Equiv.addRight (bitVector k)) (signZ ξ)).symm
        _ = ∑ t, signZ ξ t * (-1) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [signZ_add, hk]
        _ = -(∑ t, signZ ξ t) := by rw [← Finset.sum_mul]; ring
    omega

/-- The parity vector `par_ξ` of the tutorial: its entry at `z` is
`(-1)^{ξ·z}`. -/
@[tutorial_box "def:tutorial-parities"]
noncomputable def parity (ξ t : GadgetVector) : ℝ :=
  ((signZ ξ t : ℤ) : ℝ)

/-- The parity vector at the zero parameter is the all-ones vector. -/
theorem parity_trivial (t : GadgetVector) :
    parity (0 : GadgetVector) t = 1 := by
  have h : signZ (0 : GadgetVector) t = 1 := by
    rw [signZ_comm]
    exact signZ_zero t
  rw [parity, h]
  norm_num

/-- The parity vector is multiplicative in its argument. -/
theorem parity_add (ξ s t : GadgetVector) :
    parity ξ (s + t) = parity ξ s * parity ξ t := by
  rw [parity, parity, parity, signZ_add]
  push_cast
  ring

/-- The parity vectors of two parameters multiply to the parity vector of
their sum. -/
theorem parity_add_left (ξ η t : GadgetVector) :
    parity (ξ + η) t = parity ξ t * parity η t := by
  rw [parity, parity, parity, signZ_add_left]
  push_cast
  ring

/-- The local parity pairing is symmetric in its parameter and argument. -/
theorem parity_comm (ξ t : GadgetVector) : parity ξ t = parity t ξ := by
  rw [parity, parity, signZ_comm]

/-- The entries of the parity vector of a nonzero parameter sum
to zero, and those of the trivial parameter to `16`. -/
theorem sum_parity (ξ : GadgetVector) :
    ∑ t, parity ξ t = if ξ = 0 then 16 else 0 := by
  have h := sum_signZ ξ
  simp only [parity]
  rw [← Int.cast_sum, h]
  split_ifs <;> norm_num

/-- The sixteen parity vectors are pairwise orthogonal on the
sixteen-element alphabet. -/
theorem parity_orthogonal (ξ η : GadgetVector) :
    ∑ t, parity ξ t * parity η t = if ξ = η then 16 else 0 := by
  have hsum : ∑ t, parity ξ t * parity η t = ∑ t, parity (ξ + η) t := by
    apply Finset.sum_congr rfl
    intro t _ht
    rw [parity_add_left]
  rw [hsum, sum_parity]
  have hiff : ξ + η = 0 ↔ ξ = η := by
    constructor
    · intro h
      have h2 : η + η = 0 := gadget_add_self η
      calc
        ξ = ξ + η + η := by rw [add_assoc, h2, add_zero]
        _ = η := by rw [h, zero_add]
    · intro h
      rw [h]
      exact gadget_add_self η
  by_cases h : ξ = η
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-- Row form of the orthogonality: for two fixed entries `x, y`, summing
over the parameters. -/
theorem parity_row_orthogonal (x y : GadgetVector) :
    ∑ ξ, parity ξ x * parity ξ y = if x = y then 16 else 0 := by
  have h : ∑ ξ, parity ξ x * parity ξ y = ∑ ξ, parity x ξ * parity y ξ := by
    apply Finset.sum_congr rfl
    intro ξ _hξ
    rw [parity_comm ξ x, parity_comm ξ y]
  rw [h, parity_orthogonal]

end ParityVectors

section GlobalParity

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The global parity vectors -/

/-- The global parity vector of a full parameter `ξ ∈ G`: the product of
the local parity signs, `par_ξ(x) = ∏_u par_{ξ_u}(x_u)`. -/
@[tutorial_box "def:tutorial-parities"]
noncomputable def globalParity (ξ : Ω → GadgetVector) (x : Ω → GadgetVector) : ℝ :=
  ∏ u, parity (ξ u) (x u)

omit [DecidableEq Ω] in
/-- The parity vector of the parameter `0` is the all-ones vector. -/
theorem globalParity_zero : globalParity (0 : Ω → GadgetVector) = 1 := by
  funext x
  simp [globalParity, parity_trivial]

/-- The global parity vectors are orthogonal on `G`, by the product
formula: the sum over `ξ ∈ G` of a product over the coordinates is the
product over the coordinates of the local sums, and one local sum
vanishes as soon as `x` and `y` differ somewhere. -/
theorem globalParity_row_orthogonal (x y : Ω → GadgetVector) :
    ∑ ξ : Ω → GadgetVector, globalParity ξ x * globalParity ξ y =
      if x = y then (Fintype.card (Ω → GadgetVector) : ℝ) else 0 := by
  let factor : Ω → GadgetVector → ℝ := fun u ζ => parity ζ (x u) * parity ζ (y u)
  calc
    ∑ ξ : Ω → GadgetVector, globalParity ξ x * globalParity ξ y =
        ∑ ξ : Ω → GadgetVector, ∏ u, factor u (ξ u) := by
      apply Finset.sum_congr rfl
      intro ξ _hξ
      simp only [globalParity, factor]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ u, ∑ ζ, factor u ζ := (Fintype.prod_sum factor).symm
    _ = ∏ u, (if x u = y u then (16 : ℝ) else 0) := by
      apply Finset.prod_congr rfl
      intro u _hu
      exact parity_row_orthogonal (x u) (y u)
    _ = if x = y then (Fintype.card (Ω → GadgetVector) : ℝ) else 0 := by
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true, Finset.prod_const, Finset.card_univ]
        rw [gridVector_card]
        push_cast
        ring
      · rw [if_neg hxy]
        obtain ⟨u, hu⟩ : ∃ u, x u ≠ y u := by
          by_contra hall
          push Not at hall
          exact hxy (funext hall)
        apply Finset.prod_eq_zero (Finset.mem_univ u)
        rw [if_neg hu]

omit [DecidableEq Ω] in
/-- The global parity vectors are multiplicative, one coordinate at a
time. -/
theorem globalParity_add (ξ a b : Ω → GadgetVector) :
    globalParity ξ (a + b) = globalParity ξ a * globalParity ξ b := by
  simp only [globalParity, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _hu
  exact parity_add (ξ u) (a u) (b u)

omit [DecidableEq Ω] in
/-- The global parity vectors of two parameters multiply to the parity
vector of their sum. -/
theorem globalParity_add_left (ξ η x : Ω → GadgetVector) :
    globalParity (ξ + η) x = globalParity ξ x * globalParity η x := by
  simp only [globalParity, Pi.add_apply, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _hu
  exact parity_add_left (ξ u) (η u) (x u)

omit [DecidableEq Ω] in
/-- The parameter and the argument of a global parity vector can be
exchanged, coordinate by coordinate. -/
theorem globalParity_comm (ξ x : Ω → GadgetVector) :
    globalParity ξ x = globalParity x ξ := by
  simp only [globalParity]
  apply Finset.prod_congr rfl
  intro u _hu
  exact parity_comm (ξ u) (x u)

/-- The entries of the global parity vector of a nonzero
parameter sum to zero, and those of the trivial parameter to `|G|`. -/
theorem sum_globalParity (ξ : Ω → GadgetVector) :
    ∑ x : Ω → GadgetVector, globalParity ξ x =
      if ξ = 0 then (Fintype.card (Ω → GadgetVector) : ℝ) else 0 := by
  calc
    ∑ x : Ω → GadgetVector, globalParity ξ x =
        ∑ x : Ω → GadgetVector, ∏ u, parity (ξ u) (x u) := rfl
    _ = ∏ u, ∑ z, parity (ξ u) z := (Fintype.prod_sum fun u z => parity (ξ u) z).symm
    _ = ∏ u, (if ξ u = 0 then (16 : ℝ) else 0) := by
      apply Finset.prod_congr rfl
      intro u _hu
      exact sum_parity (ξ u)
    _ = if ξ = 0 then (Fintype.card (Ω → GadgetVector) : ℝ) else 0 := by
      by_cases hξ : ξ = 0
      · subst hξ
        simp only [Pi.zero_apply, if_true, Finset.prod_const, Finset.card_univ]
        rw [gridVector_card]
        push_cast
        ring
      · rw [if_neg hξ]
        obtain ⟨u, hu⟩ : ∃ u, ξ u ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hξ (funext hall)
        apply Finset.prod_eq_zero (Finset.mem_univ u)
        rw [if_neg hu]

/-- The global parity vectors are pairwise orthogonal on `G`, each of
squared norm `|G|`. -/
theorem globalParity_orthogonal (ξ η : Ω → GadgetVector) :
    ∑ x : Ω → GadgetVector, globalParity ξ x * globalParity η x =
      if ξ = η then (Fintype.card (Ω → GadgetVector) : ℝ) else 0 := by
  have h : ∑ x : Ω → GadgetVector, globalParity ξ x * globalParity η x =
      ∑ x : Ω → GadgetVector, globalParity x ξ * globalParity x η := by
    apply Finset.sum_congr rfl
    intro x _hx
    rw [globalParity_comm ξ x, globalParity_comm η x]
  rw [h, globalParity_row_orthogonal]

/-- The global parity vectors are linearly independent: pairing a vanishing
combination with one of them isolates its coefficient times `|G|`. -/
theorem globalParity_linearIndependent :
    LinearIndependent ℝ
      (globalParity : (Ω → GadgetVector) → (Ω → GadgetVector) → ℝ) := by
  rw [linearIndependent_iff']
  intro s g hsum η hη
  have hpair := congrArg (fun v : (Ω → GadgetVector) → ℝ =>
    ∑ x, v x * globalParity η x) hsum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, Finset.sum_mul] at hpair
  rw [Finset.sum_comm] at hpair
  have hiso : ∑ ξ ∈ s, ∑ x, g ξ * globalParity ξ x * globalParity η x =
      g η * (Fintype.card (Ω → GadgetVector) : ℝ) := by
    calc
      ∑ ξ ∈ s, ∑ x, g ξ * globalParity ξ x * globalParity η x =
          ∑ ξ ∈ s, g ξ * ∑ x, globalParity ξ x * globalParity η x := by
        apply Finset.sum_congr rfl
        intro ξ _hξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = ∑ ξ ∈ s, g ξ *
            (if ξ = η then (Fintype.card (Ω → GadgetVector) : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro ξ _hξ
        rw [globalParity_orthogonal]
      _ = g η * (Fintype.card (Ω → GadgetVector) : ℝ) := by
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq' s η, if_pos hη]
  rw [hiso] at hpair
  have hcard : (Fintype.card (Ω → GadgetVector) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hpair).resolve_right hcard

/-- Lemma "Parity identities".  The first pair: a parity
vector on the alphabet is multiplicative in its argument, and on `G` the
parity vectors of two parameters multiply to the parity vector of their
sum.  The second pair: at a nonzero parameter the entries of the parity
vector sum to zero, on the alphabet and on `G`. -/
@[tutorial_box "lem:tutorial-parity-identities"]
theorem parity_identities :
    (∀ ξ z z' : GadgetVector, parity ξ (z + z') = parity ξ z * parity ξ z') ∧
    (∀ (ξ ξ' : Ω → GadgetVector) (x : Ω → GadgetVector),
      globalParity ξ x * globalParity ξ' x = globalParity (ξ + ξ') x) ∧
    (∀ ξ : GadgetVector, ξ ≠ 0 → ∑ z, parity ξ z = 0) ∧
    (∀ ξ : Ω → GadgetVector, ξ ≠ 0 → ∑ x, globalParity ξ x = 0) :=
  ⟨parity_add, fun ξ ξ' x => (globalParity_add_left ξ ξ' x).symm,
    fun ξ hξ => by rw [sum_parity, if_neg hξ],
    fun ξ hξ => by rw [sum_globalParity, if_neg hξ]⟩

end GlobalParity

end DDNNFNegation
