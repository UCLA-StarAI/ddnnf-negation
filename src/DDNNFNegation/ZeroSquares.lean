import DDNNFNegation.LeastEigenvalue
import TutorialBox

/-!
# Bounding zero squares from the spectrum

Expand the indicator of a zero square in an orthonormal eigenbasis.
The constant eigenvector contributes positively; the lower bound on the
other eigenvalues limits how much they can cancel it. This bounds the
square's relative size in terms of the least eigenvalue.
-/

namespace DDNNFNegation

open Finset

section Expansion

/-! ## Expansion in an orthonormal eigenbasis -/

variable {V Ξ : Type*} [Fintype V] [Fintype Ξ] [DecidableEq V]

/-- The coefficient `⟨z, F(·, ξ)⟩` of a real vector `z` on the member `ξ`
of the family `F`. -/
def coefficient (F : V → Ξ → ℝ) (z : V → ℝ) (ξ : Ξ) : ℝ :=
  ∑ x, z x * F x ξ

/-- Row orthogonality turns a sum of products of two coefficients into
the inner product of the two vectors. -/
theorem sum_coefficient_mul_coefficient (F : V → Ξ → ℝ)
    (hrow : ∀ x y, ∑ ξ, F x ξ * F y ξ = if x = y then (1 : ℝ) else 0)
    (a b : V → ℝ) :
    ∑ ξ, coefficient F a ξ * coefficient F b ξ = 1 * ∑ x, a x * b x := by
  simp only [coefficient]
  calc ∑ ξ, (∑ x, a x * F x ξ) * (∑ u, b u * F u ξ)
      = ∑ ξ, ∑ x, ∑ u, a x * b u * (F x ξ * F u ξ) := by
        refine sum_congr rfl fun ξ _ => ?_
        rw [sum_mul_sum]
        exact sum_congr rfl fun x _ => sum_congr rfl fun u _ => by ring
    _ = ∑ x, ∑ u, a x * b u * ∑ ξ, F x ξ * F u ξ := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun u _ => by rw [mul_sum]
    _ = ∑ x, a x * b x * 1 := by
        refine sum_congr rfl fun x _ => ?_
        simp only [hrow, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
    _ = 1 * ∑ x, a x * b x := by
        rw [mul_sum]
        exact sum_congr rfl fun x _ => by ring

/-- Parseval: `∑_ξ c_ξ² = ‖z‖²`. -/
theorem sum_sq_coefficient (F : V → Ξ → ℝ)
    (hrow : ∀ x y, ∑ ξ, F x ξ * F y ξ = if x = y then (1 : ℝ) else 0)
    (z : V → ℝ) :
    ∑ ξ, coefficient F z ξ ^ 2 = 1 * (z ⬝ᵥ z) := by
  simp only [sq, dotProduct]
  exact sum_coefficient_mul_coefficient F hrow z z

/-- If every member of the family is an eigenvector of `K`, the quadratic
form is the eigenvalue-weighted sum of the squared coefficients:
`∑_ξ λ_ξ c_ξ² = z ⬝ K z`. -/
theorem sum_eigenvalue_mul_sq_coefficient (K : Matrix V V ℝ) (F : V → Ξ → ℝ) (eig : Ξ → ℝ)
    (hrow : ∀ x y, ∑ ξ, F x ξ * F y ξ = if x = y then (1 : ℝ) else 0)
    (heigen : ∀ ξ x, ∑ y, K x y * F y ξ = eig ξ * F x ξ)
    (z : V → ℝ) :
    ∑ ξ, eig ξ * coefficient F z ξ ^ 2 = 1 * (z ⬝ᵥ K.mulVec z) := by
  have hscale : ∀ ξ, eig ξ * coefficient F z ξ = coefficient F (K.vecMul z) ξ := by
    intro ξ
    simp only [coefficient, Matrix.vecMul, dotProduct]
    calc eig ξ * ∑ x, z x * F x ξ = ∑ x, z x * (eig ξ * F x ξ) := by
          rw [mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ = ∑ x, z x * ∑ y, K x y * F y ξ := by simp_rw [← heigen]
      _ = ∑ x, ∑ y, z x * K x y * F y ξ := by
          refine sum_congr rfl fun x _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun y _ => by ring
      _ = ∑ y, ∑ x, z x * K x y * F y ξ := sum_comm
      _ = ∑ y, (∑ x, z x * K x y) * F y ξ := sum_congr rfl fun y _ => by rw [sum_mul]
  calc ∑ ξ, eig ξ * coefficient F z ξ ^ 2
      = ∑ ξ, coefficient F (K.vecMul z) ξ * coefficient F z ξ := by
        refine sum_congr rfl fun ξ _ => ?_
        rw [← hscale ξ]
        ring
    _ = 1 * ∑ y, K.vecMul z y * z y := sum_coefficient_mul_coefficient F hrow _ _
    _ = 1 * (z ⬝ᵥ K.mulVec z) := by
        rw [Matrix.dotProduct_mulVec]
        simp only [dotProduct]

end Expansion

section ZeroSquares

/-! ## Small zero squares -/

variable {n : ℕ}

/-- `λ_0 = 1`: the parity vector of the parameter `0` is the all-ones
vector, and every row of `K` sums to `1` (property (c)). -/
theorem outerEigenvalue_zero (hn : 0 < n) : outerEigenvalue n 0 = 1 := by
  have h := congrFun (outerMatrix_mulVec_globalParity n 0) 0
  rw [globalParity_zero, outerMatrix_mulVec_one hn] at h
  simpa using h.symm

/-- If `F_n(u + v) = 0` for all `u, v ∈ I`, then `|I| ≤ ε * |G|`.
The zero square of the matrix has this size bound by expanding the
indicator of `I` in the parity eigenbasis. -/
@[tutorial_box "lem:tutorial-independent"]
theorem small_zero_squares (ranks : LabelOrders n) (hn : 0 < n)
    (I : Finset ((Fin n × Fin n) → GadgetVector))
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬ outerFunction ranks hn (u + v)) :
    (I.card : ℝ) ≤ spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) := by
  -- the indicator `1_I`, its coefficients `c_ξ`, and the parity eigenbasis
  set z : ((Fin n × Fin n) → GadgetVector) → ℝ := fun x => if x ∈ I then 1 else 0 with hz
  let size : ℝ := Fintype.card ((Fin n × Fin n) → GadgetVector)
  have hsizepos : 0 < size := by
    dsimp [size]
    exact_mod_cast (Fintype.card_pos (α := (Fin n × Fin n) → GadgetVector))
  let e := fun x ξ : (Fin n × Fin n) → GadgetVector => globalParity ξ x / Real.sqrt size
  set c := coefficient e z with hc
  have hrow : ∀ x y, ∑ ξ, e x ξ * e y ξ = if x = y then (1 : ℝ) else 0 := by
    intro x y
    simp only [e, div_mul_div_comm, ← sum_div, Real.mul_self_sqrt hsizepos.le]
    rw [globalParity_row_orthogonal]
    change (if x = y then size else 0) / size = _
    split_ifs <;> simp [hsizepos.ne']
  have heigen : ∀ ξ x, ∑ y, outerMatrix n x y * e y ξ =
      outerEigenvalue n ξ * e x ξ := by
    intro ξ x
    have h := congrFun (outerMatrix_mulVec_globalParity n ξ) x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [e, ← mul_div_assoc, ← sum_div]
    rw [h]
  -- property (b): the quadratic form of `1_I` vanishes
  have hquad : z ⬝ᵥ (outerMatrix n).mulVec z = 0 := by
    simp only [dotProduct, Matrix.mulVec, hz]
    refine sum_eq_zero fun u _ => ?_
    by_cases hu : u ∈ I
    · simp only [hu, if_true, one_mul]
      refine sum_eq_zero fun v _ => ?_
      by_cases hv : v ∈ I
      · simp [hv, outerMatrix_eq_zero_of_not_outerFunction ranks hn u v (hI u hu v hv)]
      · simp [hv]
    · simp [hu]
  -- `‖1_I‖² = |I|` and `c_0 = |I| / √|G|`
  have hsum : ∑ x, z x = I.card := by
    simp only [hz, sum_boole, filter_mem_eq_inter, univ_inter]
  have hnorm : z ⬝ᵥ z = I.card := by
    have hsq : ∀ x, z x * z x = z x := fun x => by by_cases hx : x ∈ I <;> simp [hz, hx]
    simp only [dotProduct, hsq, hsum]
  have hc0 : c 0 = I.card / Real.sqrt size := by
    simp only [hc, coefficient, e, globalParity_zero, Pi.one_apply,
      ← mul_div_assoc, mul_one, ← sum_div, hsum]
  -- Parseval and the eigenvalue-weighted sum in the normalized basis.
  have hparseval := sum_sq_coefficient e hrow z
  have hweighted := sum_eigenvalue_mul_sq_coefficient (outerMatrix n)
    e (outerEigenvalue n) hrow heigen z
  rw [hnorm, one_mul] at hparseval
  rw [hquad, mul_zero] at hweighted
  -- Split off the constant vector, then bound the other eigenvalues by -ε.
  have hsplit : outerEigenvalue n 0 * c 0 ^ 2 +
      ∑ ξ ∈ univ.erase (0 : (Fin n × Fin n) → GadgetVector), outerEigenvalue n ξ * c ξ ^ 2 =
      ∑ ξ, outerEigenvalue n ξ * c ξ ^ 2 :=
    add_sum_erase univ (fun ξ => outerEigenvalue n ξ * c ξ ^ 2)
      (mem_univ (0 : (Fin n × Fin n) → GadgetVector))
  rw [outerEigenvalue_zero hn, hc0, one_mul, hweighted, div_pow,
    Real.sq_sqrt hsizepos.le] at hsplit
  have hrest : -spectralEpsilon n * ∑ ξ ∈ univ.erase (0 : (Fin n × Fin n) → GadgetVector), c ξ ^ 2 ≤
      ∑ ξ ∈ univ.erase (0 : (Fin n × Fin n) → GadgetVector), outerEigenvalue n ξ * c ξ ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_right (spectral_estimate hn ξ) (sq_nonneg _)
  have hrest' : ∑ ξ ∈ univ.erase (0 : (Fin n × Fin n) → GadgetVector), c ξ ^ 2 ≤
      ∑ ξ, c ξ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => sq_nonneg _
  have hε := spectralEpsilon_nonneg n
  have hscaled := mul_le_mul_of_nonneg_left (hrest'.trans hparseval.le) hε
  -- `|I|² ≤ ε |G| |I|`, then divide by `|I|`
  have hkey : (I.card : ℝ) * I.card ≤
      spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) * I.card := by
    have hnormalized : (I.card : ℝ) ^ 2 / size ≤ spectralEpsilon n * I.card := by
      nlinarith [hsplit, hrest, hscaled]
    have hcleared := (div_le_iff₀ hsizepos).mp hnormalized
    dsimp [size] at hcleared
    nlinarith [hcleared]
  rcases (Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right hkey hpos

end ZeroSquares

end DDNNFNegation
