import DDNNFNegation.ParityVectors
import TutorialBox

/-!
# The one-coordinate weight-parity inner products

Decompose each weight into constant, point-mass, and quadratic-sign
parts, then translate the quadratic sum. Finite checks establish the
pointwise four-bit identities and the ten-minus-six total. Algebraic
identities give the inner-product formulas used in `Eigenvalues.lean`.
-/

namespace DDNNFNegation

open Finset

open scoped BigOperators

/-- The weight-parity inner product `⟨ω_r, par_ξ⟩ = ∑_z ω_r(z) par_ξ(z)` of a
weight table `ω_r`. -/
noncomputable def weightParityInnerProduct (w : GadgetVector → ℝ) (ξ : GadgetVector) : ℝ :=
  ∑ t, w t * parity ξ t

section LocalEigenvalues

/-! ## The one-coordinate parity sums -/

private def quadraticSign (z : GadgetVector) : ℤ :=
  if quadForm z = 0 then 1 else -1

-- The quadratic-sum shift exchanges the two halves of the parameter.
private theorem quadratic_shift_sign : ∀ ξ z : GadgetVector,
    quadraticSign z * signZ ξ z =
      quadraticSign ξ * quadraticSign (z + (ξ.2, ξ.1)) := by decide

private theorem quadratic_sign_total : (∑ z, quadraticSign z) = 4 := by decide

private theorem quadratic_parity_sum (ξ : GadgetVector) :
    (∑ z, (quadraticSign z : ℝ) * parity ξ z) = 4 * (quadraticSign ξ : ℝ) := by
  have hsum : (∑ z, quadraticSign z * signZ ξ z) = 4 * quadraticSign ξ := by
    calc
      (∑ z, quadraticSign z * signZ ξ z) =
          ∑ z, quadraticSign ξ * quadraticSign (z + (ξ.2, ξ.1)) := by
        exact sum_congr rfl fun z _ => quadratic_shift_sign ξ z
      _ = quadraticSign ξ * ∑ z, quadraticSign (z + (ξ.2, ξ.1)) :=
        (mul_sum _ _ _).symm
      _ = quadraticSign ξ * ∑ z, quadraticSign z := by
        congr 1
        exact Equiv.sum_comp (Equiv.addRight (ξ.2, ξ.1)) quadraticSign
      _ = 4 * quadraticSign ξ := by rw [quadratic_sign_total]; ring
  unfold parity
  exact_mod_cast hsum

private theorem weight_decomposition (z : GadgetVector) :
    weightOne z = (1 - (quadraticSign z : ℝ)) / 12 ∧
    weightZero z = (7 / 12 : ℝ) * (if z = 0 then 1 else 0) +
      1 / 48 + (quadraticSign z : ℝ) / 48 := by
  have h1 : ∀ z : GadgetVector, oneTable z = 2 * (1 - quadraticSign z) := by decide
  have h0 : ∀ z : GadgetVector,
      2 * zeroTable z = 28 * (if z = 0 then 1 else 0) + 1 + quadraticSign z := by decide
  have hz1 := h1 z
  have hz0 : (2 : ℝ) * (zeroTable z : ℝ) =
      28 * (if z = 0 then 1 else 0) + 1 + (quadraticSign z : ℝ) := by
    exact_mod_cast h0 z
  constructor
  · rw [weightOne, hz1]
    push_cast
    ring
  · rw [weightZero]
    linarith

private theorem point_mass_parity_sum (ξ : GadgetVector) :
    (∑ z : GadgetVector, (if z = 0 then (1 : ℝ) else 0) * parity ξ z) = 1 := by
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
  rw [parity_comm, parity_trivial]

/-- Lemma "Weight-parity inner products", the table `ω₀`: `⟨ω₀, par_ξ⟩` is `1`
at the trivial parameter, `2/3` at the nine nonzero parameters with
`Q(ξ) = 0`, and `1/2` at the six parameters with `Q(ξ) = 1`. -/
theorem weightZero_inner_product (ξ : GadgetVector) :
    weightParityInnerProduct weightZero ξ =
      if ξ = 0 then 1 else if quadForm ξ = 0 then 2 / 3 else 1 / 2 := by
  have hsum : weightParityInnerProduct weightZero ξ =
      7 / 12 * ∑ z, (if z = 0 then (1 : ℝ) else 0) * parity ξ z +
      (∑ z, parity ξ z) / 48 +
      (∑ z, (quadraticSign z : ℝ) * parity ξ z) / 48 := by
    simp only [weightParityInnerProduct, sum_div, mul_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro z _
    rw [(weight_decomposition z).2]
    ring
  rw [hsum, point_mass_parity_sum, sum_parity, quadratic_parity_sum]
  by_cases hξ : ξ = 0
  · subst ξ
    norm_num [quadraticSign, quadForm_zero]
  · simp only [if_neg hξ, quadraticSign]
    split_ifs <;> norm_num

/-- Lemma "Weight-parity inner products", the table `ω₁`: `⟨ω₁, par_ξ⟩` is `1`
at the trivial parameter, `-1/3` at the nine nonzero parameters with
`Q(ξ) = 0`, and `1/3` at the six parameters with `Q(ξ) = 1`. -/
theorem weightOne_inner_product (ξ : GadgetVector) :
    weightParityInnerProduct weightOne ξ =
      if ξ = 0 then 1 else if quadForm ξ = 0 then -(1 / 3) else 1 / 3 := by
  have hsum : weightParityInnerProduct weightOne ξ =
      ((∑ z, parity ξ z) - ∑ z, (quadraticSign z : ℝ) * parity ξ z) / 12 := by
    rw [weightParityInnerProduct, ← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro z _
    rw [(weight_decomposition z).1]
    ring
  rw [hsum, sum_parity, quadratic_parity_sum]
  by_cases hξ : ξ = 0
  · subst ξ
    norm_num [quadraticSign, quadForm_zero]
  · simp only [if_neg hξ, quadraticSign]
    split_ifs <;> norm_num

/-- Every `⟨ω₀, par_ξ⟩` is positive. -/
theorem weightZero_inner_product_pos (ξ : GadgetVector) :
    0 < weightParityInnerProduct weightZero ξ := by
  rw [weightZero_inner_product]
  split_ifs <;> norm_num

/-- Lemma "Weight-parity inner products": the pair
`(⟨ω₀, par_ξ⟩, ⟨ω₁, par_ξ⟩)` is `(1, 1)` at the trivial parameter,
`(2/3, -1/3)` at a nonzero parameter with `Q(ξ) = 0`, and `(1/2, 1/3)` at
a nonzero parameter with `Q(ξ) = 1`; in particular every `⟨ω₀, par_ξ⟩` is
positive.  The two tables are `weightZero_inner_product` and
`weightOne_inner_product`. -/
@[tutorial_box "lem:tutorial-weight-parity-inner-products"]
theorem weight_parity_inner_products (ξ : GadgetVector) :
    (weightParityInnerProduct weightZero ξ, weightParityInnerProduct weightOne ξ) =
      (if ξ = 0 then ((1 : ℝ), (1 : ℝ))
        else if quadForm ξ = 0 then (2 / 3, -(1 / 3)) else (1 / 2, 1 / 3)) ∧
    0 < weightParityInnerProduct weightZero ξ := by
  refine ⟨?_, weightZero_inner_product_pos ξ⟩
  rw [weightZero_inner_product, weightOne_inner_product]
  split_ifs <;> rfl

/-- At the zero parameter the parity vector is the all-ones vector, so
the one-coordinate sum is the total of the table. -/
theorem weightParityInnerProduct_trivial (w : GadgetVector → ℝ) :
    weightParityInnerProduct w (0 : GadgetVector) = ∑ t, w t := by
  simp only [weightParityInnerProduct, parity_trivial, mul_one]

/-- `⟨ω₀, par_0⟩ = 1`: the total of the table `ω₀`. -/
theorem weightZero_inner_product_trivial :
    weightParityInnerProduct weightZero (0 : GadgetVector) = 1 := by
  rw [weightParityInnerProduct_trivial]
  exact weightZero_rowSum

end LocalEigenvalues

end DDNNFNegation
