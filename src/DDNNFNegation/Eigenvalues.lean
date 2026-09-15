import DDNNFNegation.LocalInnerProducts
import TutorialBox

/-!
# Eigenvalues of the sum-dependent matrix

On a binary group, a character is an eigenvector of a matrix whose entry
depends only on the sum of its indices. Apply this identity to each product matrix and
factor its eigenvalue into the local sums from `LocalInnerProducts.lean`.
Averaging gives the eigenvalues of the outer matrix in the parity basis.
-/

namespace DDNNFNegation

open Finset
open scoped BigOperators

/-! ## Matrices determined by vector sums -/

section SumMatrices

variable {H : Type*} [Fintype H] [AddCommGroup H]

/-- For a finite abelian group of exponent two, a multiplicative sign
vector is an eigenvector of `M(a, b) = ω(a + b)`, with eigenvalue
`∑_z ω(z) * par(z)`. Substitute `z = a + b` and factor out `par(a)`. -/
@[tutorial_box "lem:tutorial-sum-matrix"]
theorem sum_matrix_eigenvectors
    (hself : ∀ a : H, a + a = 0) (ω par : H → ℝ)
    (hmul : ∀ a b : H, par (a + b) = par a * par b) (a : H) :
    ∑ b, ω (a + b) * par b = (∑ z, ω z * par z) * par a := by
  calc
    (∑ b, ω (a + b) * par b) = ∑ z, ω (a + (a + z)) * par (a + z) :=
      (Equiv.sum_comp (Equiv.addLeft a) fun b => ω (a + b) * par b).symm
    _ = ∑ z, ω z * (par a * par z) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [← add_assoc, hself, zero_add, hmul]
    _ = (∑ z, ω z * par z) * par a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _hz
      ring

end SumMatrices



section GlobalEigenbasis

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The global parity eigenbasis -/

/-- The eigenvalue of the product matrix of a term at the global parity
vector of `ξ`: the product over the coordinates of `⟨ω₁, par_{ξ_u}⟩` on the
coordinate set of the term and `⟨ω₀, par_{ξ_u}⟩` elsewhere. -/
noncomputable def termEigenvalue
    (term : Finset Ω) (ξ : Ω → GadgetVector) : ℝ :=
  ∏ u, if u ∈ term then weightParityInnerProduct weightOne (ξ u)
    else weightParityInnerProduct weightZero (ξ u)

/-- The eigenvalue sum for a product matrix factors into one weight-parity inner product per coordinate. -/
theorem sum_termWeight_mul_globalParity
    (term : Finset Ω) (ξ : Ω → GadgetVector) :
    (∑ s : Ω → GadgetVector, termWeight term s * globalParity ξ s) =
      termEigenvalue term ξ := by
  let factor : (u : Ω) → GadgetVector → ℝ := fun u z =>
    (if u ∈ term then weightOne z else weightZero z) * parity (ξ u) z
  calc
    (∑ s : Ω → GadgetVector, termWeight term s * globalParity ξ s) =
        ∑ s : Ω → GadgetVector, ∏ u, factor u (s u) := by
      apply Finset.sum_congr rfl
      intro s _hs
      simp only [termWeight, globalParity, factor]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ u, ∑ z, factor u z := (Fintype.prod_sum factor).symm
    _ = termEigenvalue term ξ := by
      simp only [termEigenvalue]
      apply Finset.prod_congr rfl
      intro u _hu
      by_cases huterm : u ∈ term
      · simp only [factor, if_pos huterm]
        rfl
      · simp only [factor, if_neg huterm]
        rfl

/-- Every global parity vector is an eigenvector of every product matrix.
Its eigenvalue is the product of the local weight-parity inner products,
by the sum-dependent matrix identity and factorization over coordinates. -/
theorem productMatrix_mulVec_globalParity
    (term : Finset Ω) (ξ : Ω → GadgetVector) :
    (productMatrix term).mulVec (globalParity ξ) =
      termEigenvalue term ξ • globalParity ξ := by
  funext x
  simp only [Matrix.mulVec, dotProduct, productMatrix, Pi.smul_apply,
    smul_eq_mul]
  rw [sum_matrix_eigenvectors gridVector_add_self (termWeight term)
        (globalParity ξ) (globalParity_add ξ) x,
    sum_termWeight_mul_globalParity term ξ]

end GlobalEigenbasis

section OuterEigenvalues

/-! ## The eigenvalues of `K` -/

/-- The eigenvalue `λ_ξ` of `K` at the global parity vector `par_ξ`: the
average over the buckets and the eligible label sets of the eigenvalues of
the product matrices. -/
noncomputable def outerEigenvalue (n : ℕ) (ξ : (Fin n × Fin n) → GadgetVector) : ℝ :=
  (∑ i, ∑ S ∈ eligibleLabelSets n, termEigenvalue (termCoordinates i S) ξ) /
    ((n : ℝ) * (eligibleLabelSets n).card)

/-- Lemma "A parity eigenbasis for `K`": every global parity vector
is an eigenvector of `K`, with the average `λ_ξ` of the term eigenvalues. -/
theorem outerMatrix_mulVec_globalParity (n : ℕ) (ξ : (Fin n × Fin n) → GadgetVector) :
    (outerMatrix n).mulVec (globalParity ξ) = outerEigenvalue n ξ • globalParity ξ := by
  funext x
  simp only [Matrix.mulVec, dotProduct, outerMatrix, outerEigenvalue, Pi.smul_apply,
    smul_eq_mul]
  set D : ℝ := (n : ℝ) * (eligibleLabelSets n).card with hD
  calc
    ∑ y, (∑ i, ∑ S ∈ eligibleLabelSets n, productMatrix (termCoordinates i S) x y) / D *
          globalParity ξ y
        = (∑ y, ∑ i, ∑ S ∈ eligibleLabelSets n,
            productMatrix (termCoordinates i S) x y * globalParity ξ y) / D := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      rw [div_mul_eq_mul_div, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = (∑ i, ∑ S ∈ eligibleLabelSets n,
            ∑ y, productMatrix (termCoordinates i S) x y * globalParity ξ y) / D := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = (∑ i, ∑ S ∈ eligibleLabelSets n,
            termEigenvalue (termCoordinates i S) ξ * globalParity ξ x) / D := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro S _
      have h := congrFun (productMatrix_mulVec_globalParity (termCoordinates i S) ξ) x
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      exact h
    _ = (∑ i, ∑ S ∈ eligibleLabelSets n, termEigenvalue (termCoordinates i S) ξ) / D *
          globalParity ξ x := by
      rw [div_mul_eq_mul_div, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- Lemma "A parity eigenbasis for `K`".  Every global parity
vector `par_ξ` is an eigenvector of every product matrix `K_{i,S}`, with
the product of the weight-parity inner products as eigenvalue
(`termEigenvalue`), hence of `K`, with the average `λ_ξ` of those
eigenvalues; and the parity vectors are pairwise orthogonal, each of
squared norm `|G|`, and linearly independent, so the `|G|` of them are an
orthogonal basis of `ℝ^G`. -/
@[tutorial_box "lem:tutorial-global-eigenbasis"]
theorem parity_eigenbasis (n : ℕ) (ξ : (Fin n × Fin n) → GadgetVector) :
    (∀ (i : Fin n) (S : Finset (Fin n)), S ∈ eligibleLabelSets n →
      (productMatrix (termCoordinates i S)).mulVec (globalParity ξ) =
        termEigenvalue (termCoordinates i S) ξ • globalParity ξ) ∧
    (outerMatrix n).mulVec (globalParity ξ) = outerEigenvalue n ξ • globalParity ξ ∧
    (∀ η : (Fin n × Fin n) → GadgetVector,
      ∑ x, globalParity ξ x * globalParity η x =
        if ξ = η then (Fintype.card ((Fin n × Fin n) → GadgetVector) : ℝ) else 0) ∧
    LinearIndependent ℝ
      (globalParity : ((Fin n × Fin n) → GadgetVector) →
        ((Fin n × Fin n) → GadgetVector) → ℝ) :=
  ⟨fun i S _hS => productMatrix_mulVec_globalParity (termCoordinates i S) ξ,
    outerMatrix_mulVec_globalParity n ξ, globalParity_orthogonal ξ,
    globalParity_linearIndependent⟩

end OuterEigenvalues

end DDNNFNegation
