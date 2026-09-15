import DDNNFNegation.Gadget
import TutorialBox

/-!
# A matrix supported on the outer function

The matrix entry at `u, v` depends on `u + v`. Its nonnegative summands
are indexed by eligible label sets. A positive entry implies that the
outer function is true at that sum, so a zero of the function forces a
zero of the matrix. The diagonal and row-sum identities provide the
normalization used in the spectral analysis.
-/

namespace DDNNFNegation

open Finset

/-! ## The two weight tables -/

/-- The table `ω₀` scaled by `24`: `15` at the zero string, `1` at the
other nine strings with `Q = 0`, `0` at the six strings with `Q = 1`. -/
def zeroTable (t : GadgetVector) : ℤ :=
  if t = 0 then 15 else if quadForm t = 0 then 1 else 0

/-- The table `ω₁` scaled by `24`: `4` at each of the six strings with
`Q = 1`, `0` at the ten strings with `Q = 0`. -/
def oneTable (t : GadgetVector) : ℤ :=
  if quadForm t = 0 then 0 else 4

/-- The weight function `ω₀` of the tutorial's left-hand table. -/
@[tutorial_box "def:tutorial-weights"]
noncomputable def weightZero (t : GadgetVector) : ℝ :=
  (zeroTable t : ℝ) / 24

/-- The weight function `ω₁` of the tutorial's right-hand table. -/
@[tutorial_box "def:tutorial-weights"]
noncomputable def weightOne (t : GadgetVector) : ℝ :=
  (oneTable t : ℝ) / 24

/-- The zero-bit weight table has no negative entries. -/
theorem weightZero_nonneg (t : GadgetVector) : 0 ≤ weightZero t := by
  unfold weightZero zeroTable
  split_ifs <;> norm_num

/-- The one-bit weight table has no negative entries. -/
theorem weightOne_nonneg (t : GadgetVector) : 0 ≤ weightOne t := by
  unfold weightOne oneTable
  split_ifs <;> norm_num

/-- `ω₀` is positive exactly at the strings with `Q = 0`. -/
theorem weightZero_pos_iff (t : GadgetVector) :
    0 < weightZero t ↔ quadForm t = 0 := by
  unfold weightZero zeroTable
  split_ifs with h0 hq
  · norm_num [h0, quadForm_zero]
  · norm_num [hq]
  · norm_num [hq]

/-- `ω₁` is positive exactly at the strings with `Q = 1`. -/
theorem weightOne_pos_iff (t : GadgetVector) :
    0 < weightOne t ↔ quadForm t = 1 := by
  rw [quadForm_eq_one_iff]
  unfold weightOne oneTable
  split_ifs with hq <;> norm_num [hq]

private theorem sum_zeroTable : ∑ t, zeroTable t = 24 := by decide

private theorem sum_oneTable : ∑ t, oneTable t = 24 := by decide

/-- The entries of `ω₀` total `(15 + 9)/24 = 1`. -/
theorem weightZero_rowSum : ∑ t : GadgetVector, weightZero t = 1 := by
  simp only [weightZero]
  rw [← sum_div, ← Int.cast_sum, sum_zeroTable]
  norm_num

/-- The entries of `ω₁` total `6 · 4/24 = 1`. -/
theorem weightOne_rowSum : ∑ t : GadgetVector, weightOne t = 1 := by
  simp only [weightOne]
  rw [← sum_div, ← Int.cast_sum, sum_oneTable]
  norm_num

/-! ## The product matrices -/

section TermMatrices

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The weight the product matrix gives to one sum vector: one factor
per coordinate, `ω₁` on the coordinate set of the term and `ω₀`
elsewhere. -/
noncomputable def termWeight (term : Finset Ω) (s : Ω → GadgetVector) : ℝ :=
  ∏ u, if u ∈ term then weightOne (s u) else weightZero (s u)

/-- The product matrix `K_{i,S}` of the outer term with coordinate set
`P_{i,S}`: its entry at `(x, y)` is the weight of the sum `x + y`. -/
@[tutorial_box "def:tutorial-product-matrices"]
noncomputable def productMatrix (term : Finset Ω) :
    Matrix (Ω → GadgetVector) (Ω → GadgetVector) ℝ :=
  fun x y => termWeight term (x + y)

/-- The entries of `productMatrix`, coordinate by coordinate. -/
theorem productMatrix_apply (term : Finset Ω) (x y : Ω → GadgetVector) :
    productMatrix term x y =
      ∏ u, if u ∈ term then weightOne (x u + y u)
        else weightZero (x u + y u) :=
  rfl

/-- The bits `Q(x_u + y_u)` are the characteristic vector of the term. -/
def RealizesTerm (term : Finset Ω) (x y : Ω → GadgetVector) : Prop :=
  ∀ u, u ∈ term ↔ gadgetBits (x + y) u

/-- Products of the local nonnegative weights remain nonnegative. -/
theorem productMatrix_nonneg (term : Finset Ω) (x y : Ω → GadgetVector) :
    0 ≤ productMatrix term x y := by
  rw [productMatrix_apply]
  apply Finset.prod_nonneg
  intro u _hu
  split_ifs
  · exact weightOne_nonneg _
  · exact weightZero_nonneg _

/-- Swapping the two arguments leaves every coordinate sum unchanged. -/
theorem productMatrix_symmetric (term : Finset Ω) :
    (productMatrix term).transpose = productMatrix term := by
  ext x y
  simp only [Matrix.transpose_apply, productMatrix]
  rw [add_comm y x]

/-- Positive weight exactly on the pairs whose bits are the characteristic
vector of the term: every factor is nonnegative, so a positive product has
positive factors, and a positive factor `ω₁` or `ω₀` at a coordinate fixes
the bit there. -/
theorem productMatrix_pos_iff_realizes
    (term : Finset Ω) (x y : Ω → GadgetVector) :
    0 < productMatrix term x y ↔ RealizesTerm term x y := by
  rw [productMatrix_apply]
  constructor
  · intro hpos u
    have hprod :
        (∏ u, if u ∈ term then weightOne (x u + y u)
          else weightZero (x u + y u)) ≠ 0 := hpos.ne'
    by_cases hu : u ∈ term
    · constructor
      · intro _
        show quadForm (x u + y u) = 1
        apply (weightOne_pos_iff (x u + y u)).1
        have hne : weightOne (x u + y u) ≠ 0 := by
          intro hzero
          apply hprod
          apply Finset.prod_eq_zero (Finset.mem_univ u)
          simp [hu, hzero]
        exact lt_of_le_of_ne (weightOne_nonneg _) (Ne.symm hne)
      · intro _
        exact hu
    · constructor
      · exact fun hmem => (hu hmem).elim
      · intro hbit
        exfalso
        have hne : weightZero (x u + y u) ≠ 0 := by
          intro hzero
          apply hprod
          apply Finset.prod_eq_zero (Finset.mem_univ u)
          simp [hu, hzero]
        have hq0 : quadForm (x u + y u) = 0 :=
          (weightZero_pos_iff _).1 (lt_of_le_of_ne (weightZero_nonneg _) (Ne.symm hne))
        have hq1 : quadForm (x u + y u) = 1 := hbit
        rw [hq0] at hq1
        exact absurd hq1 (by decide)
  · intro hrealizes
    apply Finset.prod_pos
    intro u _hu
    by_cases hu : u ∈ term
    · simp only [hu, if_true]
      exact (weightOne_pos_iff (x u + y u)).2 ((hrealizes u).1 hu)
    · simp only [hu, if_false]
      apply (weightZero_pos_iff (x u + y u)).2
      by_contra hne
      exact hu ((hrealizes u).2 ((quadForm_eq_one_iff _).2 hne))

/-- Translating the argument by a fixed string permutes the alphabet, so a
total over the alphabet is unchanged. -/
private theorem sum_add_left (w : GadgetVector → ℝ) (x : GadgetVector) :
    (∑ y : GadgetVector, w (x + y)) = ∑ t : GadgetVector, w t :=
  Equiv.sum_comp (Equiv.addLeft x) w

/-- Property (c) for one product matrix: every row of `K_{i,S}` sums to
`1`.  As `y` ranges over `G`, so does `x + y`; the sum over `G` of a
product over the coordinates is the product of the one-coordinate totals
(distributivity), and both tables total `1`. -/
theorem productMatrix_rowSum (term : Finset Ω) (x : Ω → GadgetVector) :
    ∑ y, productMatrix term x y = 1 := by
  let factor : (u : Ω) → GadgetVector → ℝ :=
    fun u z => if u ∈ term then weightOne (x u + z) else weightZero (x u + z)
  calc
    (∑ y : Ω → GadgetVector, productMatrix term x y) =
        ∑ y : Ω → GadgetVector, ∏ u, factor u (y u) := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact productMatrix_apply term x y
    _ = ∏ u, ∑ z, factor u z := (Fintype.prod_sum factor).symm
    _ = ∏ _u : Ω, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro u _hu
      by_cases huterm : u ∈ term
      · simp only [factor, huterm, if_pos]
        rw [sum_add_left weightOne (x u)]
        exact weightOne_rowSum
      · simp only [factor, if_neg huterm]
        rw [sum_add_left weightZero (x u)]
        exact weightZero_rowSum
    _ = 1 := Finset.prod_const_one

end TermMatrices


noncomputable section

/-- The matrix `K`: the average of the product matrices `K_{i,S}` over the
buckets `i` and the eligible label sets `S`. -/
@[tutorial_box "def:tutorial-product-matrices"]
def outerMatrix (n : ℕ) :
    Matrix ((Fin n × Fin n) → GadgetVector) ((Fin n × Fin n) → GadgetVector) ℝ :=
  fun x y =>
    (∑ i, ∑ S ∈ eligibleLabelSets n, productMatrix (termCoordinates i S) x y) /
      ((n : ℝ) * (eligibleLabelSets n).card)

/-- Property (a): the entries of `K` are nonnegative. -/
theorem outerMatrix_nonneg (n : ℕ) (x y : (Fin n × Fin n) → GadgetVector) :
    0 ≤ outerMatrix n x y := by
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro S _hS
  exact productMatrix_nonneg _ x y

/-- Property (a): `K` is symmetric, because every product matrix is. -/
theorem outerMatrix_symmetric (n : ℕ) :
    (outerMatrix n).transpose = outerMatrix n := by
  ext x y
  simp only [Matrix.transpose_apply, outerMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro S _hS
  have h := congrFun (congrFun (productMatrix_symmetric (termCoordinates i S)) x) y
  simp only [Matrix.transpose_apply] at h
  rw [h]

/-- A positive entry of `K` is a positive entry of some product matrix
`K_{i,S}`, whose bits `Q(x_u + y_u)` then form the characteristic vector of
`P_{i,S}`. -/
theorem exists_realizes_of_outerMatrix_pos (n : ℕ)
    (x y : (Fin n × Fin n) → GadgetVector) (hpos : 0 < outerMatrix n x y) :
    ∃ i, ∃ S ∈ eligibleLabelSets n, RealizesTerm (termCoordinates i S) x y := by
  by_contra hnone
  push Not at hnone
  have hallzero : ∀ i, ∀ S ∈ eligibleLabelSets n,
      productMatrix (termCoordinates i S) x y = 0 := by
    intro i S hS
    have hnotpos : ¬ 0 < productMatrix (termCoordinates i S) x y := fun h =>
      hnone i S hS ((productMatrix_pos_iff_realizes _ x y).mp h)
    exact le_antisymm (le_of_not_gt hnotpos) (productMatrix_nonneg _ x y)
  have hzero : outerMatrix n x y = 0 := by
    simp only [outerMatrix]
    rw [Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (hallzero i)), zero_div]
  linarith

/-- Property (b): `K(x, y) > 0` only if `F_n(x + y) = 1`.  The
characteristic vector of `P_{i,S}` satisfies the term `(i, S)` of `f_n`. -/
theorem outerMatrix_pos_imp_outerFunction {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n)
    (x y : (Fin n × Fin n) → GadgetVector) (hpos : 0 < outerMatrix n x y) :
    outerFunction ranks hn (x + y) := by
  obtain ⟨i, S, hS, hrealizes⟩ := exists_realizes_of_outerMatrix_pos n x y hpos
  let T : ThresholdTerm n := ⟨⟨i, S, by
    apply card_pos.mp
    have := mem_eligibleLabelSets.mp hS
    omega⟩, mem_eligibleLabelSets.mp hS⟩
  have hv : (fun u => u ∈ termPositive T) = gadgetBits (x + y) := by
    funext u
    exact propext (hrealizes u)
  unfold outerFunction
  rw [← hv]
  exact outerDNF_positiveCharacteristic ranks hn T

/-- Property (b) in the form Lemma "Small zero squares" uses: if
`F_n(x + y) = 0` then `K(x, y) = 0`. -/
theorem outerMatrix_eq_zero_of_not_outerFunction {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n)
    (x y : (Fin n × Fin n) → GadgetVector)
    (hzero : ¬ outerFunction ranks hn (x + y)) :
    outerMatrix n x y = 0 := by
  have hnotpos : ¬ 0 < outerMatrix n x y := fun hpos =>
    hzero (outerMatrix_pos_imp_outerFunction ranks hn x y hpos)
  exact le_antisymm (le_of_not_gt hnotpos) (outerMatrix_nonneg n x y)

/-- Property (c): every row of `K` sums to `1`, that is `K 1 = 1`.  Every
product matrix has row sum `1` (`productMatrix_rowSum`), and `K` is the
average of `n M` of them. -/
theorem outerMatrix_mulVec_one {n : ℕ} (hn : 0 < n) :
    (outerMatrix n).mulVec (1 : ((Fin n × Fin n) → GadgetVector) → ℝ) = 1 := by
  have hM : (0 : ℝ) < (eligibleLabelSets n).card := by
    exact_mod_cast card_eligibleLabelSets_pos n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  funext x
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, outerMatrix]
  rw [← Finset.sum_div, div_eq_one_iff_eq (mul_pos hn' hM).ne']
  calc ∑ y, ∑ i, ∑ S ∈ eligibleLabelSets n, productMatrix (termCoordinates i S) x y
      = ∑ i, ∑ S ∈ eligibleLabelSets n, ∑ y, productMatrix (termCoordinates i S) x y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _hi
        exact Finset.sum_comm
    _ = ∑ _i : Fin n, ∑ _S ∈ eligibleLabelSets n, (1 : ℝ) :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun S _ => productMatrix_rowSum (termCoordinates i S) x
    _ = (n : ℝ) * (eligibleLabelSets n).card := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one]

/-- Lemma "Elementary properties of `K`": (a) `K` is symmetric with
nonnegative real entries, (b) `K(x, y) > 0` only if `F_n(x + y) = 1`, and
(c) every row of `K` sums to `1`.  The three parts are
`outerMatrix_symmetric` with `outerMatrix_nonneg`,
`outerMatrix_pos_imp_outerFunction`, and `outerMatrix_mulVec_one`. -/
@[tutorial_box "lem:tutorial-matrix-properties"]
theorem outerMatrix_properties {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n) :
    ((outerMatrix n).transpose = outerMatrix n ∧
      ∀ x y : (Fin n × Fin n) → GadgetVector, 0 ≤ outerMatrix n x y) ∧
    (∀ x y : (Fin n × Fin n) → GadgetVector,
      0 < outerMatrix n x y → outerFunction ranks hn (x + y)) ∧
    (outerMatrix n).mulVec (1 : ((Fin n × Fin n) → GadgetVector) → ℝ) = 1 :=
  ⟨⟨outerMatrix_symmetric n, outerMatrix_nonneg n⟩,
    outerMatrix_pos_imp_outerFunction ranks hn, outerMatrix_mulVec_one hn⟩

end

end DDNNFNegation
