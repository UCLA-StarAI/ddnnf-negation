import DDNNFNegation.Eigenvalues
import TutorialBox

/-!
# Bounding the negative eigenvalues

Each eigenvalue is a positive prefactor times the mean of the bucket
averages. With at most `n²/30` nonzero coordinates, the bucket bound and
arithmetic-geometric mean inequality make that mean nonnegative.
Otherwise, the prefactor is at most `(2/3)^{n²/30}` and the mean is at
least `-1`. This gives the spectral lower bound `-spectralEpsilon n`.
-/

namespace DDNNFNegation

open Finset
open scoped Real

section WeightRatio

/-! ## The ratios `q_ξ` -/

theorem weightZero_inner_product_ne_zero (ξ : GadgetVector) :
    weightParityInnerProduct weightZero ξ ≠ 0 :=
  (weightZero_inner_product_pos ξ).ne'

/-- The ratio `q_ξ = ⟨ω₁, par_ξ⟩ / ⟨ω₀, par_ξ⟩`. -/
noncomputable def weightRatio (ξ : GadgetVector) : ℝ :=
  weightParityInnerProduct weightOne ξ / weightParityInnerProduct weightZero ξ

/-- `q_ξ ∈ {1, -1/2, 2/3}`: `1` at the trivial parameter, `-1/2` at the
nonzero parameters with `Q = 0`, `2/3` at the parameters with `Q = 1`. -/
theorem weightRatio_eq (ξ : GadgetVector) :
    weightRatio ξ = if ξ = 0 then 1 else if quadForm ξ = 0 then -(1 / 2) else 2 / 3 := by
  rw [weightRatio, weightOne_inner_product, weightZero_inner_product]
  split_ifs <;> norm_num

/-- At the zero parity parameter both weight sums are one, so their ratio is one. -/
theorem weightRatio_trivial : weightRatio (0 : GadgetVector) = 1 := by
  rw [weightRatio_eq, if_pos rfl]

/-- `⟨ω₀, par_ξ⟩ ≤ 2/3` at every nonzero parameter. -/
theorem weightZero_inner_product_le_two_thirds (ξ : GadgetVector) (hξ : ξ ≠ 0) :
    weightParityInnerProduct weightZero ξ ≤ 2 / 3 := by
  rw [weightZero_inner_product, if_neg hξ]
  split_ifs <;> norm_num

/-- Every local weight ratio has absolute value at most one. -/
theorem abs_weightRatio_le_one (ξ : GadgetVector) : |weightRatio ξ| ≤ 1 := by
  rw [weightRatio_eq]
  split_ifs <;> rw [abs_le] <;> constructor <;> norm_num

/-- `1 + q_ξ ≥ 1/2` at every parameter. -/
theorem one_add_weightRatio_ge (ξ : GadgetVector) : 1 / 2 ≤ 1 + weightRatio ξ := by
  rw [weightRatio_eq]
  split_ifs <;> norm_num

/-- The absolute value of a product of ratios is at most `1`. -/
theorem abs_prod_weightRatio_le_one {α : Type*} (s : Finset α) (f : α → GadgetVector) :
    |∏ a ∈ s, weightRatio (f a)| ≤ 1 := by
  rw [abs_prod]
  apply prod_le_one
  · intro a _
    exact abs_nonneg _
  · intro a _
    exact abs_weightRatio_le_one _

end WeightRatio

section Prefactor

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The prefactor `γ(ξ)` and the term eigenvalues -/

/-- The prefactor `γ(ξ) = ∏_u ⟨ω₀, par_{ξ_u}⟩`. -/
noncomputable def spectralPrefactor (ξ : Ω → GadgetVector) : ℝ :=
  ∏ u, weightParityInnerProduct weightZero (ξ u)

omit [DecidableEq Ω] in
/-- The product of the zero-table inner products is positive. -/
theorem spectralPrefactor_pos (ξ : Ω → GadgetVector) : 0 < spectralPrefactor ξ :=
  prod_pos fun u _ => weightZero_inner_product_pos (ξ u)

omit [Fintype Ω] in
/-- One factor of the product, rewritten as `⟨ω₀, par_{ξ_u}⟩` times
`q_{ξ_u}` on the term and times `1` elsewhere. -/
theorem term_product_factor (term : Finset Ω) (ξ : Ω → GadgetVector) (u : Ω) :
    (if u ∈ term then weightParityInnerProduct weightOne (ξ u)
      else weightParityInnerProduct weightZero (ξ u)) =
      weightParityInnerProduct weightZero (ξ u) *
        (if u ∈ term then weightRatio (ξ u) else 1) := by
  have h := weightZero_inner_product_ne_zero (ξ u)
  by_cases hu : u ∈ term
  · rw [if_pos hu, if_pos hu, weightRatio]
    field_simp
  · rw [if_neg hu, if_neg hu, mul_one]

/-- The eigenvalue of `K_{i,S}` at `par_ξ` is `γ(ξ) ∏_{u ∈ P_{i,S}} q_{ξ_u}`. -/
theorem termEigenvalue_eq (term : Finset Ω) (ξ : Ω → GadgetVector) :
    termEigenvalue term ξ = spectralPrefactor ξ * ∏ u ∈ term, weightRatio (ξ u) := by
  calc termEigenvalue term ξ
      = ∏ u, weightParityInnerProduct weightZero (ξ u) *
          (if u ∈ term then weightRatio (ξ u) else 1) := by
        unfold termEigenvalue
        exact prod_congr rfl fun u _ => term_product_factor term ξ u
    _ = spectralPrefactor ξ * ∏ u, (if u ∈ term then weightRatio (ξ u) else 1) := by
        rw [prod_mul_distrib]
        rfl
    _ = spectralPrefactor ξ * ∏ u ∈ term, weightRatio (ξ u) := by
        rw [← prod_filter, filter_univ_mem]

/-- The coordinates at which `ξ` is nonzero. -/
def nonzeroCoordinates (ξ : Ω → GadgetVector) : Finset Ω :=
  univ.filter fun u => ξ u ≠ 0

omit [DecidableEq Ω] in
/-- `γ(ξ) ≤ (2/3)^k` when `ξ` has `k` nonzero coordinates: a nonzero
coordinate contributes a factor at most `2/3` and a zero coordinate the
factor `1`. -/
theorem spectralPrefactor_le (ξ : Ω → GadgetVector) :
    spectralPrefactor ξ ≤ (2 / 3 : ℝ) ^ (nonzeroCoordinates ξ).card := by
  have hprod : spectralPrefactor ξ =
      ∏ u ∈ nonzeroCoordinates ξ, weightParityInnerProduct weightZero (ξ u) := by
    rw [spectralPrefactor, nonzeroCoordinates, prod_filter]
    apply prod_congr rfl
    intro u _
    by_cases hξ : ξ u = 0
    · simp [hξ, weightZero_inner_product_trivial]
    · simp [hξ]
  rw [hprod, ← prod_const]
  apply prod_le_prod
  · intro u _
    exact (weightZero_inner_product_pos _).le
  · intro u hu
    exact weightZero_inner_product_le_two_thirds _ (mem_filter.mp hu).2

end Prefactor

section BucketAverage

/-! ## Bucket averages and the eigenvalue formula -/

/-- The bucket average `μ_i(ξ) = E_S[∏_{u ∈ P_{i,S}} q_{ξ_u}]` over the
eligible label sets `S`. -/
noncomputable def bucketAverage (n : ℕ) (i : Fin n) (ξ : (Fin n × Fin n) → GadgetVector) : ℝ :=
  (∑ S ∈ eligibleLabelSets n, ∏ u ∈ termCoordinates i S, weightRatio (ξ u)) /
    (eligibleLabelSets n).card

/-- `λ_ξ = γ(ξ) (1/n) ∑_i μ_i(ξ)`. -/
@[tutorial_box "lem:tutorial-eigenvalue-formula"]
theorem eigenvalue_formula (n : ℕ) (ξ : (Fin n × Fin n) → GadgetVector) :
    outerEigenvalue n ξ = spectralPrefactor ξ * (1 / n) * ∑ i, bucketAverage n i ξ := by
  simp only [outerEigenvalue, bucketAverage, termEigenvalue_eq]
  rw [← sum_div]
  simp only [← mul_sum]
  ring

/-- `|μ_i(ξ)| ≤ 1`, because `|q| ≤ 1`. -/
theorem abs_bucketAverage_le_one (n : ℕ) (i : Fin n) (ξ : (Fin n × Fin n) → GadgetVector) :
    |bucketAverage n i ξ| ≤ 1 := by
  have hM : (0 : ℝ) < (eligibleLabelSets n).card := by
    exact_mod_cast card_eligibleLabelSets_pos n
  rw [bucketAverage, abs_div, abs_of_pos hM, div_le_one hM]
  calc |∑ S ∈ eligibleLabelSets n, ∏ u ∈ termCoordinates i S, weightRatio (ξ u)|
      ≤ ∑ S ∈ eligibleLabelSets n, |∏ u ∈ termCoordinates i S, weightRatio (ξ u)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ eligibleLabelSets n, (1 : ℝ) :=
        sum_le_sum fun S _ => abs_prod_weightRatio_le_one _ _
    _ = (eligibleLabelSets n).card := by simp

/-! ## The bucket bound -/

/-- The nonzero coordinates of `ξ` in bucket `i`; `ℓ_i` is their number. -/
def bucketSupport (n : ℕ) (i : Fin n) (ξ : (Fin n × Fin n) → GadgetVector) : Finset (Fin n) :=
  univ.filter fun a => ξ (i, a) ≠ 0

/-- The nonzero coordinates are counted bucket by bucket: `k = ∑_i ℓ_i`. -/
theorem card_nonzeroCoordinates_eq_sum (n : ℕ) (ξ : (Fin n × Fin n) → GadgetVector) :
    (nonzeroCoordinates ξ).card = ∑ i, (bucketSupport n i ξ).card := by
  simp only [nonzeroCoordinates, bucketSupport, card_filter, Fintype.sum_prod_type]

/-- Summing `∏_{u ∈ P_{i,S}} q_{ξ_u}` over all label sets `S` gives
`∏_a (1 + q_{ξ_{(i,a)}})`. -/
theorem sum_prod_weightRatio_eq (n : ℕ) (i : Fin n) (ξ : (Fin n × Fin n) → GadgetVector) :
    ∑ S : Finset (Fin n), ∏ u ∈ termCoordinates i S, weightRatio (ξ u) =
      ∏ a, (1 + weightRatio (ξ (i, a))) := by
  rw [← sum_prod_eq_prod_one_add]
  apply sum_congr rfl
  intro S _
  exact prod_termCoordinates i S fun u => weightRatio (ξ u)

/-- `2^n (1/4)^ℓ = (1/2)^ℓ 2^{n - ℓ}` for `ℓ ≤ n`. -/
theorem two_pow_sub_mul_eq (n ℓ : ℕ) (h : ℓ ≤ n) :
    (2 : ℝ) ^ n * (1 / 4) ^ ℓ = (1 / 2) ^ ℓ * 2 ^ (n - ℓ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  calc (2 : ℝ) ^ (ℓ + m) * (1 / 4) ^ ℓ
      = (2 * (1 / 4)) ^ ℓ * 2 ^ m := by
        rw [pow_add, mul_pow]
        ring
    _ = (1 / 2) ^ ℓ * 2 ^ m := by norm_num

/-- `∏_a (1 + q_{ξ_{(i,a)}}) ≥ 2^n 4^{-ℓ_i}`: a zero coordinate contributes
the factor `1 + 1 = 2` and a nonzero one at least `1/2`. -/
theorem prod_one_add_weightRatio_ge (n : ℕ) (i : Fin n) (ξ : (Fin n × Fin n) → GadgetVector) :
    (2 : ℝ) ^ n * (1 / 4) ^ (bucketSupport n i ξ).card ≤
      ∏ a, (1 + weightRatio (ξ (i, a))) := by
  have hfactor : ∀ a, (if ξ (i, a) ≠ 0 then (1 / 2 : ℝ) else 2) ≤
      1 + weightRatio (ξ (i, a)) := by
    intro a
    by_cases h : ξ (i, a) = 0
    · rw [if_neg (not_not.mpr h), h, weightRatio_trivial]
      norm_num
    · rw [if_pos h]
      exact one_add_weightRatio_ge _
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun a => ξ (i, a) ≠ 0)
  rw [card_univ, Fintype.card_fin] at hsplit
  have hℓ : (bucketSupport n i ξ).card ≤ n := by
    unfold bucketSupport
    omega
  calc (2 : ℝ) ^ n * (1 / 4) ^ (bucketSupport n i ξ).card
      = (1 / 2) ^ (bucketSupport n i ξ).card * 2 ^ (n - (bucketSupport n i ξ).card) :=
        two_pow_sub_mul_eq n _ hℓ
    _ = ∏ a, (if ξ (i, a) ≠ 0 then (1 / 2 : ℝ) else 2) := by
        rw [prod_ite, prod_const, prod_const]
        unfold bucketSupport
        congr 2
        omega
    _ ≤ ∏ a, (1 + weightRatio (ξ (i, a))) := by
        apply prod_le_prod
        · intro a _
          split_ifs <;> norm_num
        · intro a _
          exact hfactor a

/-- `μ_i(ξ) ≥ (4^{-ℓ_i} - p)/(1 - p)`. -/
theorem bucketAverage_ge (n : ℕ) (i : Fin n) (ξ : (Fin n × Fin n) → GadgetVector) :
    ((1 / 4 : ℝ) ^ (bucketSupport n i ξ).card - ineligibleFraction n) /
        (1 - ineligibleFraction n) ≤
      bucketAverage n i ξ := by
  set p := ineligibleFraction n with hp
  have hp1 : 0 < 1 - p := by linarith [ineligibleFraction_lt_one n]
  have hM : ((eligibleLabelSets n).card : ℝ) = 2 ^ n * (1 - p) := card_eligibleLabelSets_eq n
  have hMpos : (0 : ℝ) < (eligibleLabelSets n).card := by
    exact_mod_cast card_eligibleLabelSets_pos n
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfull : (2 : ℝ) ^ n * (1 / 4) ^ (bucketSupport n i ξ).card ≤
      ∑ S : Finset (Fin n), ∏ u ∈ termCoordinates i S, weightRatio (ξ u) := by
    rw [sum_prod_weightRatio_eq]
    exact prod_one_add_weightRatio_ge n i ξ
  have hineligible :
      |∑ S ∈ ineligibleLabelSets n, ∏ u ∈ termCoordinates i S, weightRatio (ξ u)| ≤
        2 ^ n * p := by
    calc |∑ S ∈ ineligibleLabelSets n, ∏ u ∈ termCoordinates i S, weightRatio (ξ u)|
        ≤ ∑ S ∈ ineligibleLabelSets n, |∏ u ∈ termCoordinates i S, weightRatio (ξ u)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ ineligibleLabelSets n, (1 : ℝ) :=
          sum_le_sum fun S _ => abs_prod_weightRatio_le_one _ _
      _ = (ineligibleLabelSets n).card := by simp
      _ = 2 ^ n * p := by
          rw [hp, ineligibleFraction, mul_div_assoc', mul_div_cancel_left₀ _ h2.ne']
  have heligible : 2 ^ n * ((1 / 4) ^ (bucketSupport n i ξ).card - p) ≤
      ∑ S ∈ eligibleLabelSets n, ∏ u ∈ termCoordinates i S, weightRatio (ξ u) := by
    have hsplit := sum_eligible_add_sum_ineligible n
      fun S => ∏ u ∈ termCoordinates i S, weightRatio (ξ u)
    have habs := (abs_le.mp hineligible).2
    linarith
  rw [bucketAverage, div_le_div_iff₀ hp1 hMpos, hM]
  calc ((1 / 4 : ℝ) ^ (bucketSupport n i ξ).card - p) * (2 ^ n * (1 - p))
      = 2 ^ n * ((1 / 4) ^ (bucketSupport n i ξ).card - p) * (1 - p) := by ring
    _ ≤ (∑ S ∈ eligibleLabelSets n, ∏ u ∈ termCoordinates i S, weightRatio (ξ u)) *
          (1 - p) :=
        mul_le_mul_of_nonneg_right heligible hp1.le

end BucketAverage

/-- The inequality of arithmetic and geometric means for the numbers
`b ^ f i`: the mean of `b ^ f i` is at least `b` raised to the mean of the
exponents. -/
theorem rpow_average_le_average_rpow
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (b : ℝ) (hb : 0 < b) (f : ι → ℝ) :
    b ^ ((∑ i ∈ s, f i) / s.card) ≤
      (∑ i ∈ s, b ^ (f i)) / s.card := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast s.card_pos.mpr hs
  have hamgm := Real.geom_mean_le_arith_mean_weighted s
    (fun _ => 1 / (s.card : ℝ)) (fun i => b ^ (f i))
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self hcard.ne'])
    (fun i _ => (Real.rpow_pos_of_pos hb _).le)
  have hgeom : ∏ i ∈ s, (b ^ (f i)) ^ (1 / (s.card : ℝ)) =
      b ^ ((∑ i ∈ s, f i) / s.card) := by
    rw [div_eq_mul_one_div (∑ i ∈ s, f i), Finset.sum_mul,
      Real.rpow_sum_of_pos hb]
    apply Finset.prod_congr rfl
    intro i _hi
    rw [← Real.rpow_mul hb.le]
  rw [hgeom] at hamgm
  calc
    b ^ ((∑ i ∈ s, f i) / s.card) ≤
        ∑ i ∈ s, 1 / (s.card : ℝ) * b ^ (f i) := hamgm
    _ = (∑ i ∈ s, b ^ (f i)) / s.card := by
      rw [← Finset.mul_sum, one_div, inv_mul_eq_div]

/-- `(1/4)^x = 2^{-2x}` for real `x`. -/
theorem quarter_rpow_eq_two_rpow (x : ℝ) :
    (1 / 4 : ℝ) ^ x = (2 : ℝ) ^ (-(2 * x)) := by
  have h4 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]
    norm_num
  rw [h4, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- With at most `n²/30` nonzero coordinates, the bucket averages have
nonnegative sum. The bucket bound and arithmetic-geometric mean inequality
give `(1/n) ∑_i 4^{-ℓ_i} ≥ 4^{-k/n} ≥ 2^{-n/15} ≥ p`. -/
theorem sum_bucketAverage_nonneg (n : ℕ) (hn : 0 < n)
    (ξ : (Fin n × Fin n) → GadgetVector)
    (hk : ((nonzeroCoordinates ξ).card : ℝ) ≤ (n : ℝ) ^ 2 / 30) :
    0 ≤ ∑ i, bucketAverage n i ξ := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set p := ineligibleFraction n with hp
  have hp1 : 0 < 1 - p := by linarith [ineligibleFraction_lt_one n]
  have hbucket : ∀ i,
      ((1 / 4 : ℝ) ^ ((bucketSupport n i ξ).card : ℝ) - p) / (1 - p) ≤
        bucketAverage n i ξ := by
    intro i
    rw [Real.rpow_natCast]
    exact bucketAverage_ge n i ξ
  have hamgm := rpow_average_le_average_rpow (univ : Finset (Fin n)) univ_nonempty
    (1 / 4 : ℝ) (by norm_num) fun i => ((bucketSupport n i ξ).card : ℝ)
  simp only [card_univ, Fintype.card_fin] at hamgm
  have hk' : ∑ i, ((bucketSupport n i ξ).card : ℝ) = (nonzeroCoordinates ξ).card := by
    simp only [card_nonzeroCoordinates_eq_sum, Nat.cast_sum]
  rw [hk', le_div_iff₀ hnreal] at hamgm
  have hexp : ((nonzeroCoordinates ξ).card : ℝ) / n ≤ n / 30 := by
    rw [div_le_iff₀ hnreal]
    linarith
  have hpow : (2 : ℝ) ^ (-(n : ℝ) / 15) ≤
      (1 / 4 : ℝ) ^ (((nonzeroCoordinates ξ).card : ℝ) / n) := by
    rw [quarter_rpow_eq_two_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hpk : p ≤ (1 / 4 : ℝ) ^ (((nonzeroCoordinates ξ).card : ℝ) / n) :=
    (most_label_sets_eligible n).trans hpow
  have hsum : (n : ℝ) * p ≤ ∑ i, (1 / 4 : ℝ) ^ ((bucketSupport n i ξ).card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hpk hnreal.le
    linarith
  have hlower : ∑ i, (((1 / 4 : ℝ) ^ ((bucketSupport n i ξ).card : ℝ) - p) / (1 - p)) ≤
      ∑ i, bucketAverage n i ξ :=
    sum_le_sum fun i _ => hbucket i
  have hnonneg :
      0 ≤ ∑ i, (((1 / 4 : ℝ) ^ ((bucketSupport n i ξ).card : ℝ) - p) / (1 - p)) := by
    rw [← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply div_nonneg _ hp1.le
    linarith
  exact hnonneg.trans hlower

/-- A negative eigenvalue requires more than `n²/30` nonzero coordinates.
Otherwise, the eigenvalue formula is a positive prefactor times a
nonnegative mean of bucket averages. -/
@[tutorial_box "lem:tutorial-negative-requires-many"]
theorem negative_needs_many {n : ℕ} (hn : 0 < n)
    (ξ : (Fin n × Fin n) → GadgetVector)
    (hneg : outerEigenvalue n ξ < 0) :
    (n : ℝ) ^ 2 / 30 < ((nonzeroCoordinates ξ).card : ℝ) := by
  by_contra hk
  have hk' : ((nonzeroCoordinates ξ).card : ℝ) ≤ (n : ℝ) ^ 2 / 30 := not_lt.mp hk
  have hnonneg : 0 ≤ outerEigenvalue n ξ := by
    rw [eigenvalue_formula n ξ]
    exact mul_nonneg (mul_nonneg (spectralPrefactor_pos ξ).le (by positivity))
      (sum_bucketAverage_nonneg n hn ξ hk')
  linarith

/-- The error bound `ε = (2/3)^{n²/30}` shared by the spectral estimate,
zero-square bound, and rectangle count. Its reciprocal grows as
`2^{Ω(n²)}`. -/
noncomputable def spectralEpsilon (n : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ ((n : ℝ) ^ 2 / 30)

/-- The spectral error bound is strictly positive, allowing division by it. -/
theorem spectralEpsilon_pos (n : ℕ) : 0 < spectralEpsilon n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The spectral error bound is nonnegative for use in product inequalities. -/
theorem spectralEpsilon_nonneg (n : ℕ) : 0 ≤ spectralEpsilon n :=
  (spectralEpsilon_pos n).le

/-- Lemma "Spectral estimate": `λ_ξ ≥ -ε` at every parameter `ξ`,
with `ε = (2/3)^{n²/30}` (`spectralEpsilon`).  A nonnegative eigenvalue
needs no bound, and by the previous lemma a negative one has more than
`n²/30` nonzero coordinates, so `γ(ξ) ≤ (2/3)^{n²/30}` while the mean of
the bucket averages is at least `-1`. -/
@[tutorial_box "lem:tutorial-spectral-estimate"]
theorem spectral_estimate {n : ℕ} (hn : 0 < n) (ξ : (Fin n × Fin n) → GadgetVector) :
    -spectralEpsilon n ≤ outerEigenvalue n ξ := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hεnonneg : 0 ≤ spectralEpsilon n := spectralEpsilon_nonneg n
  by_cases hneg : outerEigenvalue n ξ < 0
  · have hk := negative_needs_many hn ξ hneg
    rw [eigenvalue_formula n ξ]
    have hγpos := spectralPrefactor_pos ξ
    have hγ : spectralPrefactor ξ ≤ spectralEpsilon n :=
      calc spectralPrefactor ξ
          ≤ (2 / 3 : ℝ) ^ (nonzeroCoordinates ξ).card := spectralPrefactor_le ξ
        _ = (2 / 3 : ℝ) ^ ((nonzeroCoordinates ξ).card : ℝ) := by
            rw [Real.rpow_natCast]
        _ ≤ spectralEpsilon n :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hk.le
    have hmean : -1 ≤ (1 / (n : ℝ)) * ∑ i, bucketAverage n i ξ := by
      have hsum : -(n : ℝ) ≤ ∑ i, bucketAverage n i ξ := by
        calc -(n : ℝ) = ∑ _i : Fin n, (-1 : ℝ) := by simp
          _ ≤ ∑ i, bucketAverage n i ξ :=
              sum_le_sum fun i _ => (abs_le.mp (abs_bucketAverage_le_one n i ξ)).1
      have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / n)
      calc (-1 : ℝ) = (1 / (n : ℝ)) * (-(n : ℝ)) := by field_simp
        _ ≤ (1 / (n : ℝ)) * ∑ i, bucketAverage n i ξ := hscaled
    calc -spectralEpsilon n ≤ -spectralPrefactor ξ := neg_le_neg hγ
      _ ≤ spectralPrefactor ξ * ((1 / n) * ∑ i, bucketAverage n i ξ) := by
          nlinarith [mul_nonneg hγpos.le
            (show (0 : ℝ) ≤ (1 / n) * ∑ i, bucketAverage n i ξ + 1 by linarith)]
      _ = spectralPrefactor ξ * (1 / n) * ∑ i, bucketAverage n i ξ := by ring
  · linarith

end DDNNFNegation
