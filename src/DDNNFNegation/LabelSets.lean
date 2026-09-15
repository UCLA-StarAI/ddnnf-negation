import Mathlib
import TutorialBox

/-!
# Eligible label sets and term coordinates

An eligible label set `S` has `3 * |S| ≥ n`; together with bucket `i` it
determines the term's coordinate set `{i} × S`. The product-sum identity
`sum_prod_eq_prod_one_add` supports the eigenvalue calculation.

The fraction `p` of ineligible sets is at most `2^{-n/15}`: each such
set has weight `2^{n/3 - |S|} ≥ 1`, and the weights over all sets sum to
`2^{n/3} * (3/2)^n`. Consequently the number of eligible sets is
`2^n * (1 - p)`, and `p < 1` because the full set is eligible.
-/

namespace DDNNFNegation

open Finset

/-! ## The coordinate set of an outer term -/

/-- The coordinate set `P_{i,S} = {i} × S` of the outer term with bucket
`i` and label set `S`: the labels of `S`, embedded into bucket `i`. -/
def termCoordinates {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  S.image fun a => (i, a)

/-- A coordinate belongs to a term exactly when its bucket agrees and its label is selected. -/
theorem mem_termCoordinates {n : ℕ} {i j a : Fin n} {S : Finset (Fin n)} :
    (j, a) ∈ termCoordinates i S ↔ j = i ∧ a ∈ S := by
  simp [termCoordinates, and_comm, eq_comm]

/-- Embedding a label set into one bucket preserves its cardinality. -/
theorem card_termCoordinates {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    (termCoordinates i S).card = S.card := by
  rw [termCoordinates, card_image_of_injective]
  intro a b hab
  exact congrArg Prod.snd hab

/-- A product over `P_{i,S}` is a product over the labels of `S`. -/
theorem prod_termCoordinates {n : ℕ} {R : Type*} [CommMonoid R]
    (i : Fin n) (S : Finset (Fin n)) (f : Fin n × Fin n → R) :
    ∏ u ∈ termCoordinates i S, f u = ∏ a ∈ S, f (i, a) := by
  rw [termCoordinates, prod_image]
  intro a _ b _ hab
  exact congrArg Prod.snd hab

/-! ## Eligible label sets -/

/-- The eligible label sets: `S ⊆ [n]₀` with `3 |S| ≥ n`. -/
def eligibleLabelSets (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter fun S => n ≤ 3 * S.card

/-- The ineligible label sets: `S ⊆ [n]₀` with `3 |S| < n`. -/
def ineligibleLabelSets (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter fun S => 3 * S.card < n

/-- Eligibility is precisely the threshold `n ≤ 3 |S|`. -/
theorem mem_eligibleLabelSets {n : ℕ} {S : Finset (Fin n)} :
    S ∈ eligibleLabelSets n ↔ n ≤ 3 * S.card := by
  simp [eligibleLabelSets]

/-- Ineligibility is the strict failure of the label-set threshold. -/
theorem mem_ineligibleLabelSets {n : ℕ} {S : Finset (Fin n)} :
    S ∈ ineligibleLabelSets n ↔ 3 * S.card < n := by
  simp [ineligibleLabelSets]

/-- The full label set is eligible. -/
theorem univ_mem_eligibleLabelSets (n : ℕ) :
    (univ : Finset (Fin n)) ∈ eligibleLabelSets n := by
  rw [mem_eligibleLabelSets, card_univ, Fintype.card_fin]
  omega

/-- At least one label set is eligible, so averaging over eligible sets has a nonzero
denominator. -/
theorem card_eligibleLabelSets_pos (n : ℕ) : 0 < (eligibleLabelSets n).card :=
  card_pos.mpr ⟨_, univ_mem_eligibleLabelSets n⟩

/-- A sum over all `2^n` label sets splits into the eligible and the
ineligible ones. -/
theorem sum_eligible_add_sum_ineligible (n : ℕ) {R : Type*} [AddCommMonoid R]
    (f : Finset (Fin n) → R) :
    ∑ S ∈ eligibleLabelSets n, f S + ∑ S ∈ ineligibleLabelSets n, f S =
      ∑ S, f S := by
  have hnot : (univ : Finset (Finset (Fin n))).filter
      (fun S => ¬ n ≤ 3 * S.card) = ineligibleLabelSets n := by
    ext S
    simp [ineligibleLabelSets]
  rw [← hnot, eligibleLabelSets, sum_filter_add_sum_filter_not]

/-- There are `2^n` label sets. -/
theorem card_eligible_add_card_ineligible (n : ℕ) :
    (eligibleLabelSets n).card + (ineligibleLabelSets n).card = 2 ^ n := by
  have h := sum_eligible_add_sum_ineligible n (fun _ => (1 : ℕ))
  simpa [Fintype.card_finset] using h

/-- The product identity behind the bucket average: summing
`∏_{a ∈ S} q a` over all label sets `S ⊆ [n]₀` gives
`∏_{a ∈ [n]₀} (1 + q a)`. -/
theorem sum_prod_eq_prod_one_add (n : ℕ) {R : Type*} [CommSemiring R]
    (q : Fin n → R) :
    ∑ S : Finset (Fin n), ∏ a ∈ S, q a = ∏ a, (1 + q a) := by
  rw [prod_one_add, powerset_univ]

/-! ## Most label sets are eligible -/

/-- The fraction `p` of the `2^n` label sets that are ineligible. -/
noncomputable def ineligibleFraction (n : ℕ) : ℝ :=
  ((ineligibleLabelSets n).card : ℝ) / 2 ^ n

/-- The number of eligible label sets is `2^n (1 - p)`. -/
theorem card_eligibleLabelSets_eq (n : ℕ) :
    ((eligibleLabelSets n).card : ℝ) = 2 ^ n * (1 - ineligibleFraction n) := by
  have h : ((eligibleLabelSets n).card : ℝ) + (ineligibleLabelSets n).card =
      2 ^ n := by
    exact_mod_cast card_eligible_add_card_ineligible n
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [ineligibleFraction, mul_sub, mul_one, mul_div_cancel₀ _ h2]
  linarith

/-- `p < 1`, because the full label set is eligible. -/
theorem ineligibleFraction_lt_one (n : ℕ) : ineligibleFraction n < 1 := by
  have hpos : (0 : ℝ) < (eligibleLabelSets n).card := by
    exact_mod_cast card_eligibleLabelSets_pos n
  rw [card_eligibleLabelSets_eq] at hpos
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  by_contra hnot
  have hle : (2 : ℝ) ^ n * (1 - ineligibleFraction n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h2.le (by linarith [not_lt.mp hnot])
  linarith

/-- Every ineligible set has weight `2^{n/3 - |S|} ≥ 1`, and the weights of
all label sets sum to `2^{n/3} (3/2)^n` by the product identity. -/
theorem card_ineligibleLabelSets_le (n : ℕ) :
    ((ineligibleLabelSets n).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 3) * (3 / 2) ^ n := by
  have hweight : ∀ S ∈ ineligibleLabelSets n,
      (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3 - S.card) := by
    intro S hS
    have h := mem_ineligibleLabelSets.mp hS
    apply Real.one_le_rpow (by norm_num)
    have : (3 * S.card : ℝ) < n := by exact_mod_cast h
    linarith
  calc ((ineligibleLabelSets n).card : ℝ)
      = ∑ _S ∈ ineligibleLabelSets n, (1 : ℝ) := by simp
    _ ≤ ∑ S ∈ ineligibleLabelSets n, (2 : ℝ) ^ ((n : ℝ) / 3 - S.card) :=
        sum_le_sum hweight
    _ ≤ ∑ S : Finset (Fin n), (2 : ℝ) ^ ((n : ℝ) / 3 - S.card) := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
        intro S _ _
        exact (Real.rpow_pos_of_pos (by norm_num) _).le
    _ = (2 : ℝ) ^ ((n : ℝ) / 3) *
          ∑ S : Finset (Fin n), ∏ _a ∈ S, (1 / 2 : ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, prod_const,
          one_div, inv_pow, div_eq_mul_inv]
    _ = (2 : ℝ) ^ ((n : ℝ) / 3) * (3 / 2) ^ n := by
        rw [sum_prod_eq_prod_one_add, prod_const, card_univ, Fintype.card_fin]
        norm_num

/-- `2^{n/3} (3/2)^n ≤ 2^n · 2^{-n/15}`, because `(3/2)^5 ≤ 2^3`. -/
theorem two_rpow_third_mul_le (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 3) * (3 / 2) ^ n ≤
      (2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 15) := by
  have hbase : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [← pow_le_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : (5 : ℕ) ≠ 0)]
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((3 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
    rw [show (3 : ℝ) / 5 * ((5 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  have h32 : (3 / 2 : ℝ) ^ n ≤ (2 : ℝ) ^ ((3 : ℝ) / 5 * n) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hbase n
  calc (2 : ℝ) ^ ((n : ℝ) / 3) * (3 / 2) ^ n
      ≤ (2 : ℝ) ^ ((n : ℝ) / 3) * (2 : ℝ) ^ ((3 : ℝ) / 5 * n) := by
        exact mul_le_mul_of_nonneg_left h32 (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((n : ℝ) / 3 + (3 : ℝ) / 5 * n) := by
        rw [Real.rpow_add (by norm_num)]
    _ = (2 : ℝ) ^ ((n : ℝ) + (-(n : ℝ) / 15)) := by
        congr 1
        ring
    _ = (2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 15) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

/-- Lemma "Most label sets are eligible": `p ≤ 2^{-n/15}`. -/
@[tutorial_box "lem:tutorial-most-label-sets-eligible"]
theorem most_label_sets_eligible (n : ℕ) :
    ineligibleFraction n ≤ (2 : ℝ) ^ (-(n : ℝ) / 15) := by
  have h := (card_ineligibleLabelSets_le n).trans (two_rpow_third_mul_le n)
  rw [ineligibleFraction, div_le_iff₀ (by positivity)]
  calc ((ineligibleLabelSets n).card : ℝ)
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 15) := h
    _ = (2 : ℝ) ^ (-(n : ℝ) / 15) * (2 : ℝ) ^ n := mul_comm _ _

end DDNNFNegation
