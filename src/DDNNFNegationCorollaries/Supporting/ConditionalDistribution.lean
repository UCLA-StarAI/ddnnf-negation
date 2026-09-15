import DDNNFNegation
import DDNNFNegationCorollaries.Supporting.ProductMeasure

/-!
# Conditional probabilities

Definitions and normalization facts used to express the uniform
complement distribution in the probabilistic circuit corollary.
-/

namespace DDNNFNegation

open Finset ProductDist
open Classical

section Conditional

variable {N : ℕ} (π : ProductDist N) (L : (Fin N → Bool) → Prop)

/-- `Z = Pr_π[¬L]`. -/
noncomputable def normalizer : ℚ := π.mass fun x => ¬L x

/-- The conditional distribution `p(x) = π(x) [¬L x] / Z`. -/
noncomputable def condProb (x : Fin N → Bool) : ℚ :=
  (if L x then 0 else π.prob x) / normalizer π L

/-- The conditional probability of the evidence `e`. -/
noncomputable def condMass (e : Evidence N) : ℚ :=
  π.mass (fun x => Consistent e x ∧ ¬L x) / normalizer π L

theorem normalizer_eq_sum : normalizer π L = ∑ x, if L x then 0 else π.prob x := by
  unfold normalizer mass
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : L x <;> simp [h]

theorem normalizer_nonneg : 0 ≤ normalizer π L := π.mass_nonneg _

theorem normalizer_pos_of_exists (h : ∃ x, ¬L x) : 0 < normalizer π L := by
  obtain ⟨x, hx⟩ := h
  unfold normalizer mass
  apply Finset.sum_pos'
  · intro y _
    split_ifs
    · exact (π.prob_pos y).le
    · exact le_rfl
  · exact ⟨x, Finset.mem_univ x, by rw [if_pos hx]; exact π.prob_pos x⟩

theorem condProb_nonneg (x : Fin N → Bool) : 0 ≤ condProb π L x := by
  unfold condProb
  apply div_nonneg _ (normalizer_nonneg π L)
  split_ifs
  · exact le_rfl
  · exact (π.prob_pos x).le

theorem sum_condProb (h : ∃ x, ¬L x) : ∑ x, condProb π L x = 1 := by
  unfold condProb
  rw [← Finset.sum_div, ← normalizer_eq_sum]
  exact div_self (normalizer_pos_of_exists π L h).ne'

theorem condProb_pos_iff (h : ∃ x, ¬L x) (x : Fin N → Bool) :
    0 < condProb π L x ↔ ¬L x := by
  unfold condProb
  rw [div_pos_iff_of_pos_right (normalizer_pos_of_exists π L h)]
  by_cases hx : L x <;> simp [hx, π.prob_pos x]

theorem condMass_eq_sum (e : Evidence N) :
    condMass π L e = ∑ x, if Consistent e x then condProb π L x else 0 := by
  unfold condMass condProb mass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : Consistent e x <;> by_cases hL : L x <;> simp [hc, hL]

end Conditional

end DDNNFNegation
