import Mathlib

/-!
# Counting a cover on the zero fiber

A cover contains every assignment in the zero fiber. Bounding the
intersection of each rectangle with that fiber therefore gives a lower
bound on the number of rectangles. This file isolates the finite counting
argument from the spectral and encoder estimates used to bound each part.
-/

namespace DDNNFNegation

open Finset

variable {Ω J : Type*} [DecidableEq Ω] [Fintype J] (Z : Finset Ω) (R : J → Finset Ω)

/-- A set covered by finitely many sets is at most as large as the sum of
its intersections with them. -/
theorem card_le_sum_card_inter_of_cover (hcover : ∀ x ∈ Z, ∃ j, x ∈ R j) :
    Z.card ≤ ∑ j, (Z ∩ R j).card :=
  calc Z.card ≤ (univ.biUnion fun j => Z ∩ R j).card := by
        apply card_le_card
        intro x hx
        obtain ⟨j, hj⟩ := hcover x hx
        exact mem_biUnion.mpr ⟨j, mem_univ j, mem_inter.mpr ⟨hx, hj⟩⟩
    _ ≤ ∑ j, (Z ∩ R j).card := card_biUnion_le

/-- A family covering `Z`, with each member meeting `Z` in at most `error > 0` elements, has at least `|Z| / error` members. -/
theorem cover_card_lower_bound (error : ℝ) (herror : 0 < error)
    (hcover : ∀ x ∈ Z, ∃ j, x ∈ R j) (heach : ∀ j, ((Z ∩ R j).card : ℝ) ≤ error) :
    (Z.card : ℝ) / error ≤ Fintype.card J := by
  rw [div_le_iff₀ herror]
  calc (Z.card : ℝ) ≤ ∑ j, ((Z ∩ R j).card : ℝ) := by
        exact_mod_cast card_le_sum_card_inter_of_cover Z R hcover
    _ ≤ ∑ _j : J, error := sum_le_sum fun j _ => heach j
    _ = Fintype.card J * error := by simp

end DDNNFNegation
