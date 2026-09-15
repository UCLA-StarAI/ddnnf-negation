import DDNNFNegation.CommonPartialSums
import DDNNFNegation.FiberCounts
import DDNNFNegation.Encoder
import TutorialBox

/-!
# Bounding a rectangle on the encoder's zero fiber

The zero fiber consists of assignments whose selected columns sum to zero.
Across a partition, their two partial sums agree. The common values in a
zero rectangle form a zero square of the outer matrix. Combining the
spectral bound on that square with the partial-sum fiber counts bounds
the rectangle's share of the zero fiber.
-/

namespace DDNNFNegation

open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The zero fiber `E⁻¹(0)`: the assignments mapped to zero by the encoder. -/
@[tutorial_box "def:tutorial-zero-fiber"]
def zeroFiber {G : Type*} [DecidableEq G] [AddCommGroup G] (a : ι → G) : Finset (ι → Bool) :=
  finiteMapFiber (subsetSum a) 0

/-- The zero fiber consists of zero-inputs: `E⁻¹(0) ⊆ L_n⁻¹(0)`,
because `F_n(0) = 0`. -/
@[tutorial_box "lem:tutorial-zero-fiber-zero-inputs"]
theorem zeroFiber_subset_zeroInputs {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : ι → ((Fin n × Fin n) → GadgetVector)) :
    ∀ x ∈ zeroFiber a, ¬hardFunction ranks hn a x := by
  intro x hx
  have hsum : subsetSum a x = 0 := by simpa [zeroFiber, finiteMapFiber] using hx
  unfold hardFunction
  rw [hsum]
  exact outerFunction_zero ranks hn

/-! ### The zero fiber is large -/

section ZeroFiberCount

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

omit [Fintype G] in
/-- `E⁻¹(0)` is the fiber over `0` of the encoder restricted to all positions,
up to restricting each assignment to the full set. -/
theorem zeroFiber_card_eq (a : ι → G) :
    (zeroFiber a).card = (finiteMapFiber (partialSubsetSum a univ) 0).card := by
  have hsum : ∀ x : ι → Bool, subsetSum a x = partialSubsetSum a univ (fun i => x i) := by
    intro x
    unfold subsetSum partialSubsetSum
    rw [sum_attach univ (fun i => if x i then a i else 0)]
  apply card_nbij' (fun x => fun i : ↥(univ : Finset ι) => x i)
    (fun y => fun i => y ⟨i, mem_univ i⟩)
  · intro x hx
    simp only [zeroFiber, finiteMapFiber, mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    rwa [← hsum]
  · intro y hy
    simp only [zeroFiber, finiteMapFiber, mem_coe, mem_filter, mem_univ, true_and] at hy ⊢
    rw [hsum]
    exact hy
  · intro x _
    rfl
  · intro y _
    rfl

/-- `|E⁻¹(0)| ≥ 2^N / |G|`. The encoder is exactly uniform on its image,
so `|E⁻¹(0)| = 2^N / |im(E)|`, and `im(E) ⊆ G`. -/
theorem zeroFiber_card_ge (hexp : ∀ g : G, g + g = 0) (a : ι → G) :
    (2 : ℝ) ^ Fintype.card ι / Fintype.card G ≤ (zeroFiber a).card := by
  rw [zeroFiber_card_eq]
  have hmul := equal_fiber_sizes hexp a univ (partialImage a univ).zero_mem
  rw [card_univ] at hmul
  have hsub : Nat.card (partialImage a univ) ≤ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast (@Fintype.card_pos G _ ⟨0⟩)
  rw [div_le_iff₀ hG]
  exact_mod_cast calc 2 ^ Fintype.card ι
      = (finiteMapFiber (partialSubsetSum a univ) 0).card * Nat.card (partialImage a univ) :=
        hmul.symm
    _ ≤ (finiteMapFiber (partialSubsetSum a univ) 0).card * Fintype.card G :=
        Nat.mul_le_mul_left _ hsub

end ZeroFiberCount

/-! ### The rectangle estimate -/

section RectangleEstimate

variable {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
  (a : ι → ((Fin n × Fin n) → GadgetVector)) (R : BooleanRectangle ι)

/-- Splitting each assignment at the cut identifies `R ∩ E⁻¹(0)` with the pairs
`(x_J, x_{Jᶜ})` of the rectangle whose partial sums add to zero. -/
theorem card_inter_zeroFiber_eq :
    (R.assignments ∩ zeroFiber a).card =
      (rectangleZeroPairs (partialSubsetSum a R.cut) (partialSubsetSum a R.cutᶜ)
        R.left R.right).card := by
  have hmem : ∀ x : ι → Bool, x ∈ R.assignments ∩ zeroFiber a ↔
      assignmentPartitionEquiv R.cut x ∈
        rectangleZeroPairs (partialSubsetSum a R.cut) (partialSubsetSum a R.cutᶜ)
          R.left R.right := by
    intro x
    rw [mem_inter, BooleanRectangle.assignments, mem_assignmentRectangle, zeroFiber,
      finiteMapFiber, mem_filter, subsetSum_partition a R.cut, rectangleZeroPairs, mem_filter,
      mem_product]
    simp only [mem_univ, true_and, and_assoc]
    exact Iff.rfl
  apply card_nbij' (assignmentPartitionEquiv R.cut) (assignmentPartitionEquiv R.cut).symm
  · intro x hx
    rw [mem_coe] at hx ⊢
    exact (hmem x).mp hx
  · intro p hp
    rw [mem_coe] at hp ⊢
    rw [hmem, (assignmentPartitionEquiv R.cut).apply_symm_apply]
    exact hp
  · intro x _
    exact (assignmentPartitionEquiv R.cut).symm_apply_apply x
  · intro p _
    exact (assignmentPartitionEquiv R.cut).apply_symm_apply p

/-- For a zero rectangle `R` of `L_n` with cut `J`,
`|R ∩ E⁻¹(0)| ≤ ε |G| · 2^{|J|}/|im(E_J)| · 2^{|Jᶜ|}/|im(E_{Jᶜ})|`,
by the common-partial-sum bound and the bound on every fiber of the two encoders. -/
theorem card_inter_zeroFiber_le (hzero : ∀ x ∈ R.assignments, ¬ hardFunction ranks hn a x) :
    ((R.assignments ∩ zeroFiber a).card : ℝ) ≤
      spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) *
        (2 ^ R.cut.card / Nat.card (partialImage a R.cut)) *
        (2 ^ R.cutᶜ.card / Nat.card (partialImage a R.cutᶜ)) := by
  rw [card_inter_zeroFiber_eq]
  refine zeroRectangle_zeroPairs_card_le _ _ R.left R.right ranks hn _ _ (by positivity)
    (by positivity) (card_finiteMapFiber_le_div gridVector_add_self a R.cut)
    (card_finiteMapFiber_le_div gridVector_add_self a R.cutᶜ) ?_
  intro x hx y hy
  have h := hzero ((assignmentPartitionEquiv R.cut).symm (x, y)) (by
    rw [BooleanRectangle.assignments, mem_assignmentRectangle,
      (assignmentPartitionEquiv R.cut).apply_symm_apply]
    exact ⟨hx, hy⟩)
  unfold hardFunction at h
  rwa [subsetSum_partition_symm] at h

/-- Every balanced zero rectangle `R` of `L_n` has
`|R ∩ E⁻¹(0)| ≤ 64 ε |E⁻¹(0)|` when the encoder has large images at
balanced cuts. The image bounds give `|G| ≤ 8 |im(E_J)|` on both sides;
`card_inter_zeroFiber_le` then bounds the intersection by `64 ε · 2^N / |G|`.
Finally `zeroFiber_card_ge` bounds `2^N / |G|` by `|E⁻¹(0)|`. -/
@[tutorial_box "lem:tutorial-rectangle-estimate"]
theorem rectangle_estimate
    (hencoder : ∀ S : Finset ι, Fintype.card ι ≤ 3 * S.card →
      Fintype.card ((Fin n × Fin n) → GadgetVector) ≤ 8 * Nat.card (partialImage a S))
    (hbalanced : R.IsBalanced)
    (hzero : ∀ x ∈ R.assignments, ¬ hardFunction ranks hn a x) :
    ((R.assignments ∩ zeroFiber a).card : ℝ) ≤
      64 * spectralEpsilon n * (zeroFiber a).card := by
  have h15 := card_inter_zeroFiber_le ranks hn a R hzero
  have h16 := two_index_bound (partialImage a R.cut) (partialImage a R.cutᶜ)
    (hencoder R.cut (IsBalanced.left hbalanced)) (hencoder R.cutᶜ (IsBalanced.right hbalanced))
  have h12 := zeroFiber_card_ge gridVector_add_self a
  have hε := spectralEpsilon_nonneg n
  have hGS : (0 : ℝ) < Nat.card (partialImage a R.cut) := by exact_mod_cast Nat.card_pos
  have hGT : (0 : ℝ) < Nat.card (partialImage a R.cutᶜ) := by exact_mod_cast Nat.card_pos
  have hG : (0 : ℝ) < Fintype.card ((Fin n × Fin n) → GadgetVector) := by
    exact_mod_cast Fintype.card_pos
  have hpow : (2 : ℝ) ^ R.cut.card * 2 ^ R.cutᶜ.card = 2 ^ Fintype.card ι := by
    rw [← pow_add, card_add_card_compl]
  calc ((R.assignments ∩ zeroFiber a).card : ℝ)
      ≤ spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) *
          (2 ^ R.cut.card / Nat.card (partialImage a R.cut)) *
          (2 ^ R.cutᶜ.card / Nat.card (partialImage a R.cutᶜ)) := h15
    _ = spectralEpsilon n *
          ((Fintype.card ((Fin n × Fin n) → GadgetVector) : ℝ) ^ 2 /
            ((Nat.card (partialImage a R.cut) : ℝ) * Nat.card (partialImage a R.cutᶜ))) *
          (2 ^ Fintype.card ι / Fintype.card ((Fin n × Fin n) → GadgetVector)) := by
        rw [← hpow]
        field_simp
    _ ≤ spectralEpsilon n * 64 * (zeroFiber a).card := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h16 hε) h12 (by positivity)
        positivity
    _ = 64 * spectralEpsilon n * (zeroFiber a).card := by ring

end RectangleEstimate

end

end DDNNFNegation
