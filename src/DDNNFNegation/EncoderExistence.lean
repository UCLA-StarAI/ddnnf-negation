import DDNNFNegation.GeneratingLists
import DDNNFNegation.Gadget
import TutorialBox

/-!
# An encoder with large images

Choose the columns independently and uniformly. For each fixed set of
positions and each subgroup of excessive index, bound the probability that
all selected columns lie in that subgroup. Counting these choices and
applying a union bound produces one encoder whose restriction to every
sufficiently large set of positions has image of index at most eight.
-/

namespace DDNNFNegation

open Finset
open scoped Classical

noncomputable section

/-! ### Columns in a fixed containing set -/

section Counting

variable {G : Type*} [Fintype G]

/-- The column tuples whose columns indexed by `S` all lie in `K`. -/
def columnsInEvent {N : ℕ} (S : Finset (Fin N)) (K : Finset G) : Finset (Fin N → G) :=
  Fintype.piFinset (fun j => if j ∈ S then K else univ)

/-- Membership in the fixed-pair event means that every selected column lies in the
containing set. -/
theorem mem_columnsInEvent {N : ℕ} {S : Finset (Fin N)} {K : Finset G} {a : Fin N → G} :
    a ∈ columnsInEvent S K ↔ ∀ j ∈ S, a j ∈ K := by
  rw [columnsInEvent, Fintype.mem_piFinset]
  constructor
  · intro h j hj
    have := h j
    rwa [if_pos hj] at this
  · intro h j
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      exact h j hj
    · rw [if_neg hj]
      exact mem_univ _

/-- Exactly `|K|^{|S|} |G|^{N - |S|}` column tuples have their `S`-columns
in `K`: the tutorial's `16^{-|S|}` once `|K| = |G| / 16`. -/
theorem card_columnsInEvent {N : ℕ} (S : Finset (Fin N)) (K : Finset G) :
    (columnsInEvent S K).card = K.card ^ S.card * Fintype.card G ^ (N - S.card) := by
  rw [columnsInEvent, Fintype.card_piFinset]
  have h : ∀ j : Fin N, (if j ∈ S then K else univ).card =
      if j ∈ S then K.card else Fintype.card G := by
    intro j
    split_ifs <;> simp
  simp_rw [h]
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter, filter_not,
    filter_mem_eq_inter, univ_inter, card_univ_sdiff, Fintype.card_fin]

/-- If `16 |K| ≤ |G|`, the event costs a factor `16^{|S|}` against all tuples. -/
theorem card_columnsInEvent_mul_pow_le {N : ℕ} (S : Finset (Fin N)) (K : Finset G)
    (hK : K.card * 16 ≤ Fintype.card G) :
    (columnsInEvent S K).card * 16 ^ S.card ≤ Fintype.card G ^ N := by
  rw [card_columnsInEvent]
  have hS : S.card ≤ N := card_finset_fin_le S
  calc K.card ^ S.card * Fintype.card G ^ (N - S.card) * 16 ^ S.card
      = (K.card * 16) ^ S.card * Fintype.card G ^ (N - S.card) := by ring
    _ ≤ Fintype.card G ^ S.card * Fintype.card G ^ (N - S.card) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hK _)
    _ = Fintype.card G ^ N := by rw [← pow_add, Nat.add_sub_cancel' hS]

end Counting

/-! ### The union bound over fixed pairs of positions and containing sets -/

section BadSet

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

/-- Column tuples for which some set holding a third of the `N = 60 m`
columns generates a subgroup of index more than eight. -/
def deficientEncoders (m : ℕ) : Finset (Fin (60 * m) → G) :=
  univ.filter (fun a => ∃ S : Finset (Fin (60 * m)), 60 * m ≤ 3 * S.card ∧
    8 < Nat.card (G ⧸ partialImage a S))

/-- A bad tuple has a large position set whose columns all lie in one
of the fixed family of containing sets. This only establishes membership
in a union of events; it does not sample a set depending on the tuple. -/
theorem deficient_encoders_subset_union (m : ℕ) (hdim : Module.finrank (ZMod 2) G = 4 * m) :
    deficientEncoders (G := G) m ⊆
      ((univ : Finset (Finset (Fin (60 * m)))).filter
        (fun J => 60 * m ≤ 3 * J.card)).biUnion
        (fun J => (univ : Finset
          {H : Submodule (ZMod 2) G // Module.finrank (ZMod 2) H = 4 * m - 4}).biUnion
            (fun H => columnsInEvent J (univ.filter (· ∈ H.val)))) := by
  intro a ha
  obtain ⟨-, J, hJ, h8⟩ := mem_filter.mp ha
  obtain ⟨H, hJH, hH⟩ := exists_containing_set_of_small_image m hdim a J h8
  refine mem_biUnion.mpr ⟨J, mem_filter.mpr ⟨mem_univ _, hJ⟩, ?_⟩
  refine mem_biUnion.mpr ⟨⟨H, hH⟩, mem_univ _, mem_columnsInEvent.mpr ?_⟩
  exact fun j hj => mem_filter.mpr ⟨mem_univ _, hJH j hj⟩

set_option maxHeartbeats 800000 in
/-- The tutorial's union bound in exact natural-number arithmetic:
`2^(60m) * 32^(4m-4) * 16^(-20m) = 2^(-20)` for `m ≥ 1`.
We clear the denominator, so no rounding of probabilities is involved. -/
theorem deficient_encoders_fraction_bound (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card G = 16 ^ m) :
    (deficientEncoders (G := G) m).card * 2 ^ 20 ≤ Fintype.card G ^ (60 * m) := by
  classical
  have hdim : Module.finrank (ZMod 2) G = 4 * m := by
    have h := natCard_eq_two_pow_finrank G
    rw [Nat.card_eq_fintype_card, hcard, show (16 : ℕ) = 2 ^ 4 by norm_num,
      ← pow_mul] at h
    exact (Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) h).symm
  let largePositionSets := (univ : Finset (Finset (Fin (60 * m)))).filter
    (fun J => 60 * m ≤ 3 * J.card)
  let containingSets := (univ : Finset
    {H : Submodule (ZMod 2) G // Module.finrank (ZMod 2) H = 4 * m - 4})
  let containingSet (H : {H : Submodule (ZMod 2) G //
      Module.finrank (ZMod 2) H = 4 * m - 4}) : Finset G := univ.filter (· ∈ H.val)
  have hset (H : {H : Submodule (ZMod 2) G //
      Module.finrank (ZMod 2) H = 4 * m - 4}) :
      (containingSet H).card * 16 = Fintype.card G := by
    have hsize : (containingSet H).card = Nat.card H.val := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hsize, natCard_eq_two_pow_finrank, H.property, hcard,
      show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_mul]
    congr 1
    omega
  have hterm : ∀ S ∈ largePositionSets, ∀ H ∈ containingSets,
      (columnsInEvent S (containingSet H)).card * 16 ^ (20 * m) ≤
        Fintype.card G ^ (60 * m) := by
    intro S hS H _hH
    have hS' : 60 * m ≤ 3 * S.card := (mem_filter.mp hS).2
    have hH' := (hset H).le
    have hs : 20 * m ≤ S.card := by omega
    calc (columnsInEvent S (containingSet H)).card * 16 ^ (20 * m)
        ≤ (columnsInEvent S (containingSet H)).card * 16 ^ S.card :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs)
      _ ≤ Fintype.card G ^ (60 * m) := card_columnsInEvent_mul_pow_le S _ hH'
  have hsum : (deficientEncoders (G := G) m).card * 16 ^ (20 * m) ≤
      largePositionSets.card * containingSets.card * Fintype.card G ^ (60 * m) := by
    calc (deficientEncoders (G := G) m).card * 16 ^ (20 * m)
        ≤ (largePositionSets.biUnion (fun S => containingSets.biUnion
            (fun H => columnsInEvent S (containingSet H)))).card * 16 ^ (20 * m) :=
          Nat.mul_le_mul_right _ (card_le_card (deficient_encoders_subset_union m hdim))
      _ ≤ (∑ S ∈ largePositionSets, ∑ H ∈ containingSets, (columnsInEvent S (containingSet H)).card) *
            16 ^ (20 * m) := by
          apply Nat.mul_le_mul_right
          exact card_biUnion_le.trans (sum_le_sum fun S _ => card_biUnion_le)
      _ = ∑ S ∈ largePositionSets, ∑ H ∈ containingSets,
            (columnsInEvent S (containingSet H)).card * 16 ^ (20 * m) := by
          rw [sum_mul]
          exact sum_congr rfl fun S _ => by rw [sum_mul]
      _ ≤ ∑ S ∈ largePositionSets, ∑ H ∈ containingSets, Fintype.card G ^ (60 * m) :=
          sum_le_sum fun S hS => sum_le_sum fun H hH => hterm S hS H hH
      _ = largePositionSets.card * containingSets.card * Fintype.card G ^ (60 * m) := by
          rw [sum_const, sum_const, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hPositions' : largePositionSets.card ≤ 2 ^ (60 * m) := by
    calc largePositionSets.card ≤ (univ : Finset (Finset (Fin (60 * m)))).card := card_filter_le _ _
      _ = 2 ^ (60 * m) := by rw [card_univ, Fintype.card_finset, Fintype.card_fin]
  have hContainers' : containingSets.card ≤ 32 ^ (4 * m - 4) := by
    simpa [containingSets, ← Nat.card_eq_fintype_card] using codimension_four_sets_count m hm hcard
  have hconst : 16 ^ (20 * m) = 2 ^ (60 * m) * 32 ^ (4 * m - 4) * 2 ^ 20 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, show (32 : ℕ) = 2 ^ 5 by norm_num]
    simp only [← pow_mul, ← pow_add]
    congr 1
    omega
  have hpos : 0 < 2 ^ (60 * m) * 32 ^ (4 * m - 4) :=
    Nat.mul_pos (by positivity) (by positivity)
  have h1 : (2 ^ (60 * m) * 32 ^ (4 * m - 4)) *
        ((deficientEncoders (G := G) m).card * 2 ^ 20) ≤
      (2 ^ (60 * m) * 32 ^ (4 * m - 4)) * Fintype.card G ^ (60 * m) := by
    calc (2 ^ (60 * m) * 32 ^ (4 * m - 4)) *
          ((deficientEncoders (G := G) m).card * 2 ^ 20)
        = (deficientEncoders (G := G) m).card * 16 ^ (20 * m) := by rw [hconst]; ring
      _ ≤ largePositionSets.card * containingSets.card * Fintype.card G ^ (60 * m) := hsum
      _ ≤ 2 ^ (60 * m) * 32 ^ (4 * m - 4) * Fintype.card G ^ (60 * m) := by
          gcongr
  exact Nat.le_of_mul_le_mul_left h1 hpos

end BadSet

/-! ### Existence -/

section Existence

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

/-- **The encoder exists**, abstract form: in an `𝔽₂`-space of order
`16 ^ m` there are `N = 60 m` columns such that every `S` holding a third
of them generates a subgroup of index at most eight.  The bad tuples number
at most `|G|^N / 2^20 < |G|^N`. -/
theorem encoder_exists_of_cardinality (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card G = 16 ^ m) :
    ∃ a : Fin (60 * m) → G,
      ∀ S : Finset (Fin (60 * m)), Fintype.card (Fin (60 * m)) ≤ 3 * S.card →
        Nat.card (G ⧸ partialImage a S) ≤ 8 := by
  classical
  have hI := deficient_encoders_fraction_bound m hm hcard
  have hpos : 0 < Fintype.card G ^ (60 * m) := by rw [hcard]; positivity
  have hlt : (deficientEncoders (G := G) m).card < Fintype.card (Fin (60 * m) → G) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have h : (deficientEncoders (G := G) m).card * 16 ≤ Fintype.card G ^ (60 * m) :=
      (Nat.mul_le_mul_left _ (by norm_num : 16 ≤ 2 ^ 20)).trans hI
    omega
  rw [← card_univ] at hlt
  obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, fun S hS => ?_⟩
  by_contra hcon
  push Not at hcon
  apply ha
  rw [deficientEncoders, mem_filter]
  exact ⟨mem_univ _, S, by simpa using hS, hcon⟩

end Existence

/-! ### Instantiation at the gadget alphabet -/

/-- Lagrange: an index bound `[G : H] ≤ 8` is the cardinality bound
`|G| ≤ 8 |H|`. -/
theorem card_le_eight_mul_card_of_index_le_eight {G : Type*} [Fintype G] [AddCommGroup G]
    (H : AddSubgroup G) (hindex : Nat.card (G ⧸ H) ≤ 8) :
    Fintype.card G ≤ 8 * Nat.card H := by
  rw [← Nat.card_eq_fintype_card, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H]
  exact Nat.mul_le_mul_right (Nat.card H) hindex

/-- **The encoder over the `n × n` grid group**.  For `n ≥ 1` there
are `N = 60 n²` columns in `(Fin n × Fin n) → GadgetVector` such that every
`S` with `3 |S| ≥ N` generates a subgroup of index at most eight.  The
partial sums over any `S` are exactly uniform on the generated subgroup for
any columns whatsoever (`FiberCounts.lean`), so this is the only property
the zero-fiber count asks of the encoder. -/
theorem encoder_exists_on_grid (n : ℕ) (hn : 0 < n) :
    ∃ a : Fin (60 * (n * n)) → ((Fin n × Fin n) → GadgetVector),
      ∀ S : Finset (Fin (60 * (n * n))),
        Fintype.card (Fin (60 * (n * n))) ≤ 3 * S.card →
        Nat.card (((Fin n × Fin n) → GadgetVector) ⧸ partialImage a S) ≤ 8 := by
  apply encoder_exists_of_cardinality (n * n) (Nat.mul_pos hn hn)
  rw [gridVector_card, Fintype.card_prod, Fintype.card_fin]

/-- One encoding matrix has large images on every set of at least `N/3`
positions. Equal fiber sizes, valid for every matrix, are stated separately
by `equal_fiber_sizes` in `FiberCounts.lean`. -/
@[tutorial_box "lem:tutorial-encoder"]
theorem encoder_with_large_images (n : ℕ) (hn : 0 < n) :
    ∃ a : Fin (60 * (n * n)) → ((Fin n × Fin n) → GadgetVector),
      ∀ S : Finset (Fin (60 * (n * n))),
        Fintype.card (Fin (60 * (n * n))) ≤ 3 * S.card →
        Fintype.card ((Fin n × Fin n) → GadgetVector) ≤
          8 * Nat.card (partialImage a S) := by
  obtain ⟨a, ha⟩ := encoder_exists_on_grid n hn
  exact ⟨a, fun S hS => card_le_eight_mul_card_of_index_le_eight _ (ha S hS)⟩

end

end DDNNFNegation
