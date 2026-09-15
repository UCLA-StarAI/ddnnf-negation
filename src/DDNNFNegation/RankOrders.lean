import Mathlib
import TutorialBox

/-!
# Signed terms, rank orders, and permutation tails

A signed term specifies sets of positive and negative coordinates.
A satisfiable term cannot have overlap. Terms with conflicting demands
on a coordinate cannot be satisfied together. `LabelOrders` gives one
permutation of the labels for each bucket.

For a uniformly random permutation, the minimum rank of a nonempty set
has an exact tail count proved by a swap bijection. When the set has
density at least one third, this gives a geometric tail and a constant
moment bound. Their product over independent permutations supports the
union bound in `OuterDNF.lean`, selecting ranks for which every eligible
term has width at most `10*n`.
-/

namespace DDNNFNegation

open Finset

noncomputable section

section

/-! ## Abstract signed terms -/

/-- A conjunction described by the variables required to be true and false. -/
structure SignedTerm (Ω : Type*) where
  positive : Finset Ω
  negative : Finset Ω

/-- A Boolean valuation satisfies a signed term when it has every requested
positive literal and none of the variables occurring negatively. -/
def SignedTerm.Satisfied
    {Ω : Type*} [DecidableEq Ω] (T : SignedTerm Ω) (v : Ω → Prop) : Prop :=
  (∀ u ∈ T.positive, v u) ∧ (∀ u ∈ T.negative, ¬v u)

/-- Two signed terms are syntactically incompatible if one asks for a
variable positively and the other asks for the same variable negatively. -/
def SignedTerm.Incompatible
    {Ω : Type*} [DecidableEq Ω] (T U : SignedTerm Ω) : Prop :=
  ∃ u, (u ∈ T.positive ∧ u ∈ U.negative) ∨
    (u ∈ U.positive ∧ u ∈ T.negative)

/-- A conflicting literal prevents a valuation from satisfying both signed terms. -/
theorem SignedTerm.not_both_satisfied_of_incompatible
    {Ω : Type*} [DecidableEq Ω] {T U : SignedTerm Ω}
    (h : T.Incompatible U) (v : Ω → Prop) :
    ¬(T.Satisfied v ∧ U.Satisfied v) := by
  rintro ⟨hT, hU⟩
  obtain ⟨u, hTU | hUT⟩ := h
  · exact (hU.2 u hTU.2) (hT.1 u hTU.1)
  · exact (hT.2 u hUT.2) (hU.1 u hUT.1)

/-- Pairwise literal conflicts give uniqueness of a satisfied term index. -/
theorem SignedTerm.atMostOne_satisfied
    {Ω κ : Type*} [DecidableEq Ω]
    (term : κ → SignedTerm Ω)
    (hpair : ∀ a b, a ≠ b → (term a).Incompatible (term b))
    (v : Ω → Prop) {a b : κ}
    (ha : (term a).Satisfied v) (hb : (term b).Satisfied v) : a = b := by
  by_contra hab
  exact (SignedTerm.not_both_satisfied_of_incompatible (hpair a b hab) v) ⟨ha, hb⟩

/-- The characteristic valuation of the positive set satisfies every
consistent signed term. -/
theorem SignedTerm.satisfied_positiveCharacteristic
    {Ω : Type*} [DecidableEq Ω] (T : SignedTerm Ω)
    (hdisjoint : Disjoint T.positive T.negative) :
    T.Satisfied (fun u => u ∈ T.positive) := by
  refine ⟨fun _ hu => hu, ?_⟩
  intro u huNegative huPositive
  exact Finset.disjoint_left.mp hdisjoint huPositive huNegative

end

/-- The tutorial's rank system: `n` permutations `π_r`, one per bucket, each
a ranking table of the labels. -/
@[tutorial_box "def:tutorial-buckets"]
abbrev LabelOrders (n : ℕ) := Fin n → Equiv.Perm (Fin n)

/-- A permutation carries a nonempty label set to a nonempty set of ranks. -/
theorem image_nonempty_of_nonempty {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {S : Finset α} (hS : S.Nonempty) : (S.image f).Nonempty :=
  hS.image f

/-- Least zero-based rank under one permutation, with value zero on the empty
set.  The empty case is irrelevant to the construction but makes finite
event families independent of proof terms. -/
def permutationMin {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  if hS : S.Nonempty then
    ((S.image p).min' (image_nonempty_of_nonempty p hS) : Fin n).val
  else 0

/-- For a nonempty set, the least rank is its ordinary finite minimum. -/
theorem permutationMin_of_nonempty {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    permutationMin p S =
      ((S.image p).min' (image_nonempty_of_nonempty p hS) : Fin n).val := by
  simp [permutationMin, hS]

/-- Sum of the one-based prefix lengths produced by an `n`-tuple of orders. -/
def rankTupleCost {n : ℕ} (r : LabelOrders n)
    (S : Finset (Fin n)) : ℕ :=
  ∑ j : Fin n, (permutationMin (r j) S + 1)

/-! ## A finite union bound -/

/-- Rank tuples whose cost for `S` exceeds the proposed threshold. -/
def badRankTuples {n : ℕ} (C : ℕ) (S : Finset (Fin n))
    : Finset (LabelOrders n) :=
  univ.filter fun r => C * n < rankTupleCost r S

/-! ## First-moment and tensorization identities -/

theorem pow_rankTupleCost {n : ℕ} (x : ℝ) (r : LabelOrders n)
    (S : Finset (Fin n)) :
    x ^ rankTupleCost r S =
      ∏ j : Fin n, x ^ (permutationMin (r j) S + 1) := by
  simpa [rankTupleCost] using
    (Finset.prod_pow_eq_pow_sum (univ : Finset (Fin n))
      (fun j => permutationMin (r j) S + 1) x).symm

/-- Independence is just the finite product-sum identity. -/
theorem sum_pow_rankTupleCost {n : ℕ} (x : ℝ)
    (S : Finset (Fin n)) :
    ∑ r : LabelOrders n, x ^ rankTupleCost r S =
      (∑ p : Equiv.Perm (Fin n),
        x ^ (permutationMin p S + 1)) ^ n := by
  simp_rw [pow_rankTupleCost]
  rw [Fintype.sum_pow]

/-- Finite Markov inequality, written entirely as a counting statement. -/
theorem card_badRankTuples_mul_pow_le {n C : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (S : Finset (Fin n)) :
    ((badRankTuples C S).card : ℝ) * x ^ (C * n + 1) ≤
      (∑ p : Equiv.Perm (Fin n),
        x ^ (permutationMin p S + 1)) ^ n := by
  rw [← sum_pow_rankTupleCost x S, ← nsmul_eq_mul, ← sum_const]
  calc
    ∑ r ∈ badRankTuples C S, x ^ (C * n + 1)
        ≤ ∑ r ∈ badRankTuples C S, x ^ rankTupleCost r S := by
      apply sum_le_sum
      intro r hr
      have hcost : C * n + 1 ≤ rankTupleCost r S := by
        have := (mem_filter.mp hr).2
        omega
      exact pow_le_pow_right₀ hx hcost
    _ ≤ ∑ r : LabelOrders n, x ^ rankTupleCost r S := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun r _ _ => pow_nonneg (by linarith) _)

/-- Tensorized bad-event bound from a one-permutation moment estimate. -/
theorem card_badRankTuples_mul_pow_le_of_singleMoment {n C : ℕ}
    {x M : ℝ} (hx : 1 ≤ x)
    (S : Finset (Fin n))
    (hsingle :
      ∑ p : Equiv.Perm (Fin n),
          x ^ (permutationMin p S + 1) ≤
        M * Fintype.card (Equiv.Perm (Fin n))) :
    ((badRankTuples C S).card : ℝ) * x ^ (C * n + 1) ≤
      (M * Fintype.card (Equiv.Perm (Fin n))) ^ n := by
  exact (card_badRankTuples_mul_pow_le hx S).trans
    (pow_le_pow_left₀ (by positivity) hsingle n)

/-! ## Reducing the one-permutation moment to a tail count -/

/-- Permutations for which the least chosen rank is at least `t`. -/
def permutationMinTail {n : ℕ} (S : Finset (Fin n)) (t : ℕ) :
    Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun p => t ≤ permutationMin p S

/-- The least rank of a nonempty label set is a valid position in the permutation. -/
theorem permutationMin_lt_card {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hS : S.Nonempty) : permutationMin p S < n := by
  rw [permutationMin_of_nonempty p S hS]
  exact (S.image p).min' (image_nonempty_of_nonempty p hS) |>.isLt

/-- The integers up to the least rank are exactly the thresholds that the least rank
exceeds. -/
theorem range_succ_permutationMin {n : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    range (permutationMin p S + 1) =
      (range n).filter fun t => t ≤ permutationMin p S := by
  ext t
  simp only [mem_range, mem_filter]
  have hmin := permutationMin_lt_card p S hS
  omega

/-- Expand a power into its finite geometric sum for the exponential-moment calculation. -/
theorem pow_succ_eq_one_add_geom (x : ℝ) (m : ℕ) :
    x ^ (m + 1) = 1 + (x - 1) * ∑ t ∈ range (m + 1), x ^ t := by
  rw [mul_comm, geom_sum_mul]
  ring

/-- Layer-cake identity for the least-rank moment. -/
theorem sum_pow_permutationMin_eq_tail_sum {n : ℕ} (x : ℝ)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∑ p : Equiv.Perm (Fin n), x ^ (permutationMin p S + 1) =
      Fintype.card (Equiv.Perm (Fin n)) +
        (x - 1) * ∑ t ∈ range n,
          x ^ t * (permutationMinTail S t).card := by
  calc
    ∑ p : Equiv.Perm (Fin n), x ^ (permutationMin p S + 1) =
        ∑ p : Equiv.Perm (Fin n),
          (1 + (x - 1) * ∑ t ∈ range (permutationMin p S + 1), x ^ t) := by
            apply sum_congr rfl
            intro p _hp
            exact pow_succ_eq_one_add_geom x (permutationMin p S)
    _ = ∑ p : Equiv.Perm (Fin n),
          (1 + (x - 1) * ∑ t ∈ range n,
            if t ≤ permutationMin p S then x ^ t else 0) := by
          apply sum_congr rfl
          intro p _hp
          congr 2
          rw [range_succ_permutationMin p S hS, sum_filter]
    _ = Fintype.card (Equiv.Perm (Fin n)) +
        (x - 1) * ∑ t ∈ range n,
          x ^ t * (permutationMinTail S t).card := by
      rw [sum_add_distrib]
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
      congr 1
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro t ht
      rw [sum_ite]
      simp [permutationMinTail, nsmul_eq_mul, mul_comm]

/-- Bound the truncated geometric series of ratio `5/6` by the infinite sum `6`. -/
theorem geom_five_six_sum_le_six (n : ℕ) :
    ∑ t ∈ range n, ((5 : ℝ) / 6) ^ t ≤ 6 := by
  rw [geom_sum_eq (by norm_num : (5 : ℝ) / 6 ≠ 1)]
  have hpow : 0 ≤ ((5 : ℝ) / 6) ^ n := by positivity
  norm_num
  linarith

/-- A geometric tail bound gives the moment estimate used in the union
bound. The finite geometric sum has ratio `(5/4)*(2/3) = 5/6`. -/
theorem singleMoment_three_of_twoThirds_tail {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (htail : ∀ t < n,
      ((permutationMinTail S t).card : ℝ) ≤
        Fintype.card (Equiv.Perm (Fin n)) * ((2 : ℝ) / 3) ^ t) :
    ∑ p : Equiv.Perm (Fin n),
        ((5 : ℝ) / 4) ^ (permutationMin p S + 1) ≤
      3 * Fintype.card (Equiv.Perm (Fin n)) := by
  rw [sum_pow_permutationMin_eq_tail_sum ((5 : ℝ) / 4) S hS]
  have hweighted :
      ∑ t ∈ range n,
          ((5 : ℝ) / 4) ^ t * (permutationMinTail S t).card ≤
        Fintype.card (Equiv.Perm (Fin n)) * 6 := by
    calc
      ∑ t ∈ range n,
          ((5 : ℝ) / 4) ^ t * (permutationMinTail S t).card
          ≤ ∑ t ∈ range n,
              ((5 : ℝ) / 4) ^ t *
                (Fintype.card (Equiv.Perm (Fin n)) * ((2 : ℝ) / 3) ^ t) := by
            apply sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_left (htail t (mem_range.mp ht)) (by positivity)
      _ = Fintype.card (Equiv.Perm (Fin n)) *
          ∑ t ∈ range n, ((5 : ℝ) / 6) ^ t := by
            rw [mul_sum]
            apply sum_congr rfl
            intro t _ht
            calc
              ((5 : ℝ) / 4) ^ t *
                    (Fintype.card (Equiv.Perm (Fin n)) * ((2 : ℝ) / 3) ^ t) =
                  Fintype.card (Equiv.Perm (Fin n)) *
                    (((5 : ℝ) / 4) ^ t * ((2 : ℝ) / 3) ^ t) := by ring
              _ = Fintype.card (Equiv.Perm (Fin n)) *
                    (((5 : ℝ) / 4) * ((2 : ℝ) / 3)) ^ t := by rw [mul_pow]
              _ = Fintype.card (Equiv.Perm (Fin n)) * ((5 : ℝ) / 6) ^ t := by norm_num
      _ ≤ Fintype.card (Equiv.Perm (Fin n)) * 6 := by
            exact mul_le_mul_of_nonneg_left (geom_five_six_sum_le_six n) (by positivity)
  norm_num
  have hcard : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by positivity
  nlinarith

/-! ## The exact tail count -/

theorem le_permutationMin_iff {n t : ℕ} (p : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    t ≤ permutationMin p S ↔ ∀ x ∈ S, t ≤ (p x).val := by
  rw [permutationMin_of_nonempty p S hS]
  constructor
  · intro ht x hx
    exact ht.trans (Finset.min'_le (S.image p) (p x) (mem_image_of_mem p hx))
  · intro ht
    obtain ⟨x, hx⟩ := hS
    have htn : t < n := (ht x hx).trans_lt (p x).isLt
    let tf : Fin n := ⟨t, htn⟩
    have himage : (S.image p).Nonempty := ⟨p x, mem_image_of_mem p hx⟩
    have hfin : tf ≤ (S.image p).min' himage := by
      apply Finset.le_min'
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact ht x hx
    exact hfin

/-- The ranks at least `t` number `n - t`. -/
theorem card_filter_le_val (n t : ℕ) :
    (univ.filter fun r : Fin n => t ≤ r.val).card = n - t := by
  classical
  have hcompl : (univ.filter fun r : Fin n => t ≤ r.val) =
      (univ.filter fun r : Fin n => r.val < t)ᶜ := by
    ext r
    simp [not_lt]
  rw [hcompl, card_compl, Fintype.card_fin, Fin.card_filter_val_lt]
  rcases le_total n t with h | h
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right h]

/-- In the tail event `t ≤ M_q(S)`, the labels outside `S` placed at a rank
at least `t` number `n - t - |S|`: all `|S|` labels of `S` sit among the
`n - t` ranks at least `t`. -/
theorem card_filter_notMem_le_rank {n t : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (q : Equiv.Perm (Fin n)) (hq : t ≤ permutationMin q S) :
    (univ.filter fun b : Fin n => b ∉ S ∧ t ≤ (q b).val).card =
      n - t - S.card := by
  classical
  have hsub : S ⊆ univ.filter fun b : Fin n => t ≤ (q b).val := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (le_permutationMin_iff q S hS).mp hq x hx⟩
  have hset : (univ.filter fun b : Fin n => b ∉ S ∧ t ≤ (q b).val) =
      (univ.filter fun b : Fin n => t ≤ (q b).val) \ S := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    tauto
  have hmap : (univ.filter fun b : Fin n => t ≤ (q b).val) =
      (univ.filter fun r : Fin n => t ≤ r.val).map q.symm.toEmbedding := by
    ext b
    simp [mem_map_equiv]
  rw [hset, card_sdiff_of_subset hsub, hmap, card_map, card_filter_le_val]

/-- For `t < n`, raising the threshold from `t` to `t+1` multiplies the
tail count by `(n-t-|S|)/(n-t)`. Swap rank `t` with a rank at least `t`
and record the label previously at rank `t`; reversing the swap gives
the counting bijection. -/
theorem card_permutationMinTail_succ_mul {n t : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (ht : t < n) :
    (permutationMinTail S (t + 1)).card * (n - t) =
      (permutationMinTail S t).card * (n - t - S.card) := by
  classical
  let z : Fin n := ⟨t, ht⟩
  have hzval : z.val = t := rfl
  have hA : (permutationMinTail S (t + 1) ×ˢ
      (univ.filter fun r : Fin n => t ≤ r.val)).card =
      (permutationMinTail S (t + 1)).card * (n - t) := by
    rw [card_product, card_filter_le_val]
  have hB : ((permutationMinTail S t ×ˢ (univ : Finset (Fin n))).filter
      fun qb : Equiv.Perm (Fin n) × Fin n => qb.2 ∉ S ∧ t ≤ (qb.1 qb.2).val).card =
      (permutationMinTail S t).card * (n - t - S.card) := by
    rw [card_filter, sum_product, ← smul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro q hq
    have h := card_filter_notMem_le_rank S hS q (mem_filter.mp hq).2
    rw [card_filter] at h
    exact h
  have hAB : (permutationMinTail S (t + 1) ×ˢ
      (univ.filter fun r : Fin n => t ≤ r.val)).card =
      ((permutationMinTail S t ×ˢ (univ : Finset (Fin n))).filter
        fun qb : Equiv.Perm (Fin n) × Fin n =>
          qb.2 ∉ S ∧ t ≤ (qb.1 qb.2).val).card := by
    refine card_nbij'
      (fun pr => (Equiv.swap z pr.2 * pr.1, pr.1.symm z))
      (fun qb => (Equiv.swap z (qb.1 qb.2) * qb.1, qb.1 qb.2)) ?_ ?_ ?_ ?_
    · rintro ⟨p, r⟩ hpr
      obtain ⟨hp, hr⟩ := mem_product.mp hpr
      have hpmin : t + 1 ≤ permutationMin p S := (mem_filter.mp hp).2
      have hrt : t ≤ r.val := (mem_filter.mp hr).2
      have hqmin : t ≤ permutationMin (Equiv.swap z r * p) S := by
        apply (le_permutationMin_iff _ S hS).mpr
        intro x hxS
        have hx := (le_permutationMin_iff p S hS).mp hpmin x hxS
        rw [Equiv.Perm.mul_apply]
        by_cases hxr : p x = r
        · rw [hxr, Equiv.swap_apply_right]
        · have hxz : p x ≠ z := by
            intro hxz
            rw [hxz, hzval] at hx
            omega
          rw [Equiv.swap_apply_of_ne_of_ne hxz hxr]
          omega
      have hbnot : p.symm z ∉ S := by
        intro hbS
        have hb := (le_permutationMin_iff p S hS).mp hpmin _ hbS
        rw [Equiv.apply_symm_apply, hzval] at hb
        omega
      refine mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, hqmin⟩, mem_univ _⟩, hbnot, ?_⟩
      show t ≤ ((Equiv.swap z r * p) (p.symm z)).val
      rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
      exact hrt
    · rintro ⟨q, b⟩ hqb
      obtain ⟨hqb', hbnot, hbt⟩ := mem_filter.mp hqb
      have hbt' : t ≤ (q b).val := hbt
      have hq : t ≤ permutationMin q S :=
        (mem_filter.mp (mem_product.mp hqb').1).2
      have hpmin : t + 1 ≤ permutationMin (Equiv.swap z (q b) * q) S := by
        apply (le_permutationMin_iff _ S hS).mpr
        intro x hxS
        have hx := (le_permutationMin_iff q S hS).mp hq x hxS
        have hxb : q x ≠ q b := fun h => hbnot (q.injective h ▸ hxS)
        rw [Equiv.Perm.mul_apply]
        by_cases hxz : q x = z
        · rw [hxz, Equiv.swap_apply_left]
          have hqbz : q b ≠ z := fun h => hxb (hxz.trans h.symm)
          have hne : (q b).val ≠ t := fun h => hqbz (Fin.ext (h.trans hzval.symm))
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hxz hxb]
          have hne : (q x).val ≠ t := fun h => hxz (Fin.ext (h.trans hzval.symm))
          omega
      exact mem_product.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, hpmin⟩, mem_filter.mpr ⟨mem_univ _, hbt⟩⟩
    · rintro ⟨p, r⟩ _
      have hb : (Equiv.swap z r * p) (p.symm z) = r := by
        rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
      refine Prod.ext ?_ ?_
      · show Equiv.swap z ((Equiv.swap z r * p) (p.symm z)) * (Equiv.swap z r * p) = p
        rw [hb, Equiv.swap_mul_self_mul]
      · exact hb
    · rintro ⟨q, b⟩ _
      refine Prod.ext ?_ ?_
      · exact Equiv.swap_mul_self_mul z (q b) q
      · show (Equiv.swap z (q b) * q).symm z = b
        rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  rw [← hA, hAB, hB]

/-- The exact tail count in falling factorials: `|Tail(t)| · n^{(t)} =
n! · (n - |S|)^{(t)}`, that is, `|Tail(t)| = (n-|S|)^{(t)} (n-t)!`. -/
theorem card_permutationMinTail_mul_descFactorial {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∀ t ≤ n, (permutationMinTail S t).card * n.descFactorial t =
      Fintype.card (Equiv.Perm (Fin n)) * (n - S.card).descFactorial t := by
  intro t
  induction t with
  | zero =>
      intro _
      simp [permutationMinTail]
  | succ t ih =>
      intro ht
      have hrec := card_permutationMinTail_succ_mul S hS (t := t) (by omega)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      calc (permutationMinTail S (t + 1)).card * ((n - t) * n.descFactorial t)
          = ((permutationMinTail S (t + 1)).card * (n - t)) * n.descFactorial t := by
            ring
        _ = ((permutationMinTail S t).card * (n - t - S.card)) * n.descFactorial t := by
            rw [hrec]
        _ = ((permutationMinTail S t).card * n.descFactorial t) * (n - t - S.card) := by
            ring
        _ = (Fintype.card (Equiv.Perm (Fin n)) * (n - S.card).descFactorial t) *
              (n - t - S.card) := by
            rw [ih (by omega)]
        _ = Fintype.card (Equiv.Perm (Fin n)) *
              ((n - S.card - t) * (n - S.card).descFactorial t) := by
            rw [show n - t - S.card = n - S.card - t by omega]
            ring

/-- For `t ≤ n`, the probability that every label of `S` has rank at
least `t` is `∏_{j<t} (n-|S|-j)/(n-j)`. -/
theorem card_permutationMinTail_div_eq_prod {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) {t : ℕ} (ht : t ≤ n) :
    ((permutationMinTail S t).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) =
      ∏ j ∈ range t, (((n - S.card - j : ℕ) : ℝ) / ((n - j : ℕ) : ℝ)) := by
  have hkey := card_permutationMinTail_mul_descFactorial S hS t ht
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  have hdescNat : n.descFactorial t ≠ 0 := by
    intro h
    have := Nat.descFactorial_eq_zero_iff_lt.mp h
    omega
  have hdesc : (0 : ℝ) < n.descFactorial t := by
    exact_mod_cast Nat.pos_of_ne_zero hdescNat
  have hnum : ∏ j ∈ range t, ((n - S.card - j : ℕ) : ℝ) =
      ((n - S.card).descFactorial t : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hden : ∏ j ∈ range t, ((n - j : ℕ) : ℝ) = (n.descFactorial t : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [prod_div_distrib, hnum, hden, div_eq_div_iff hcard.ne' hdesc.ne']
  exact_mod_cast hkey.trans (mul_comm _ _)

/-- Each factor is at most `(n-|S|)/n ≤ 2/3`, giving the geometric tail
bound when `n ≤ 3*|S|`. -/
theorem permutationMinTail_twoThirds {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (hthird : n ≤ 3 * S.card) :
    ∀ t < n,
      ((permutationMinTail S t).card : ℝ) ≤
        Fintype.card (Equiv.Perm (Fin n)) * ((2 : ℝ) / 3) ^ t := by
  intro t ht
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  rw [mul_comm, ← div_le_iff₀ hcard, card_permutationMinTail_div_eq_prod S hS ht.le]
  calc ∏ j ∈ range t, (((n - S.card - j : ℕ) : ℝ) / ((n - j : ℕ) : ℝ))
      ≤ ∏ _j ∈ range t, ((2 : ℝ) / 3) := by
        apply prod_le_prod
        · intro j _
          positivity
        · intro j hj
          have hjn : j < n := (mem_range.mp hj).trans ht
          have hpos : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_pos_of_lt hjn
          have hfactor : 3 * (n - S.card - j) ≤ 2 * (n - j) := by omega
          have hfactorR :
              (3 : ℝ) * ((n - S.card - j : ℕ) : ℝ) ≤ 2 * ((n - j : ℕ) : ℝ) := by
            exact_mod_cast hfactor
          rw [div_le_iff₀ hpos]
          linarith
    _ = ((2 : ℝ) / 3) ^ t := by
        rw [prod_const, card_range]

/-- The one-permutation moment bound for a nonempty set of density at least one third. -/
theorem singleMoment_three {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (hthird : n ≤ 3 * S.card) :
    ∑ p : Equiv.Perm (Fin n),
        ((5 : ℝ) / 4) ^ (permutationMin p S + 1) ≤
      3 * Fintype.card (Equiv.Perm (Fin n)) :=
  singleMoment_three_of_twoThirds_tail S hS
    (permutationMinTail_twoThirds S hS hthird)

/-- The union-bound estimate: `(5/4)^9 > 6`, hence `6^n < (5/4)^{9*n+1}`. -/
theorem six_pow_lt_five_four_pow_nine_mul {n : ℕ} (hn : 0 < n) :
    (6 : ℝ) ^ n < ((5 : ℝ) / 4) ^ (9 * n + 1) := by
  have hbase : (6 : ℝ) < ((5 : ℝ) / 4) ^ 9 := by norm_num
  have hpow : (6 : ℝ) ^ n < (((5 : ℝ) / 4) ^ 9) ^ n :=
    pow_lt_pow_left₀ hbase (by norm_num) hn.ne'
  have hexp : (((5 : ℝ) / 4) ^ 9) ^ n = ((5 : ℝ) / 4) ^ (9 * n) := by
    rw [← pow_mul]
  rw [hexp] at hpow
  exact hpow.trans (pow_lt_pow_right₀ (by norm_num) (by omega))

end

end DDNNFNegation
