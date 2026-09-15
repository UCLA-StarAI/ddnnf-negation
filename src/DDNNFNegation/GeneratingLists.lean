import DDNNFNegation.EncoderIndex

/-!
# Counting containing sets by their generating lists

A containing set has `2^r` elements, where `r = 4m - 4`. At step `j < r`, exactly
`2^j` vectors are already generated, leaving at least half the set as
choices. Thus each set has at least `(2^r / 2)^r` generating lists.

Lean represents these lists by independent tuples in the submodule.
Mathlib's `card_linearIndependent` proves their exact count by extending
a tuple by a vector outside its span, the same doubling argument.
`containing_sets_count` forgets the containing set and records only the
ambient tuple. Its injectivity is the tutorial's no-double-counting step:
a full-length list spans exactly its containing set. Dividing the total
list count by the per-set lower bound gives `32^(4m-4)`.
`containing_sets_bound` states the tutorial lemma by set cardinality;
its specialization is `m = n²` and `|G| = 16^(n²)`.

The lower bound is written `2^(r-1)` per choice to avoid division in
natural-number arithmetic. At `r = 0` the empty list is the unique list;
`codimension_four_sets_count` handles this case explicitly.
-/

namespace DDNNFNegation
open Finset Module
noncomputable section
variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G]

/-- An ordered generating list in a set of size `2^r` has at least half
that set available at each of its `r` doubling steps. -/
theorem generating_lists_lower_bound (r : ℕ) (H : Submodule (ZMod 2) G)
    (hH : finrank (ZMod 2) H = r) :
    (2 ^ (r - 1)) ^ r ≤ Nat.card {v : Fin r → H // LinearIndependent (ZMod 2) v} := by
  rw [card_linearIndependent (by omega), hH]
  have : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [this]
  calc (2 ^ (r - 1)) ^ r = ∏ _ : Fin r, (2 ^ (r - 1)) := by simp
    _ ≤ ∏ i : Fin r, (2 ^ r - 2 ^ i.val) := by
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      have hi : 2 ^ i.val * 2 ≤ 2 ^ r := by
        rw [← pow_succ]
        exact Nat.pow_le_pow_right (by omega) i.isLt
      have hir := i.isLt
      have hpow : 2 ^ (r - 1) * 2 = 2 ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      omega

/-- An independent list of full length generates its containing set uniquely. -/
theorem generating_list_span (r : ℕ) (H : Submodule (ZMod 2) G)
    (hH : finrank (ZMod 2) H = r)
    (v : Fin r → H) (hv : LinearIndependent (ZMod 2) v) :
    Submodule.span (ZMod 2) (Set.range (fun i => (v i : G))) = H := by
  have hspan := hv.span_eq_top_of_card_eq_finrank' (by simpa using hH.symm)
  have := congrArg (Submodule.map H.subtype) hspan
  simpa [Submodule.map_span, ← Set.range_comp, Function.comp_def] using this

/-- Count containing sets by disjoint families of generating lists. -/
theorem containing_sets_count (r : ℕ) :
    Nat.card {H : Submodule (ZMod 2) G // finrank (ZMod 2) H = r} *
      (2 ^ (r - 1)) ^ r ≤ Fintype.card G ^ r := by
  classical
  let A := {H : Submodule (ZMod 2) G // finrank (ZMod 2) H = r}
  let Lists (H : A) := {v : Fin r → H.val // LinearIndependent (ZMod 2) v}
  let : Fintype A := Fintype.ofFinite A
  let (H : A) : Fintype (Lists H) := Fintype.ofFinite _
  let forget : (Σ H : A, Lists H) → (Fin r → G) := fun p i => p.2.val i
  have hinj : Function.Injective forget := by
    rintro ⟨H, v⟩ ⟨K, w⟩ h
    have hHK : H = K := by
      apply Subtype.ext
      have hv := generating_list_span r H.val H.property v.val v.property
      have hw := generating_list_span r K.val K.property w.val w.property
      rw [← hv, ← hw]
      exact congrArg (fun f : Fin r → G => Submodule.span (ZMod 2) (Set.range f)) h
    subst K
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun h i)
  calc Nat.card A * (2 ^ (r - 1)) ^ r = ∑ H : A, (2 ^ (r - 1)) ^ r := by
        simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ H : A, Fintype.card (Lists H) := by
        apply sum_le_sum
        intro H _
        exact (generating_lists_lower_bound r H.val H.property).trans_eq
          Nat.card_eq_fintype_card
    _ = Fintype.card (Σ H : A, Lists H) := Fintype.card_sigma.symm
    _ ≤ Fintype.card (Fin r → G) := Fintype.card_le_of_injective forget hinj
    _ = Fintype.card G ^ r := by simp

/-- There are at most `32^(4m-4)` possible containing sets. The numerator
counts all lists; the denominator counts lists for each single set. -/
theorem codimension_four_sets_count (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card G = 16 ^ m) :
    Nat.card {H : Submodule (ZMod 2) G // finrank (ZMod 2) H = 4 * m - 4}
      ≤ 32 ^ (4 * m - 4) := by
  have h := containing_sets_count (G := G) (4 * m - 4)
  by_cases hm1 : m = 1
  · simp [hm1] at h ⊢
  · have hexp : (4 * m - 4 - 1) + 5 = 4 * m := by omega
    have heq : 32 ^ (4 * m - 4) * (2 ^ (4 * m - 4 - 1)) ^ (4 * m - 4) =
        Fintype.card G ^ (4 * m - 4) := by
      have hbase : 32 * 2 ^ (4 * m - 4 - 1) = 16 ^ m := by
        rw [show (32 : ℕ) = 2 ^ 5 by norm_num,
          show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_mul]
        congr 1
        omega
      rw [← mul_pow, hbase, hcard]
    rw [← heq] at h
    exact Nat.le_of_mul_le_mul_right h (by positivity)

/-- There are at most `32^(4m-4)` addition-closed containing sets of size
`|G|/16`. Over `𝔽₂`, nonempty addition-closed sets are precisely submodules.
The size equation avoids natural-number division; the preceding count uses
the equivalent dimension `4m-4`. -/
@[tutorial_box "lem:tutorial-containing-sets"]
theorem containing_sets_bound (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card G = 16 ^ m) :
    Nat.card {H : Submodule (ZMod 2) G // Nat.card H * 16 = Fintype.card G}
      ≤ 32 ^ (4 * m - 4) := by
  let byDimension :
      {H : Submodule (ZMod 2) G // Nat.card H * 16 = Fintype.card G} →
      {H : Submodule (ZMod 2) G // finrank (ZMod 2) H = 4 * m - 4} := fun ⟨H, h⟩ =>
    ⟨H, by
      rw [natCard_eq_two_pow_finrank, hcard,
        show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_mul] at h
      have := Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) h
      omega⟩
  have hinj : Function.Injective byDimension := by
    intro H K h
    apply Subtype.ext
    exact congrArg (fun H : {H : Submodule (ZMod 2) G //
      finrank (ZMod 2) H = 4 * m - 4} => H.val) h
  exact (Nat.card_le_card_of_injective byDimension hinj).trans
    (codimension_four_sets_count m hm hcard)

end
end DDNNFNegation
