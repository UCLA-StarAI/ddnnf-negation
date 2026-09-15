import Mathlib

/-!
# Finite monotone closure

An inflationary monotone operation on subsets of a finite type reaches its
least fixed point after at most one round per element.  This is the finite
fixed-point fact used to handle epsilon and unit rules without eliminating
them from a grammar.
-/

namespace DDNNFNegation

namespace FiniteClosure

variable {Fact : Type*} [Fintype Fact] [DecidableEq Fact]

def iterate (step : Finset Fact → Finset Fact) : ℕ → Finset Fact
  | 0 => ∅
  | n + 1 => step (iterate step n)

omit [Fintype Fact] [DecidableEq Fact] in
@[simp] theorem iterate_zero (step : Finset Fact → Finset Fact) :
    iterate step 0 = ∅ := rfl

omit [Fintype Fact] [DecidableEq Fact] in
@[simp] theorem iterate_succ (step : Finset Fact → Finset Fact) (n : ℕ) :
    iterate step (n + 1) = step (iterate step n) := rfl

omit [Fintype Fact] [DecidableEq Fact] in
theorem iterate_subset_succ (step : Finset Fact → Finset Fact)
    (hinflationary : ∀ facts, facts ⊆ step facts) (n : ℕ) :
    iterate step n ⊆ iterate step (n + 1) := by
  rw [iterate_succ]
  exact hinflationary _

omit [Fintype Fact] [DecidableEq Fact] in
theorem iterate_mono (step : Finset Fact → Finset Fact)
    (hinflationary : ∀ facts, facts ⊆ step facts) :
    Monotone (iterate step) :=
  monotone_nat_of_le_succ (iterate_subset_succ step hinflationary)

omit [Fintype Fact] [DecidableEq Fact] in
theorem iterate_eq_of_eq_succ (step : Finset Fact → Finset Fact)
    {m n : ℕ} (hm : iterate step (m + 1) = iterate step m)
    (hmn : m ≤ n) : iterate step n = iterate step m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  have hfixed : step (iterate step m) = iterate step m := by
    simpa only [iterate_succ] using hm
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by omega,
        iterate_succ, ih, hfixed]

theorem fixed_at_card (step : Finset Fact → Finset Fact)
    (hinflationary : ∀ facts, facts ⊆ step facts) :
    step (iterate step (Fintype.card Fact)) =
      iterate step (Fintype.card Fact) := by
  let total := Fintype.card Fact
  by_contra hfixed
  have hne : ∀ m ≤ total,
      iterate step (m + 1) ≠ iterate step m := by
    intro m hm hsame
    have hfinal := iterate_eq_of_eq_succ step hsame hm
    have hnext := iterate_eq_of_eq_succ step hsame (Nat.le_succ_of_le hm)
    apply hfixed
    rw [← iterate_succ step total, hnext, hfinal]
  have hcard : ∀ m ≤ total + 1, m ≤ (iterate step m).card := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        have hmTotal : m ≤ total := by omega
        have hsubset := iterate_subset_succ step hinflationary m
        have hstrict : (iterate step m).card <
            (iterate step (m + 1)).card :=
          Finset.card_lt_card (hsubset.ssubset_of_ne (hne m hmTotal).symm)
        omega
  have htooLarge := hcard (total + 1) le_rfl
  have hbounded : (iterate step (total + 1)).card ≤ total := by
    exact Finset.card_le_univ _
  omega

omit [Fintype Fact] [DecidableEq Fact] in
theorem iterate_subset_of_prefixed (step : Finset Fact → Finset Fact)
    (hmonotone : Monotone step) {closed : Finset Fact}
    (hclosed : step closed ⊆ closed) (n : ℕ) :
    iterate step n ⊆ closed := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ]
      exact (hmonotone ih).trans hclosed

theorem iterate_card_is_least_fixed_point
    (step : Finset Fact → Finset Fact)
    (hmonotone : Monotone step)
    (hinflationary : ∀ facts, facts ⊆ step facts) :
    IsLeast {facts : Finset Fact | step facts = facts}
      (iterate step (Fintype.card Fact)) := by
  constructor
  · exact fixed_at_card step hinflationary
  · intro closed hclosed
    exact iterate_subset_of_prefixed step hmonotone hclosed.le _

end FiniteClosure

end DDNNFNegation
