import Mathlib

/-!
# Positive product measures on Boolean assignments

Each variable has a rational probability strictly between zero and one.
Assignment weights multiply the corresponding factors. Summing these
weights defines event probabilities. The lemmas establish positivity,
normalization, independence on disjoint variable sets, and a common
denominator for the finite sums.
-/

namespace DDNNFNegation

open Finset

/-- A strictly positive rational product distribution on `Fin N → Bool`:
`p i` is the probability that position `i` is `true`. -/
structure ProductDist (N : ℕ) where
  p : Fin N → ℚ
  pos : ∀ i, 0 < p i
  lt_one : ∀ i, p i < 1

namespace ProductDist

open Classical

variable {N : ℕ} (π : ProductDist N)

/-- The weight of the value `b` at position `i`. -/
def w (i : Fin N) (b : Bool) : ℚ := if b then π.p i else 1 - π.p i

@[simp] theorem w_true (i : Fin N) : π.w i true = π.p i := rfl

@[simp] theorem w_false (i : Fin N) : π.w i false = 1 - π.p i := rfl

theorem w_pos (i : Fin N) (b : Bool) : 0 < π.w i b := by
  cases b
  · simp only [w_false]; linarith [π.lt_one i]
  · simpa using π.pos i

theorem w_add (i : Fin N) : π.w i true + π.w i false = 1 := by simp

theorem sum_w (i : Fin N) : ∑ b, π.w i b = 1 := by
  rw [Fintype.sum_bool, w_add]

theorem w_le_one (i : Fin N) (b : Bool) : π.w i b ≤ 1 := by
  have h1 := π.w_pos i true
  have h2 := π.w_pos i false
  have h := π.w_add i
  cases b <;> linarith

/-- The probability of a full assignment. -/
def prob (x : Fin N → Bool) : ℚ := ∏ i, π.w i (x i)

theorem prob_pos (x : Fin N → Bool) : 0 < π.prob x :=
  Finset.prod_pos fun i _ => π.w_pos i (x i)

theorem prob_nonneg (x : Fin N → Bool) : 0 ≤ π.prob x := (π.prob_pos x).le

theorem sum_prob : ∑ x, π.prob x = 1 := by
  unfold prob
  rw [← Fintype.prod_sum]
  simp_rw [sum_w]
  simp

/-- The expectation of a function. -/
def expect (F : (Fin N → Bool) → ℚ) : ℚ := ∑ x, F x * π.prob x

/-- The probability of an event. -/
noncomputable def mass (E : (Fin N → Bool) → Prop) : ℚ :=
  ∑ x, if E x then π.prob x else 0

theorem mass_eq_expect (E : (Fin N → Bool) → Prop) :
    π.mass E = π.expect fun x => if E x then 1 else 0 := by
  unfold mass expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : E x <;> simp [hx]

theorem mass_congr {E F : (Fin N → Bool) → Prop} (h : ∀ x, E x ↔ F x) :
    π.mass E = π.mass F := by
  unfold mass
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : E x
  · rw [if_pos hx, if_pos ((h x).1 hx)]
  · rw [if_neg hx, if_neg (fun hf => hx ((h x).2 hf))]

theorem mass_nonneg (E : (Fin N → Bool) → Prop) : 0 ≤ π.mass E :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> [exact π.prob_nonneg x; exact le_rfl]

theorem mass_true : π.mass (fun _ => True) = 1 := by
  unfold mass; simp [sum_prob]

theorem mass_false : π.mass (fun _ => False) = 0 := by
  unfold mass; simp

theorem mass_le_one (E : (Fin N → Bool) → Prop) : π.mass E ≤ 1 := by
  rw [← π.sum_prob]
  unfold mass
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs <;> [exact le_rfl; exact π.prob_nonneg x]

theorem mass_not (E : (Fin N → Bool) → Prop) : π.mass (fun x => ¬E x) = 1 - π.mass E := by
  rw [← π.sum_prob]
  unfold mass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : E x <;> simp [h]

/-- The mass of a disjoint union, over a finite family of pairwise
incompatible events. -/
theorem mass_exists_of_pairwise {ι : Type*} (s : Finset ι) (E : ι → (Fin N → Bool) → Prop)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x, ¬(E i x ∧ E j x)) :
    π.mass (fun x => ∃ i ∈ s, E i x) = ∑ i ∈ s, π.mass (E i) := by
  unfold mass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : ∃ i ∈ s, E i x
  · obtain ⟨i0, hi0, hE0⟩ := hx
    rw [if_pos ⟨i0, hi0, hE0⟩, Finset.sum_eq_single i0]
    · rw [if_pos hE0]
    · intro j hj hne
      rw [if_neg (fun hE => h j hj i0 hi0 hne x ⟨hE, hE0⟩)]
    · intro habs; exact absurd hi0 habs
  · rw [if_neg hx]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg (fun hE => hx ⟨i, hi, hE⟩)]

/-! ## Evidence -/

/-- A partial assignment: `some b` fixes a position, `none` leaves it free. -/
abbrev Evidence (N : ℕ) := Fin N → Option Bool

/-- Agreement with the evidence on the positions in `S`. -/
def ConsistentOn (e : Evidence N) (S : Finset (Fin N)) (x : Fin N → Bool) : Prop :=
  ∀ i ∈ S, ∀ b, e i = some b → x i = b

/-- Agreement with the evidence everywhere. -/
def Consistent (e : Evidence N) (x : Fin N → Bool) : Prop :=
  ∀ i b, e i = some b → x i = b

theorem consistent_iff_consistentOn_univ (e : Evidence N) (x : Fin N → Bool) :
    Consistent e x ↔ ConsistentOn e univ x := by
  simp [Consistent, ConsistentOn]

theorem consistentOn_union (e : Evidence N) (S T : Finset (Fin N)) (x : Fin N → Bool) :
    ConsistentOn e (S ∪ T) x ↔ ConsistentOn e S x ∧ ConsistentOn e T x := by
  simp only [ConsistentOn, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨h1, h2⟩ i (hi | hi)
    · exact h1 i hi
    · exact h2 i hi

theorem consistentOn_sdiff_union (e : Evidence N) {S T : Finset (Fin N)} (hT : T ⊆ S)
    (x : Fin N → Bool) :
    ConsistentOn e S x ↔ ConsistentOn e T x ∧ ConsistentOn e (S \ T) x := by
  rw [← consistentOn_union, Finset.union_sdiff_of_subset hT]

/-- The mass of the evidence at one position: `1` at a free position, the
weight of the fixed value otherwise. -/
def localMass (e : Evidence N) (i : Fin N) : ℚ :=
  match e i with
  | none => π.w i true + π.w i false
  | some b => π.w i b

theorem localMass_pos (e : Evidence N) (i : Fin N) : 0 < π.localMass e i := by
  unfold localMass
  cases e i with
  | none => simp
  | some b => exact π.w_pos i b

theorem localMass_le_one (e : Evidence N) (i : Fin N) : π.localMass e i ≤ 1 := by
  unfold localMass
  cases e i with
  | none => simp
  | some b => exact π.w_le_one i b

/-- The local factor of the consistency indicator at position `i` and
value `b`. -/
def localFactor (e : Evidence N) (S : Finset (Fin N)) (i : Fin N) (b : Bool) : ℚ :=
  if (i ∈ S → ∀ b', e i = some b' → b = b') then π.w i b else 0

theorem sum_localFactor (e : Evidence N) (S : Finset (Fin N)) (i : Fin N) :
    ∑ b, π.localFactor e S i b = if i ∈ S then π.localMass e i else 1 := by
  unfold localFactor localMass
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    cases he : e i with
    | none =>
      have hc : ∀ b, (i ∈ S → ∀ b', (none : Option Bool) = some b' → b = b') := by
        intro b _ b' hb'; cases hb'
      rw [Finset.sum_congr rfl (fun b _ => if_pos (hc b)), Fintype.sum_bool]
    | some b' =>
      have hc : ∀ b, (i ∈ S → ∀ b'', some b' = some b'' → b = b'') ↔ b = b' := by
        intro b
        constructor
        · intro h; exact h hi b' rfl
        · intro h _ b'' hb''; cases hb''; exact h
      simp_rw [hc]
      rw [Fintype.sum_bool]
      cases b' <;> simp
  · rw [if_neg hi]
    have hc : ∀ b, (i ∈ S → ∀ b', e i = some b' → b = b') := fun b h => absurd h hi
    rw [Finset.sum_congr rfl (fun b _ => if_pos (hc b))]
    exact π.sum_w i

theorem prod_localFactor (e : Evidence N) (S : Finset (Fin N)) (x : Fin N → Bool) :
    ∏ i, π.localFactor e S i (x i) = if ConsistentOn e S x then π.prob x else 0 := by
  unfold localFactor prob
  rw [Finset.prod_ite_zero]
  congr 1
  apply propext
  simp only [Finset.mem_univ, true_implies, ConsistentOn]

/-- The probability of agreeing with the evidence on `S`. -/
theorem mass_consistentOn (e : Evidence N) (S : Finset (Fin N)) :
    π.mass (ConsistentOn e S) = ∏ i ∈ S, π.localMass e i := by
  unfold mass
  have h : ∀ x, (if ConsistentOn e S x then π.prob x else 0) =
      ∏ i, π.localFactor e S i (x i) := fun x => (π.prod_localFactor e S x).symm
  simp_rw [h]
  rw [← Fintype.prod_sum]
  simp_rw [sum_localFactor]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem mass_consistent (e : Evidence N) :
    π.mass (Consistent e) = ∏ i, π.localMass e i := by
  rw [π.mass_congr (consistent_iff_consistentOn_univ e), mass_consistentOn]

/-- The evidence fixing one position. -/
def singleEvidence (i : Fin N) (b : Bool) : Evidence N :=
  fun j => if j = i then some b else none

theorem consistentOn_singleEvidence (i : Fin N) (b : Bool) (x : Fin N → Bool) :
    ConsistentOn (singleEvidence i b) {i} x ↔ x i = b := by
  simp [ConsistentOn, singleEvidence]

/-- The probability that one position takes the value `b`. -/
theorem mass_coord (i : Fin N) (b : Bool) : π.mass (fun x => x i = b) = π.w i b := by
  rw [← π.mass_congr (consistentOn_singleEvidence i b), mass_consistentOn,
    Finset.prod_singleton]
  simp [localMass, singleEvidence]

theorem mass_consistentOn_pos (e : Evidence N) (S : Finset (Fin N)) :
    0 < π.mass (ConsistentOn e S) := by
  rw [mass_consistentOn]
  exact Finset.prod_pos fun i _ => π.localMass_pos e i

/-- The probability of agreeing with the evidence on `S`, as the product the
algorithm computes. -/
def evidenceMass (e : Evidence N) (S : Finset (Fin N)) : ℚ := ∏ i ∈ S, π.localMass e i

theorem mass_consistentOn_eq_evidenceMass (e : Evidence N) (S : Finset (Fin N)) :
    π.mass (ConsistentOn e S) = π.evidenceMass e S :=
  π.mass_consistentOn e S

theorem evidenceMass_pos (e : Evidence N) (S : Finset (Fin N)) : 0 < π.evidenceMass e S :=
  Finset.prod_pos fun i _ => π.localMass_pos e i

/-! ## Exact arithmetic: a common denominator -/

/-- The product of the denominators of the parameters: a common denominator
of every event probability. -/
def denomBound : ℕ := ∏ i, (π.p i).den

theorem denomBound_pos : 0 < π.denomBound := Finset.prod_pos fun i _ => (π.p i).den_pos

theorem w_mul_den_eq_intCast (i : Fin N) (b : Bool) :
    ∃ z : ℤ, π.w i b * ((π.p i).den : ℚ) = z := by
  cases b
  · refine ⟨((π.p i).den : ℤ) - (π.p i).num, ?_⟩
    simp only [w_false, sub_mul, one_mul, Rat.mul_den_eq_num]
    push_cast
    ring
  · exact ⟨(π.p i).num, by simp [Rat.mul_den_eq_num]⟩

theorem prob_mul_denomBound_eq_intCast (x : Fin N → Bool) :
    ∃ z : ℤ, π.prob x * (π.denomBound : ℚ) = z := by
  unfold prob denomBound
  push_cast
  rw [← Finset.prod_mul_distrib]
  choose z hz using fun i => π.w_mul_den_eq_intCast i (x i)
  refine ⟨∏ i, z i, ?_⟩
  push_cast
  exact Finset.prod_congr rfl fun i _ => hz i

/-- Every event probability is `k / D` for a natural number `k ≤ D`, with
`D = denomBound` the product of the parameter denominators. -/
theorem mass_mul_denomBound_eq_natCast (E : (Fin N → Bool) → Prop) :
    ∃ k : ℕ, π.mass E * (π.denomBound : ℚ) = k ∧ k ≤ π.denomBound := by
  choose z hz using π.prob_mul_denomBound_eq_intCast
  have hsum : π.mass E * (π.denomBound : ℚ) = ((∑ x, if E x then z x else 0 : ℤ) : ℚ) := by
    unfold mass
    rw [Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · exact hz x
    · simp
  have hnonneg : (0 : ℚ) ≤ ((∑ x, if E x then z x else 0 : ℤ) : ℚ) := by
    rw [← hsum]
    exact mul_nonneg (π.mass_nonneg E) (by positivity)
  have hnonneg' : (0 : ℤ) ≤ ∑ x, if E x then z x else 0 := by exact_mod_cast hnonneg
  refine ⟨(∑ x, if E x then z x else 0).toNat, ?_, ?_⟩
  · rw [hsum]
    exact_mod_cast (Int.toNat_of_nonneg hnonneg').symm
  · have h1 : π.mass E * (π.denomBound : ℚ) ≤ π.denomBound := by
      calc π.mass E * (π.denomBound : ℚ) ≤ 1 * π.denomBound :=
            mul_le_mul_of_nonneg_right (π.mass_le_one E) (by positivity)
        _ = π.denomBound := one_mul _
    have h3 : (((∑ x, if E x then z x else 0).toNat : ℕ) : ℚ) =
        π.mass E * (π.denomBound : ℚ) := by
      rw [hsum]
      have : (((∑ x, if E x then z x else 0).toNat : ℕ) : ℚ) =
          (((∑ x, if E x then z x else 0).toNat : ℤ) : ℚ) := (Int.cast_natCast _).symm
      rw [this, Int.toNat_of_nonneg hnonneg']
    have h4 : (((∑ x, if E x then z x else 0).toNat : ℕ) : ℚ) ≤ (π.denomBound : ℚ) := by
      rw [h3]; exact h1
    exact_mod_cast h4

/-! ## Independence -/

/-- `F` depends only on the positions in `S`. -/
def DependsOn (S : Finset (Fin N)) (F : (Fin N → Bool) → ℚ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → F x = F y

theorem dependsOn_indicator {S : Finset (Fin N)} {E : (Fin N → Bool) → Prop}
    (h : ∀ x y, (∀ i ∈ S, x i = y i) → (E x ↔ E y)) :
    DependsOn S (fun x => if E x then (1 : ℚ) else 0) := by
  intro x y hxy
  show (if E x then (1 : ℚ) else 0) = if E y then 1 else 0
  by_cases hx : E x
  · rw [if_pos hx, if_pos ((h x y hxy).1 hx)]
  · rw [if_neg hx, if_neg (fun hy => hx ((h x y hxy).2 hy))]

theorem consistentOn_dependsOn (e : Evidence N) (S : Finset (Fin N)) (x y : Fin N → Bool)
    (hxy : ∀ i ∈ S, x i = y i) : ConsistentOn e S x ↔ ConsistentOn e S y := by
  unfold ConsistentOn
  constructor
  · intro h i hi b hb; rw [← hxy i hi]; exact h i hi b hb
  · intro h i hi b hb; rw [hxy i hi]; exact h i hi b hb

section Split

variable (S : Finset (Fin N))

/-- The split of an assignment into its parts on `S` and outside `S`. -/
abbrev splitEquiv : (Fin N → Bool) ≃ ({i // i ∈ S} → Bool) × ({i // i ∉ S} → Bool) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)

theorem splitEquiv_symm_apply_of_mem (a : {i // i ∈ S} → Bool) (b : {i // i ∉ S} → Bool)
    (i : Fin N) (hi : i ∈ S) : (splitEquiv S).symm (a, b) i = a ⟨i, hi⟩ := by
  simp [splitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

theorem splitEquiv_symm_apply_of_not_mem (a : {i // i ∈ S} → Bool) (b : {i // i ∉ S} → Bool)
    (i : Fin N) (hi : i ∉ S) : (splitEquiv S).symm (a, b) i = b ⟨i, hi⟩ := by
  simp [splitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

/-- The weight of the part of an assignment on a set of positions. -/
def partWeight {P : Fin N → Prop} [DecidablePred P] (a : {i // P i} → Bool) : ℚ :=
  ∏ i : {i // P i}, π.w i (a i)

theorem sum_partWeight {P : Fin N → Prop} [DecidablePred P] [inst : Fintype {i // P i}] :
    ∑ a : {i // P i} → Bool, π.partWeight a = 1 := by
  obtain rfl : inst = Subtype.fintype P := Subsingleton.elim _ _
  unfold partWeight
  rw [← Fintype.prod_sum]
  simp_rw [sum_w]
  simp

theorem prob_splitEquiv_symm (a : {i // i ∈ S} → Bool) (b : {i // i ∉ S} → Bool) :
    π.prob ((splitEquiv S).symm (a, b)) = π.partWeight a * π.partWeight b := by
  unfold prob partWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [splitEquiv_symm_apply_of_mem S a b i i.2]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [splitEquiv_symm_apply_of_not_mem S a b i i.2]

theorem sum_split (H : (Fin N → Bool) → ℚ) :
    ∑ x, H x = ∑ a, ∑ b, H ((splitEquiv S).symm (a, b)) := by
  rw [← Equiv.sum_comp (splitEquiv S).symm H, Fintype.sum_prod_type]

end Split

/-- Functions of disjoint sets of positions are independent. -/
theorem expect_mul_of_disjoint {S T : Finset (Fin N)} {F G : (Fin N → Bool) → ℚ}
    (hF : DependsOn S F) (hG : DependsOn T G) (hd : Disjoint S T) :
    π.expect (fun x => F x * G x) = π.expect F * π.expect G := by
  let a₀ : {i // i ∈ S} → Bool := fun _ => false
  let b₀ : {i // i ∉ S} → Bool := fun _ => false
  have hFa : ∀ a b, F ((splitEquiv S).symm (a, b)) = F ((splitEquiv S).symm (a, b₀)) := by
    intro a b
    apply hF
    intro i hi
    rw [splitEquiv_symm_apply_of_mem S a b i hi, splitEquiv_symm_apply_of_mem S a b₀ i hi]
  have hGb : ∀ a b, G ((splitEquiv S).symm (a, b)) = G ((splitEquiv S).symm (a₀, b)) := by
    intro a b
    apply hG
    intro i hi
    have hiS : i ∉ S := Finset.disjoint_right.1 hd hi
    rw [splitEquiv_symm_apply_of_not_mem S a b i hiS,
      splitEquiv_symm_apply_of_not_mem S a₀ b i hiS]
  have hprob := π.prob_splitEquiv_symm S
  unfold expect
  simp only [sum_split S]
  simp_rw [hprob]
  have h1 : ∀ a, ∑ b, F ((splitEquiv S).symm (a, b)) * G ((splitEquiv S).symm (a, b)) *
      (π.partWeight a * π.partWeight b) =
      (F ((splitEquiv S).symm (a, b₀)) * π.partWeight a) *
        ∑ b, G ((splitEquiv S).symm (a₀, b)) * π.partWeight b := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hFa a b, hGb a b]; ring
  have h2 : ∀ a, ∑ b, F ((splitEquiv S).symm (a, b)) * (π.partWeight a * π.partWeight b) =
      F ((splitEquiv S).symm (a, b₀)) * π.partWeight a := by
    intro a
    have : ∑ b, F ((splitEquiv S).symm (a, b)) * (π.partWeight a * π.partWeight b) =
        (F ((splitEquiv S).symm (a, b₀)) * π.partWeight a) *
          ∑ b : {i // i ∉ S} → Bool, π.partWeight b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hFa a b]; ring
    rw [this, π.sum_partWeight (P := fun i => i ∉ S), mul_one]
  have h3 : ∑ a, ∑ b, G ((splitEquiv S).symm (a, b)) * (π.partWeight a * π.partWeight b) =
      ∑ b, G ((splitEquiv S).symm (a₀, b)) * π.partWeight b := by
    rw [Finset.sum_comm]
    have : ∀ b, ∑ a, G ((splitEquiv S).symm (a, b)) * (π.partWeight a * π.partWeight b) =
        (G ((splitEquiv S).symm (a₀, b)) * π.partWeight b) *
          ∑ a : {i // i ∈ S} → Bool, π.partWeight a := by
      intro b
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hGb a b]; ring
    rw [Finset.sum_congr rfl (fun b _ => this b), ← Finset.sum_mul,
      π.sum_partWeight (P := fun i => i ∈ S), mul_one]
  simp_rw [h1, h2]
  rw [h3, ← Finset.sum_mul]

/-- Independence of two events on disjoint sets of positions. -/
theorem mass_and_of_disjoint {S T : Finset (Fin N)} {E F : (Fin N → Bool) → Prop}
    (hE : ∀ x y, (∀ i ∈ S, x i = y i) → (E x ↔ E y))
    (hF : ∀ x y, (∀ i ∈ T, x i = y i) → (F x ↔ F y)) (hd : Disjoint S T) :
    π.mass (fun x => E x ∧ F x) = π.mass E * π.mass F := by
  rw [mass_eq_expect, mass_eq_expect, mass_eq_expect,
    ← π.expect_mul_of_disjoint (dependsOn_indicator hE) (dependsOn_indicator hF) hd]
  unfold expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : E x <;> by_cases hy : F x <;> simp [hx, hy]

end ProductDist

end DDNNFNegation
