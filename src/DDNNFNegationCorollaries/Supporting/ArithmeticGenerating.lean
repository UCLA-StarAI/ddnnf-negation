import DDNNFNegationCorollaries.Supporting.ArithmeticSupport

/-!
# Assignment encodings of multilinear polynomials

The assignment encoding gives each absent variable its complementary
indicator. Following the conversion of Broadrick, Zhang, and Van den
Broeck, Lemma 3, pad the Boolean support circuit so it tests all positions.
The resulting DNNF has size `O(N * (s + 1))`. This transfers the DNNF
lower bound to monotone arithmetic circuits for the missing monomials.
-/

namespace DDNNFNegation

open MvPolynomial Finset

/-! ## Selected monomials -/

section selected

variable {N : ℕ}

/-- The exponent vector of the multilinear monomial `∏_{i ∈ S, x i} X_i`. -/
noncomputable def selected (x : Fin N → Bool) (S : Finset (Fin N)) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ if i ∈ S ∧ x i = true then 1 else 0

@[simp] theorem selected_apply (x : Fin N → Bool) (S : Finset (Fin N)) (i : Fin N) :
    selected x S i = if i ∈ S ∧ x i = true then 1 else 0 := by
  simp [selected]

theorem selected_apply_of_mem {x : Fin N → Bool} {S : Finset (Fin N)} {i : Fin N}
    (hi : i ∈ S) : selected x S i = if x i = true then 1 else 0 := by
  simp [hi]

theorem selected_apply_of_notMem {x : Fin N → Bool} {S : Finset (Fin N)} {i : Fin N}
    (hi : i ∉ S) : selected x S i = 0 := by
  simp [hi]

theorem selected_le_one (x : Fin N → Bool) (S : Finset (Fin N)) (i : Fin N) :
    selected x S i ≤ 1 := by
  rw [selected_apply]
  split_ifs <;> omega

theorem selected_empty (x : Fin N → Bool) : selected x ∅ = 0 := by
  ext i
  simp

theorem selected_support_subset (x : Fin N → Bool) (S : Finset (Fin N)) :
    (selected x S).support ⊆ S := by
  intro i hi
  rw [Finsupp.mem_support_iff, selected_apply] at hi
  by_contra h
  exact hi (by simp [h])

/-- Selecting inside a larger set changes nothing when the extra positions
are all false. -/
theorem selected_eq_of_subset {x : Fin N → Bool} {S' S : Finset (Fin N)} (hsub : S' ⊆ S)
    (hfalse : ∀ i ∈ S, i ∉ S' → x i = false) : selected x S = selected x S' := by
  ext i
  by_cases hi' : i ∈ S'
  · rw [selected_apply_of_mem (hsub hi'), selected_apply_of_mem hi']
  · rw [selected_apply_of_notMem hi']
    by_cases hi : i ∈ S
    · rw [selected_apply_of_mem hi, hfalse i hi hi']
      simp
    · exact selected_apply_of_notMem hi

theorem selected_union_of_disjoint {x : Fin N → Bool} {S T : Finset (Fin N)}
    (h : Disjoint S T) : selected x (S ∪ T) = selected x S + selected x T := by
  ext i
  rw [Finsupp.add_apply]
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.mp h hS
    rw [selected_apply_of_mem (mem_union_left _ hS), selected_apply_of_mem hS,
      selected_apply_of_notMem hT, add_zero]
  · by_cases hT : i ∈ T
    · rw [selected_apply_of_mem (mem_union_right _ hT), selected_apply_of_mem hT,
        selected_apply_of_notMem hS, zero_add]
    · rw [selected_apply_of_notMem hS, selected_apply_of_notMem hT,
        selected_apply_of_notMem (by simp [hS, hT])]

theorem selected_univ_injective :
    Function.Injective (fun x : Fin N → Bool ↦ selected x univ) := by
  intro x y h
  funext i
  have hi := DFunLike.congr_fun h i
  simp only [selected_apply, mem_univ, true_and] at hi
  cases hx : x i <;> cases hy : y i <;> simp [hx, hy] at hi ⊢

/-- The multilinear exponent vectors are exactly the selected ones. -/
theorem multilinear_iff_exists_selected (m : Fin N →₀ ℕ) :
    (∀ i, m i ≤ 1) ↔ ∃ x : Fin N → Bool, m = selected x univ := by
  constructor
  · intro h
    refine ⟨fun i ↦ decide (m i = 1), ?_⟩
    ext i
    simp only [selected_apply, mem_univ, true_and, decide_eq_true_eq]
    have := h i
    split_ifs with h1 <;> omega
  · rintro ⟨x, rfl⟩ i
    exact selected_le_one x univ i

/-- Membership of a selected monomial, restricted to a set containing every
variable of the polynomial. -/
theorem selected_mem_support_iff {p : MvPolynomial (Fin N) ℝ} {x : Fin N → Bool}
    {S' S : Finset (Fin N)} (hsub : S' ⊆ S)
    (hvars : ∀ m ∈ p.support, m.support ⊆ S') :
    selected x S ∈ p.support ↔
      selected x S' ∈ p.support ∧ ∀ i ∈ S, i ∉ S' → x i = false := by
  constructor
  · intro h
    have hfalse : ∀ i ∈ S, i ∉ S' → x i = false := by
      intro i hi hi'
      cases hxi : x i with
      | false => rfl
      | true =>
        exfalso
        apply hi'
        apply hvars _ h
        rw [Finsupp.mem_support_iff, selected_apply_of_mem hi, hxi]
        simp
    refine ⟨?_, hfalse⟩
    rwa [selected_eq_of_subset hsub hfalse] at h
  · rintro ⟨h, hfalse⟩
    rw [selected_eq_of_subset hsub hfalse]
    exact h

/-- Membership of a selected monomial in a product of polynomials with
nonnegative coefficients and disjoint variable sets. -/
theorem selected_mem_support_mul_iff {p q : MvPolynomial (Fin N) ℝ}
    (hp : ∀ m, 0 ≤ coeff m p) (hq : ∀ m, 0 ≤ coeff m q) {x : Fin N → Bool}
    {S T : Finset (Fin N)} (hdisj : Disjoint S T)
    (hvp : ∀ m ∈ p.support, m.support ⊆ S) (hvq : ∀ m ∈ q.support, m.support ⊆ T) :
    selected x (S ∪ T) ∈ (p * q).support ↔
      selected x S ∈ p.support ∧ selected x T ∈ q.support := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp (support_mul p q h)
    have hu' : u = selected x S := by
      ext i
      have hi := DFunLike.congr_fun huv i
      rw [Finsupp.add_apply] at hi
      by_cases hiS : i ∈ S
      · have hiT : i ∉ T := Finset.disjoint_left.mp hdisj hiS
        have hv0 : v i = 0 :=
          Finsupp.notMem_support_iff.mp fun hm ↦ hiT (hvq v hv hm)
        rw [selected_apply_of_mem (mem_union_left _ hiS), hv0, add_zero] at hi
        rw [selected_apply_of_mem hiS]
        exact hi
      · have hu0 : u i = 0 :=
          Finsupp.notMem_support_iff.mp fun hm ↦ hiS (hvp u hu hm)
        rw [selected_apply_of_notMem hiS]
        exact hu0
    have hv' : v = selected x T := by
      ext i
      have hi := DFunLike.congr_fun huv i
      rw [Finsupp.add_apply] at hi
      by_cases hiT : i ∈ T
      · have hiS : i ∉ S := Finset.disjoint_right.mp hdisj hiT
        have hu0 : u i = 0 :=
          Finsupp.notMem_support_iff.mp fun hm ↦ hiS (hvp u hu hm)
        rw [selected_apply_of_mem (mem_union_right _ hiT), hu0, zero_add] at hi
        rw [selected_apply_of_mem hiT]
        exact hi
      · have hv0 : v i = 0 :=
          Finsupp.notMem_support_iff.mp fun hm ↦ hiT (hvq v hv hm)
        rw [selected_apply_of_notMem hiT]
        exact hv0
    rw [hu'] at hu
    rw [hv'] at hv
    exact ⟨hu, hv⟩
  · rintro ⟨hu, hv⟩
    rw [selected_union_of_disjoint hdisj]
    exact add_mem_support_mul_of_nonneg p q hp hq hu hv

/-- Splitting the positions at or beyond `k` into position `k` and the
positions beyond it. -/
theorem filter_le_eq_union_filter_succ (D : Finset (Fin N)) (k : ℕ) (hk : k < N) :
    D.filter (fun i ↦ k ≤ i.1) =
      (if (⟨k, hk⟩ : Fin N) ∈ D then {(⟨k, hk⟩ : Fin N)} else ∅) ∪
        D.filter (fun i ↦ k + 1 ≤ i.1) := by
  ext i
  simp only [mem_filter, mem_union]
  split_ifs with hD
  · simp only [mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hik : i.1 = k
      · exact Or.inl (Fin.ext hik)
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        exact ⟨hD, le_rfl⟩
      · exact ⟨h1, by omega⟩
  · simp only [Finset.notMem_empty, false_or]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hlt
      have : i = ⟨k, hk⟩ := Fin.ext (show i.1 = k by omega)
      subst this
      exact hD h1
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩

/-- The same split for a universally quantified statement. -/
theorem forall_le_iff_and_forall_succ (D : Finset (Fin N)) (k : ℕ) (hk : k < N)
    (P : Fin N → Prop) :
    (∀ i ∈ D, k ≤ i.1 → P i) ↔
      ((⟨k, hk⟩ : Fin N) ∈ D → P ⟨k, hk⟩) ∧ ∀ i ∈ D, k + 1 ≤ i.1 → P i := by
  constructor
  · intro h
    exact ⟨fun hD ↦ h _ hD le_rfl, fun i hi hki ↦ h i hi (by omega)⟩
  · rintro ⟨h0, h⟩ i hi hki
    by_cases hik : k + 1 ≤ i.1
    · exact h i hi hik
    · have : i = ⟨k, hk⟩ := Fin.ext (show i.1 = k by omega)
      subst this
      exact h0 hi

end selected

/-! ## Selected supports of an unpaired circuit -/

section unpaired

variable {N : ℕ}

namespace ArithNode

variable {Gate : Type*}

/-- Selected supports from the children's: a product with overlapping factors
is dropped. -/
def selectedVars (child : Gate → Finset (Fin N)) :
    ArithNode (Fin N) Gate → Finset (Fin N)
  | const _ => ∅
  | var i => {i}
  | add left right => child left ∪ child right
  | mul left right =>
      if Disjoint (child left) (child right) then child left ∪ child right else ∅

theorem selectedVars_congr (node : ArithNode (Fin N) Gate)
    (c₁ c₂ : Gate → Finset (Fin N))
    (h : ∀ child, node.IsChild child → c₁ child = c₂ child) :
    node.selectedVars c₁ = node.selectedVars c₂ := by
  cases node with
  | const c => rfl
  | var x => rfl
  | add left right =>
      simp only [selectedVars]
      rw [h left (Or.inl rfl), h right (Or.inr rfl)]
  | mul left right =>
      simp only [selectedVars]
      rw [h left (Or.inl rfl), h right (Or.inr rfl)]

/-- The child on one side of a sum; `none` at every other node. -/
def addChild : ArithNode (Fin N) Gate → Bool → Option Gate
  | add left right, b => some (if b then left else right)
  | _, _ => none

theorem addChild_add_true (left right : Gate) :
    (add left right : ArithNode (Fin N) Gate).addChild true = some left := rfl

theorem addChild_add_false (left right : Gate) :
    (add left right : ArithNode (Fin N) Gate).addChild false = some right := rfl

theorem addChild_isChild {node : ArithNode (Fin N) Gate} {b : Bool} {c : Gate}
    (h : node.addChild b = some c) : node.IsChild c := by
  cases node with
  | const _ => cases h
  | var _ => cases h
  | mul _ _ => cases h
  | add left right =>
      simp only [addChild, Option.some.injEq] at h
      subst h
      cases b <;> simp [IsChild]

end ArithNode

namespace ArithCircuit

open Classical in
/-- The selected support of a gate: the positions occurring in its
monomials, after pruning zero subcircuits and overlapping products. -/
noncomputable def selectedSupport (C : ArithCircuit (Fin N)) (gate : C.Gate) :
    Finset (Fin N) :=
  if C.poly gate = 0 then ∅ else
    (C.node gate).selectedVars fun child ↦
      if _h : (C.node gate).IsChild child then C.selectedSupport child else ∅
termination_by C.rank gate
decreasing_by exact C.child_rank gate child _h

variable (C : ArithCircuit (Fin N))

open Classical in
theorem selectedSupport_eq (gate : C.Gate) :
    C.selectedSupport gate =
      if C.poly gate = 0 then ∅ else (C.node gate).selectedVars C.selectedSupport := by
  rw [selectedSupport]
  split_ifs
  · rfl
  · apply ArithNode.selectedVars_congr
    intro child hchild
    simp [hchild]

variable {C}

/-- Every position in the selected support of a gate occurs in one of its
monomials. -/
theorem exists_mem_support_of_mem_selectedSupport (hmono : C.IsMonotone) :
    ∀ gate, ∀ i ∈ C.selectedSupport gate, ∃ m ∈ (C.poly gate).support, m i ≠ 0 := by
  intro gate
  induction gate using C.induction_rank with
  | _ gate ih =>
  rw [selectedSupport_eq]
  split_ifs with h0
  · intro i hi
    exact absurd hi (Finset.notMem_empty i)
  · cases hnode : C.node gate with
    | const c =>
        intro i hi
        exact absurd hi (Finset.notMem_empty i)
    | var j =>
        intro i hi
        simp only [ArithNode.selectedVars, mem_singleton] at hi
        subst hi
        rw [C.poly_eq gate, hnode]
        refine ⟨Finsupp.single i 1, ?_, ?_⟩
        · simp [ArithNode.eval, MvPolynomial.support_X]
        · simp
    | add left right =>
        have hl := ih left (by rw [hnode]; exact Or.inl rfl)
        have hr := ih right (by rw [hnode]; exact Or.inr rfl)
        have hsupp : (C.poly gate).support =
            (C.poly left).support ∪ (C.poly right).support := by
          rw [C.poly_eq gate, hnode]
          exact support_add_of_nonneg _ _ (C.coeff_nonneg hmono left)
            (C.coeff_nonneg hmono right)
        simp only [ArithNode.selectedVars]
        intro i hi
        rw [hsupp]
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨d, hd, hdi⟩ := hl i hi
          exact ⟨d, Finset.mem_union_left _ hd, hdi⟩
        · obtain ⟨d, hd, hdi⟩ := hr i hi
          exact ⟨d, Finset.mem_union_right _ hd, hdi⟩
    | mul left right =>
        have hprod : C.poly gate = C.poly left * C.poly right := by
          rw [C.poly_eq gate, hnode]
          rfl
        have hl0 : C.poly left ≠ 0 := fun h ↦ h0 (by rw [hprod, h, zero_mul])
        have hr0 : C.poly right ≠ 0 := fun h ↦ h0 (by rw [hprod, h, mul_zero])
        obtain ⟨u, hu⟩ := exists_mem_support_of_ne_zero hl0
        obtain ⟨v, hv⟩ := exists_mem_support_of_ne_zero hr0
        have hl := ih left (by rw [hnode]; exact Or.inl rfl)
        have hr := ih right (by rw [hnode]; exact Or.inr rfl)
        simp only [ArithNode.selectedVars]
        split_ifs with hdisj
        · intro i hi
          rw [hprod]
          rcases Finset.mem_union.mp hi with hi | hi
          · obtain ⟨d, hd, hdi⟩ := hl i hi
            refine ⟨d + v, add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
              (C.coeff_nonneg hmono right) hd hv, ?_⟩
            simp only [Finsupp.add_apply]
            omega
          · obtain ⟨d, hd, hdi⟩ := hr i hi
            refine ⟨u + d, add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
              (C.coeff_nonneg hmono right) hu hd, ?_⟩
            simp only [Finsupp.add_apply]
            omega
        · intro i hi
          exact absurd hi (Finset.notMem_empty i)

/-- At a contributing product of a circuit with multilinear output, the two
factors have disjoint selected supports: a common position would give a
squared variable in an output monomial. -/
theorem selectedSupport_disjoint_of_extends (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m i ≤ 1)
    {gate left right : C.Gate} (hnode : C.node gate = .mul left right)
    (h : C.Extends gate) :
    Disjoint (C.selectedSupport left) (C.selectedSupport right) := by
  have hprod : C.poly gate = C.poly left * C.poly right := by
    rw [C.poly_eq gate, hnode]
    rfl
  by_contra hnd
  obtain ⟨i, hil, hir⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨d, hd, hdi⟩ := exists_mem_support_of_mem_selectedSupport hmono left i hil
  obtain ⟨d', hd', hdi'⟩ := exists_mem_support_of_mem_selectedSupport hmono right i hir
  have hmem : d + d' ∈ (C.poly gate).support := by
    rw [hprod]
    exact add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
      (C.coeff_nonneg hmono right) hd hd'
  obtain ⟨m', hm', hle⟩ := h (d + d') hmem
  have h1 := hout m' hm' i
  have h2 : (d + d') i ≤ m' i := hle i
  simp only [Finsupp.add_apply] at h2
  omega

/-- Every monomial of a contributing gate lives inside its selected
support. -/
theorem support_subset_selectedSupport_of_extends (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m i ≤ 1) :
    ∀ gate, C.Extends gate → ∀ m ∈ (C.poly gate).support, m.support ⊆ C.selectedSupport gate := by
  intro gate
  induction gate using C.induction_rank with
  | _ gate ih =>
  intro hext m hm
  rw [selectedSupport_eq]
  split_ifs with h0
  · rw [h0, MvPolynomial.support_zero] at hm
    exact absurd hm (Finset.notMem_empty m)
  · cases hnode : C.node gate with
    | const c =>
        have hc : C.poly gate = MvPolynomial.C c := by
          rw [C.poly_eq gate, hnode]
          rfl
        rw [hc, MvPolynomial.support_C] at hm
        split_ifs at hm with hc0
        · exact absurd hm (Finset.notMem_empty m)
        · rw [mem_singleton] at hm
          subst hm
          simp [ArithNode.selectedVars]
    | var j =>
        have hv : C.poly gate = X j := by
          rw [C.poly_eq gate, hnode]
          rfl
        rw [hv, MvPolynomial.support_X, mem_singleton] at hm
        subst hm
        simp only [ArithNode.selectedVars]
        exact Finsupp.support_single_subset
    | add left right =>
        obtain ⟨hl, hr⟩ := extends_add hmono hnode hext
        have hsupp : (C.poly gate).support =
            (C.poly left).support ∪ (C.poly right).support := by
          rw [C.poly_eq gate, hnode]
          exact support_add_of_nonneg _ _ (C.coeff_nonneg hmono left)
            (C.coeff_nonneg hmono right)
        rw [hsupp] at hm
        simp only [ArithNode.selectedVars]
        rcases Finset.mem_union.mp hm with hm | hm
        · exact (ih left (by rw [hnode]; exact Or.inl rfl) hl m hm).trans
            Finset.subset_union_left
        · exact (ih right (by rw [hnode]; exact Or.inr rfl) hr m hm).trans
            Finset.subset_union_right
    | mul left right =>
        have hprod : C.poly gate = C.poly left * C.poly right := by
          rw [C.poly_eq gate, hnode]
          rfl
        have hl0 : C.poly left ≠ 0 := fun h ↦ h0 (by rw [hprod, h, zero_mul])
        have hr0 : C.poly right ≠ 0 := fun h ↦ h0 (by rw [hprod, h, mul_zero])
        obtain ⟨hl, hr⟩ := extends_mul hmono hnode hl0 hr0 hext
        have hdisj := selectedSupport_disjoint_of_extends hmono hout hnode hext
        simp only [ArithNode.selectedVars, if_pos hdisj]
        rw [hprod] at hm
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp (support_mul _ _ hm)
        subst huv
        refine Finsupp.support_add.trans (Finset.union_subset_union ?_ ?_)
        · exact ih left (by rw [hnode]; exact Or.inl rfl) hl u hu
        · exact ih right (by rw [hnode]; exact Or.inr rfl) hr v hv

end ArithCircuit

/-! ## The padded gate type -/

/-- Gates of the padded translation: the main gate of every circuit gate, two
padding gates per circuit gate, a chain of `N + 1` gates per padding gate and
one for the root, `N` negative literals, and the root. -/
abbrev PadGate (Gate : Type*) (N : ℕ) : Type _ :=
  Gate ⊕ (Gate × Bool) ⊕ (Option (Gate × Bool) × Fin (N + 1)) ⊕ Fin N ⊕ Unit

set_option synthInstance.maxSize 1024 in
/-- Equality on the padded gates: the nested sum exceeds the default instance
size limit, so the instance is named. -/
instance PadGate.instDecidableEq (Gate : Type*) [DecidableEq Gate] (N : ℕ) :
    DecidableEq (PadGate Gate N) := inferInstance

namespace PadGate

variable {Gate : Type*}

/-- The main gate of a circuit gate. -/
abbrev main (g : Gate) : PadGate Gate N := Sum.inl g

/-- The padding gate on one side of a sum. -/
abbrev pad (g : Gate) (b : Bool) : PadGate Gate N := Sum.inr (Sum.inl (g, b))

/-- Position `k` of the chain of a padding gate (`some`) or of the root
(`none`). -/
abbrev chain (c : Option (Gate × Bool)) (k : Fin (N + 1)) : PadGate Gate N :=
  Sum.inr (Sum.inr (Sum.inl (c, k)))

/-- The negative literal of a position. -/
abbrev lit (i : Fin N) : PadGate Gate N := Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))

/-- The root. -/
abbrev root : PadGate Gate N := Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

/-- The node of a padding gate, from the child it pads. -/
def sideNode (g : Gate) (b : Bool) : Option Gate → NNFNode (Fin N) (PadGate Gate N)
  | some c => .conj (main c) (chain (some (g, b)) 0)
  | none => .bot

/-- The node at position `k` of the chain asserting that every position of
`D` is false: a literal for position `k` when it lies in `D`, a pass-through
otherwise, `true` at the end. -/
def chainNode (D : Finset (Fin N)) (c : Option (Gate × Bool)) (k : Fin (N + 1)) :
    NNFNode (Fin N) (PadGate Gate N) :=
  if h : k.1 < N then
    if (⟨k.1, h⟩ : Fin N) ∈ D then
      .conj (lit ⟨k.1, h⟩) (chain c ⟨k.1 + 1, by omega⟩)
    else .disj [chain c ⟨k.1 + 1, by omega⟩]
  else .top

theorem card (Gate : Type*) [Fintype Gate] (N : ℕ) :
    Fintype.card (PadGate Gate N) = Fintype.card Gate * (2 * N + 5) + 2 * N + 2 := by
  simp only [PadGate, Fintype.card_sum, Fintype.card_prod, Fintype.card_option,
    Fintype.card_bool, Fintype.card_fin, Fintype.card_unit]
  ring

end PadGate

namespace ArithNode

variable {Gate : Type*}

/-- The node of a main gate, from the arithmetic node. -/
noncomputable def padNNF (g : Gate) (support : Gate → Finset (Fin N)) :
    ArithNode (Fin N) Gate → NNFNode (Fin N) (PadGate Gate N)
  | const _ => .top
  | var i => .pos i
  | add _ _ => .disj [PadGate.pad g true, PadGate.pad g false]
  | mul left right =>
      if Disjoint (support left) (support right) then
        .conj (PadGate.main left) (PadGate.main right)
      else .bot

end ArithNode

namespace ArithCircuit

variable (C : ArithCircuit (Fin N))

/-- The positions a chain sets to false: those outside the output's
selected support at the root, those of a sum outside the padded child's
support at a padding gate. -/
noncomputable def padSet : Option (C.Gate × Bool) → Finset (Fin N)
  | none => univ \ C.selectedSupport C.output
  | some (g, b) =>
      match (C.node g).addChild b with
      | some c => C.selectedSupport g \ C.selectedSupport c
      | none => ∅

theorem padSet_none : C.padSet none = univ \ C.selectedSupport C.output := rfl

theorem padSet_some {g c : C.Gate} {b : Bool} (hc : (C.node g).addChild b = some c) :
    C.padSet (some (g, b)) = C.selectedSupport g \ C.selectedSupport c := by
  simp only [padSet, hc]

open Classical in
/-- The node of a main gate. -/
noncomputable def mainNode (g : C.Gate) : NNFNode (Fin N) (PadGate C.Gate N) :=
  if C.poly g = 0 then .bot else (C.node g).padNNF g C.selectedSupport

/-- The node table of the padded translation. -/
noncomputable def padNode : PadGate C.Gate N → NNFNode (Fin N) (PadGate C.Gate N)
  | .inl g => C.mainNode g
  | .inr (.inl (g, b)) => PadGate.sideNode g b ((C.node g).addChild b)
  | .inr (.inr (.inl (c, k))) => PadGate.chainNode (C.padSet c) c k
  | .inr (.inr (.inr (.inl i))) => .neg i
  | .inr (.inr (.inr (.inr ()))) => .conj (PadGate.main C.output) (PadGate.chain none 0)

/-- The rank of the padded translation: main gates and their padding sit
above everything below them in the circuit, chains descend with their
position, literals are at the bottom, and the root is on top. -/
def padRank : PadGate C.Gate N → ℕ
  | .inl g => (N + 3) * C.rank g + N + 3
  | .inr (.inl (g, _)) => (N + 3) * C.rank g + N + 2
  | .inr (.inr (.inl (some (g, _), k))) => (N + 3) * C.rank g + (N + 1 - k.1)
  | .inr (.inr (.inl (none, k))) => (N + 3) * C.rank C.output + N + 3 + (N + 1 - k.1)
  | .inr (.inr (.inr (.inl _))) => 0
  | .inr (.inr (.inr (.inr ()))) => (N + 3) * C.rank C.output + 2 * N + 6

theorem rank_mul_le {g c : C.Gate} (h : C.rank c < C.rank g) :
    (N + 3) * C.rank c + (N + 3) ≤ (N + 3) * C.rank g := by
  have := Nat.mul_le_mul_left (N + 3) (Nat.succ_le_of_lt h)
  rwa [Nat.mul_succ] at this

theorem padNode_child_rank (gate child : PadGate C.Gate N)
    (h : (C.padNode gate).IsChild child) : C.padRank child < C.padRank gate := by
  rcases gate with g | ⟨g, b⟩ | ⟨c, k⟩ | i | u
  · change (C.mainNode g).IsChild child at h
    unfold mainNode at h
    split_ifs at h with h0
    · exact absurd h id
    · rcases hnode : C.node g with c | i | ⟨l, r⟩ | ⟨l, r⟩ <;> rw [hnode] at h
      · exact absurd h id
      · exact absurd h id
      · simp only [ArithNode.padNNF, NNFNode.IsChild, List.mem_cons, List.not_mem_nil,
          or_false] at h
        rcases h with rfl | rfl <;> simp only [padRank] <;> omega
      · simp only [ArithNode.padNNF] at h
        split_ifs at h
        · rcases h with rfl | rfl
          · have := C.rank_mul_le (C.child_rank g l (by rw [hnode]; exact Or.inl rfl))
            simp only [padRank]
            omega
          · have := C.rank_mul_le (C.child_rank g r (by rw [hnode]; exact Or.inr rfl))
            simp only [padRank]
            omega
        · exact absurd h id
  · change (PadGate.sideNode g b ((C.node g).addChild b)).IsChild child at h
    rcases hc : (C.node g).addChild b with _ | c <;> rw [hc] at h
    · exact absurd h id
    · rcases h with rfl | rfl
      · have := C.rank_mul_le (C.child_rank g c (ArithNode.addChild_isChild hc))
        simp only [padRank]
        omega
      · simp only [padRank, Fin.val_zero]
        omega
  · change (PadGate.chainNode (C.padSet c) c k).IsChild child at h
    unfold PadGate.chainNode at h
    split_ifs at h with hk hD
    · rcases h with rfl | rfl
      · rcases c with _ | ⟨g, b⟩ <;> simp only [padRank] <;> omega
      · rcases c with _ | ⟨g, b⟩ <;> simp only [padRank] <;> omega
    · simp only [NNFNode.IsChild, List.mem_singleton] at h
      subst h
      rcases c with _ | ⟨g, b⟩ <;> simp only [padRank] <;> omega
    · exact absurd h id
  · exact absurd h id
  · change (NNFNode.conj (PadGate.main C.output) (PadGate.chain none 0)).IsChild child at h
    rcases h with rfl | rfl <;> simp only [padRank, Fin.val_zero] <;> omega

/-- The padded translation as an acyclic node table. -/
noncomputable def padDescription : AcyclicNNFDescription (Fin N) (PadGate C.Gate N) where
  output := PadGate.root
  node := C.padNode
  rank := C.padRank
  child_rank := C.padNode_child_rank

/-- The DNNF read off a monotone circuit with multilinear output. -/
noncomputable def padDNNF : NNFCircuit (Fin N) :=
  C.padDescription.toCircuit

theorem padDNNF_size : C.padDNNF.size = C.size * (2 * N + 5) + 2 * N + 2 := by
  show Fintype.card (PadGate C.Gate N) = _
  rw [PadGate.card]
  rfl

/-! ### Supports -/

theorem padSupport_lit (i : Fin N) : C.padDescription.support (PadGate.lit i) = {i} := by
  rw [AcyclicNNFDescription.support_eq]
  rfl

theorem padSupport_chain (c : Option (C.Gate × Bool)) (k : Fin (N + 1)) :
    C.padDescription.support (PadGate.chain c k) =
      (C.padSet c).filter (fun i ↦ k.1 ≤ i.1) := by
  suffices h : ∀ j, ∀ k : Fin (N + 1), N - k.1 = j →
      C.padDescription.support (PadGate.chain c k) =
        (C.padSet c).filter (fun i ↦ k.1 ≤ i.1) from h _ k rfl
  intro j
  induction j with
  | zero =>
      intro k hk
      have hkN : ¬ k.1 < N := by omega
      rw [AcyclicNNFDescription.support_eq]
      change (PadGate.chainNode (C.padSet c) c k).Support _ = _
      rw [PadGate.chainNode, dif_neg hkN]
      change (∅ : Finset (Fin N)) = _
      symm
      rw [Finset.filter_eq_empty_iff]
      intro i _
      have := i.isLt
      omega
  | succ j ih =>
      intro k hk
      have hkN : k.1 < N := by omega
      rw [AcyclicNNFDescription.support_eq]
      change (PadGate.chainNode (C.padSet c) c k).Support _ = _
      rw [PadGate.chainNode, dif_pos hkN]
      have ih' := ih ⟨k.1 + 1, by omega⟩ (show N - (k.1 + 1) = j by omega)
      rw [filter_le_eq_union_filter_succ _ _ hkN]
      split_ifs with hD
      · simp only [NNFNode.Support]
        rw [padSupport_lit, ih']
      · simp only [NNFNode.Support, List.foldl, Finset.empty_union]
        rw [ih']

theorem padSupport_chain_zero (c : Option (C.Gate × Bool)) :
    C.padDescription.support (PadGate.chain c 0) = C.padSet c := by
  rw [padSupport_chain]
  exact Finset.filter_true_of_mem fun i _ ↦ by simp

theorem padSupport_pad {g c : C.Gate} {b : Bool} (hc : (C.node g).addChild b = some c)
    (ih : C.padDescription.support (PadGate.main c) = C.selectedSupport c) :
    C.padDescription.support (PadGate.pad g b) =
      C.selectedSupport c ∪ (C.selectedSupport g \ C.selectedSupport c) := by
  rw [AcyclicNNFDescription.support_eq]
  change (PadGate.sideNode g b ((C.node g).addChild b)).Support _ = _
  rw [hc]
  simp only [PadGate.sideNode, NNFNode.Support]
  rw [ih, padSupport_chain_zero, C.padSet_some hc]

theorem padSupport_main :
    ∀ g, C.padDescription.support (PadGate.main g) = C.selectedSupport g := by
  intro g
  induction g using C.induction_rank with
  | _ g ih =>
  rw [AcyclicNNFDescription.support_eq]
  change (C.mainNode g).Support _ = _
  unfold mainNode
  split_ifs with h0
  · rw [selectedSupport_eq, if_pos h0]
    rfl
  · have hS : C.selectedSupport g = (C.node g).selectedVars C.selectedSupport := by
      rw [selectedSupport_eq, if_neg h0]
    rcases hnode : C.node g with c | i | ⟨l, r⟩ | ⟨l, r⟩ <;> rw [hnode] at hS
    · rw [hS]
      rfl
    · rw [hS]
      rfl
    · simp only [ArithNode.padNNF, NNFNode.Support, List.foldl, Finset.empty_union]
      have hcl : (C.node g).addChild true = some l := by rw [hnode]; rfl
      have hcr : (C.node g).addChild false = some r := by rw [hnode]; rfl
      rw [C.padSupport_pad hcl (ih l (by rw [hnode]; exact Or.inl rfl)),
        C.padSupport_pad hcr (ih r (by rw [hnode]; exact Or.inr rfl)), hS]
      simp only [ArithNode.selectedVars]
      ext i
      simp only [mem_union, mem_sdiff]
      tauto
    · simp only [ArithNode.padNNF]
      rw [hS]
      simp only [ArithNode.selectedVars]
      split_ifs with hdisj
      · simp only [NNFNode.Support]
        rw [ih l (by rw [hnode]; exact Or.inl rfl), ih r (by rw [hnode]; exact Or.inr rfl)]
      · rfl

/-! ### Decomposability -/

theorem padDNNF_isDNNF : C.padDNNF.IsDNNF := by
  intro gate left right h
  change C.padNode gate = _ at h
  change Disjoint (C.padDescription.support left) (C.padDescription.support right)
  rcases gate with g | ⟨g, b⟩ | ⟨c, k⟩ | i | u
  · change C.mainNode g = _ at h
    unfold mainNode at h
    by_cases h0 : C.poly g = 0
    · rw [if_pos h0] at h
      cases h
    · rw [if_neg h0] at h
      rcases hnode : C.node g with c | i | ⟨l, r⟩ | ⟨l, r⟩ <;> rw [hnode] at h
      · cases h
      · cases h
      · cases h
      · simp only [ArithNode.padNNF] at h
        by_cases hdisj : Disjoint (C.selectedSupport l) (C.selectedSupport r)
        · rw [if_pos hdisj] at h
          cases h
          rw [padSupport_main, padSupport_main]
          exact hdisj
        · rw [if_neg hdisj] at h
          cases h
  · change PadGate.sideNode g b ((C.node g).addChild b) = _ at h
    rcases hc : (C.node g).addChild b with _ | c <;> rw [hc] at h
    · cases h
    · cases h
      rw [padSupport_main, padSupport_chain_zero]
      simp only [padSet, hc]
      exact Finset.disjoint_sdiff
  · change PadGate.chainNode (C.padSet c) c k = _ at h
    unfold PadGate.chainNode at h
    by_cases hk : k.1 < N
    · rw [dif_pos hk] at h
      by_cases hD : (⟨k.1, hk⟩ : Fin N) ∈ C.padSet c
      · rw [if_pos hD] at h
        cases h
        rw [padSupport_lit, padSupport_chain, Finset.disjoint_singleton_left, mem_filter, not_and]
        intro _
        show ¬ (k.1 + 1 ≤ k.1)
        omega
      · rw [if_neg hD] at h
        cases h
    · rw [dif_neg hk] at h
      cases h
  · cases h
  · change NNFNode.conj (PadGate.main C.output) (PadGate.chain none 0) = _ at h
    cases h
    rw [padSupport_main, padSupport_chain_zero, padSet_none]
    exact Finset.disjoint_sdiff

/-! ### Semantics -/

theorem padSemantics_lit (i : Fin N) (x : Fin N → Bool) :
    C.padDescription.semantics (PadGate.lit i) x ↔ x i = false := by
  rw [AcyclicNNFDescription.semantics_eq]
  rfl

theorem padSemantics_chain (c : Option (C.Gate × Bool)) (k : Fin (N + 1)) (x : Fin N → Bool) :
    C.padDescription.semantics (PadGate.chain c k) x ↔
      ∀ i ∈ C.padSet c, k.1 ≤ i.1 → x i = false := by
  suffices h : ∀ j, ∀ k : Fin (N + 1), N - k.1 = j →
      (C.padDescription.semantics (PadGate.chain c k) x ↔
        ∀ i ∈ C.padSet c, k.1 ≤ i.1 → x i = false) from h _ k rfl
  intro j
  induction j with
  | zero =>
      intro k hk
      have hkN : ¬ k.1 < N := by omega
      rw [AcyclicNNFDescription.semantics_eq]
      change (PadGate.chainNode (C.padSet c) c k).Holds x _ ↔ _
      rw [PadGate.chainNode, dif_neg hkN]
      simp only [NNFNode.Holds, true_iff]
      intro i _ hki
      have := i.isLt
      omega
  | succ j ih =>
      intro k hk
      have hkN : k.1 < N := by omega
      rw [AcyclicNNFDescription.semantics_eq]
      change (PadGate.chainNode (C.padSet c) c k).Holds x _ ↔ _
      rw [PadGate.chainNode, dif_pos hkN]
      have ih' := ih ⟨k.1 + 1, by omega⟩ (show N - (k.1 + 1) = j by omega)
      rw [forall_le_iff_and_forall_succ _ _ hkN]
      split_ifs with hD
      · simp only [NNFNode.Holds]
        rw [padSemantics_lit, ih']
        simp [hD]
      · simp only [NNFNode.Holds, List.mem_singleton, exists_eq_left]
        rw [ih']
        simp [hD]

theorem padSemantics_chain_zero (c : Option (C.Gate × Bool)) (x : Fin N → Bool) :
    C.padDescription.semantics (PadGate.chain c 0) x ↔ ∀ i ∈ C.padSet c, x i = false := by
  rw [padSemantics_chain]
  simp

theorem padSemantics_pad {g c : C.Gate} {b : Bool} (hc : (C.node g).addChild b = some c)
    (x : Fin N → Bool) :
    C.padDescription.semantics (PadGate.pad g b) x ↔
      C.padDescription.semantics (PadGate.main c) x ∧
        ∀ i ∈ C.selectedSupport g, i ∉ C.selectedSupport c → x i = false := by
  rw [AcyclicNNFDescription.semantics_eq]
  change (PadGate.sideNode g b ((C.node g).addChild b)).Holds x _ ↔ _
  rw [hc]
  simp only [PadGate.sideNode, NNFNode.Holds]
  rw [padSemantics_chain_zero, C.padSet_some hc]
  simp only [mem_sdiff, and_imp]

variable {C}

/-- The invariant of the translation: a contributing gate is true at `x`
exactly when the monomial selecting `x` inside its selected support occurs
in its polynomial. -/
theorem padSemantics_main (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m i ≤ 1) :
    ∀ g, C.Extends g → ∀ x,
      (C.padDescription.semantics (PadGate.main g) x ↔
        selected x (C.selectedSupport g) ∈ (C.poly g).support) := by
  intro g
  induction g using C.induction_rank with
  | _ g ih =>
  intro hext x
  rw [AcyclicNNFDescription.semantics_eq]
  change (C.mainNode g).Holds x _ ↔ _
  unfold mainNode
  split_ifs with h0
  · rw [h0, MvPolynomial.support_zero]
    simp [NNFNode.Holds]
  · have hS : C.selectedSupport g = (C.node g).selectedVars C.selectedSupport := by
      rw [selectedSupport_eq, if_neg h0]
    rcases hnode : C.node g with c | i | ⟨l, r⟩ | ⟨l, r⟩ <;> rw [hnode] at hS
    · have hc : C.poly g = MvPolynomial.C c := by
        rw [C.poly_eq g, hnode]
        rfl
      have hc0 : c ≠ 0 := fun h ↦ h0 (by rw [hc, h, map_zero])
      rw [hS, hc, MvPolynomial.support_C, if_neg hc0]
      simp [ArithNode.padNNF, ArithNode.selectedVars, NNFNode.Holds, selected_empty]
    · have hv : C.poly g = X i := by
        rw [C.poly_eq g, hnode]
        rfl
      rw [hS, hv, MvPolynomial.support_X, mem_singleton]
      simp only [ArithNode.padNNF, ArithNode.selectedVars, NNFNode.Holds]
      constructor
      · intro hx
        ext j
        rw [selected_apply, Finsupp.single_apply]
        by_cases hj : j = i
        · subst hj
          simp [hx]
        · simp [hj, Ne.symm hj]
      · intro h
        have hi := DFunLike.congr_fun h i
        rw [selected_apply_of_mem (mem_singleton_self i), Finsupp.single_eq_same] at hi
        cases hx : x i
        · rw [hx] at hi
          simp at hi
        · rfl
    · obtain ⟨hl, hr⟩ := extends_add hmono hnode hext
      have hsum : C.poly g = C.poly l + C.poly r := by
        rw [C.poly_eq g, hnode]
        rfl
      have hsupp : (C.poly g).support = (C.poly l).support ∪ (C.poly r).support := by
        rw [hsum]
        exact support_add_of_nonneg _ _ (C.coeff_nonneg hmono l) (C.coeff_nonneg hmono r)
      have hvl := support_subset_selectedSupport_of_extends hmono hout l hl
      have hvr := support_subset_selectedSupport_of_extends hmono hout r hr
      have hsubl : C.selectedSupport l ⊆ C.selectedSupport g := by
        rw [hS]
        exact Finset.subset_union_left
      have hsubr : C.selectedSupport r ⊆ C.selectedSupport g := by
        rw [hS]
        exact Finset.subset_union_right
      simp only [ArithNode.padNNF, NNFNode.Holds, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left]
      have hcl : (C.node g).addChild true = some l := by rw [hnode]; rfl
      have hcr : (C.node g).addChild false = some r := by rw [hnode]; rfl
      rw [C.padSemantics_pad hcl x, C.padSemantics_pad hcr x]
      rw [ih l (by rw [hnode]; exact Or.inl rfl) hl x, ih r (by rw [hnode]; exact Or.inr rfl) hr x,
        hsupp, mem_union, selected_mem_support_iff hsubl hvl, selected_mem_support_iff hsubr hvr]
    · have hprod : C.poly g = C.poly l * C.poly r := by
        rw [C.poly_eq g, hnode]
        rfl
      have hl0 : C.poly l ≠ 0 := fun h ↦ h0 (by rw [hprod, h, zero_mul])
      have hr0 : C.poly r ≠ 0 := fun h ↦ h0 (by rw [hprod, h, mul_zero])
      obtain ⟨hl, hr⟩ := extends_mul hmono hnode hl0 hr0 hext
      have hdisj := selectedSupport_disjoint_of_extends hmono hout hnode hext
      have hvl := support_subset_selectedSupport_of_extends hmono hout l hl
      have hvr := support_subset_selectedSupport_of_extends hmono hout r hr
      rw [hS]
      simp only [ArithNode.padNNF, ArithNode.selectedVars, if_pos hdisj, NNFNode.Holds]
      rw [ih l (by rw [hnode]; exact Or.inl rfl) hl x, ih r (by rw [hnode]; exact Or.inr rfl) hr x,
        hprod]
      exact (selected_mem_support_mul_iff (C.coeff_nonneg hmono l) (C.coeff_nonneg hmono r)
        hdisj hvl hvr).symm

/-- The padded DNNF is true at `x` exactly when the monomial of the positions
set by `x` occurs in the output. -/
theorem padDNNF_computes (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m i ≤ 1) :
    C.padDNNF.Computes fun x ↦ selected x univ ∈ (C.poly C.output).support := by
  intro x
  change C.padDescription.semantics PadGate.root x ↔ _
  rw [AcyclicNNFDescription.semantics_eq]
  change (NNFNode.conj (PadGate.main C.output) (PadGate.chain none 0)).Holds x _ ↔ _
  simp only [NNFNode.Holds]
  rw [padSemantics_main hmono hout _ C.extends_output x, padSemantics_chain_zero, padSet_none,
    selected_mem_support_iff (Finset.subset_univ _)
      (support_subset_selectedSupport_of_extends hmono hout _ C.extends_output)]
  simp only [mem_sdiff, mem_univ, true_and, true_implies]

end ArithCircuit

end unpaired

end DDNNFNegation
