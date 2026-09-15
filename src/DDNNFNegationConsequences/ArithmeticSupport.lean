import DDNNFNegationConsequences.ArithmeticCircuits
import DDNNFNegationConsequences.AcyclicCircuitBuilder

/-!
# Pruning the support translation of a monotone circuit

Assume the output monomials use at most one indicator from each paired
position. Every monomial that contributes to the output inherits this
property. Thus contributing nonzero products have disjoint positions.

The translation makes zero gates and products with overlapping positions
false. It is a DNNF by construction and preserves positivity at gates whose
monomials extend to output monomials. In particular it computes the output
polynomial's Boolean support, with the same number of nodes.
-/

namespace DDNNFNegation

open MvPolynomial Finset

section nonneg

variable {V : Type*} [DecidableEq V]

/-- Without cancellation the monomials of a sum are those of its terms. -/
theorem support_add_of_nonneg (p q : MvPolynomial V ℝ)
    (hp : ∀ m, 0 ≤ coeff m p) (hq : ∀ m, 0 ≤ coeff m q) :
    (p + q).support = p.support ∪ q.support := by
  ext m
  simp only [mem_support_iff, coeff_add, mem_union]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2, add_zero] at h
    exact h rfl
  · rintro (h | h)
    · have := lt_of_le_of_ne (hp m) (Ne.symm h)
      linarith [hq m]
    · have := lt_of_le_of_ne (hq m) (Ne.symm h)
      linarith [hp m]

/-- Without cancellation the product of two monomials of the factors is a
monomial of the product. -/
theorem add_mem_support_mul_of_nonneg (p q : MvPolynomial V ℝ)
    (hp : ∀ m, 0 ≤ coeff m p) (hq : ∀ m, 0 ≤ coeff m q)
    {u v : V →₀ ℕ} (hu : u ∈ p.support) (hv : v ∈ q.support) :
    u + v ∈ (p * q).support := by
  rw [mem_support_iff, coeff_mul]
  apply ne_of_gt
  have hpos : 0 < coeff u p * coeff v q :=
    mul_pos (lt_of_le_of_ne (hp u) (Ne.symm (mem_support_iff.mp hu)))
      (lt_of_le_of_ne (hq v) (Ne.symm (mem_support_iff.mp hv)))
  refine lt_of_lt_of_le hpos ?_
  refine Finset.single_le_sum
    (f := fun x : (V →₀ ℕ) × (V →₀ ℕ) ↦ coeff x.1 p * coeff x.2 q)
    (fun x _ ↦ mul_nonneg (hp x.1) (hq x.2)) (a := (u, v)) ?_
  simp

omit [DecidableEq V] in
/-- A nonzero polynomial has a monomial. -/
theorem exists_mem_support_of_ne_zero {p : MvPolynomial V ℝ} (hp : p ≠ 0) :
    ∃ m, m ∈ p.support := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  exact ⟨d, mem_support_iff.mpr hd⟩

end nonneg

namespace ArithCircuit

section extendsMonomials

variable {V : Type*} [DecidableEq V] (C : ArithCircuit V)

/-! ### Monomials that extend to the output -/

/-- Every monomial of the gate divides a monomial of the output. -/
def Extends (gate : C.Gate) : Prop :=
  ∀ m ∈ (C.poly gate).support, ∃ m' ∈ (C.poly C.output).support, m ≤ m'

theorem extends_output : C.Extends C.output :=
  fun m hm ↦ ⟨m, hm, le_rfl⟩

variable {C}

theorem extends_add (hmono : C.IsMonotone) {gate left right : C.Gate}
    (hnode : C.node gate = .add left right) (h : C.Extends gate) :
    C.Extends left ∧ C.Extends right := by
  have hsupp : (C.poly gate).support = (C.poly left).support ∪ (C.poly right).support := by
    rw [C.poly_eq gate, hnode]
    exact support_add_of_nonneg _ _ (C.coeff_nonneg hmono left) (C.coeff_nonneg hmono right)
  constructor
  · intro m hm
    exact h m (hsupp ▸ Finset.mem_union_left _ hm)
  · intro m hm
    exact h m (hsupp ▸ Finset.mem_union_right _ hm)

theorem extends_mul (hmono : C.IsMonotone) {gate left right : C.Gate}
    (hnode : C.node gate = .mul left right) (hl : C.poly left ≠ 0) (hr : C.poly right ≠ 0)
    (h : C.Extends gate) : C.Extends left ∧ C.Extends right := by
  have hprod : C.poly gate = C.poly left * C.poly right := by
    rw [C.poly_eq gate, hnode]
    rfl
  obtain ⟨u, hu⟩ := exists_mem_support_of_ne_zero hl
  obtain ⟨v, hv⟩ := exists_mem_support_of_ne_zero hr
  constructor
  · intro m hm
    have hmv : m + v ∈ (C.poly gate).support := by
      rw [hprod]
      exact add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
        (C.coeff_nonneg hmono right) hm hv
    obtain ⟨m', hm', hle⟩ := h (m + v) hmv
    exact ⟨m', hm', le_trans le_self_add hle⟩
  · intro m hm
    have hum : u + m ∈ (C.poly gate).support := by
      rw [hprod]
      exact add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
        (C.coeff_nonneg hmono right) hu hm
    obtain ⟨m', hm', hle⟩ := h (u + m) hum
    exact ⟨m', hm', le_trans le_add_self hle⟩

end extendsMonomials

end ArithCircuit

section paired

variable {N : ℕ}

/-- The positions of the indeterminates occurring in a polynomial. -/
noncomputable def polyPositions (p : MvPolynomial (Fin N × Bool) ℝ) : Finset (Fin N) :=
  positions p.vars

theorem mem_polyPositions (p : MvPolynomial (Fin N × Bool) ℝ) (i : Fin N) :
    i ∈ polyPositions p ↔ ∃ d ∈ p.support, ∃ b, d (i, b) ≠ 0 := by
  simp only [polyPositions, positions, mem_image, mem_vars_iff_mem_support,
    Finsupp.mem_support_iff]
  constructor
  · rintro ⟨⟨j, b⟩, ⟨d, hd, hdj⟩, rfl⟩
    exact ⟨d, hd, b, hdj⟩
  · rintro ⟨d, hd, b, hdi⟩
    exact ⟨(i, b), ⟨d, hd, hdi⟩, rfl⟩

namespace ArithNode

variable {Gate : Type*}

/-- Supports of the pruned translation, from the children's: a product with
overlapping factors is dropped. -/
def prunedVars (child : Gate → Finset (Fin N)) :
    ArithNode (Fin N × Bool) Gate → Finset (Fin N)
  | const _ => ∅
  | var (i, _) => {i}
  | add left right => child left ∪ child right
  | mul left right =>
      if Disjoint (child left) (child right) then child left ∪ child right else ∅

theorem prunedVars_congr (node : ArithNode (Fin N × Bool) Gate)
    (c₁ c₂ : Gate → Finset (Fin N))
    (h : ∀ child, node.IsChild child → c₁ child = c₂ child) :
    node.prunedVars c₁ = node.prunedVars c₂ := by
  cases node with
  | const c => rfl
  | var x => rfl
  | add left right =>
      simp only [prunedVars]
      rw [h left (Or.inl rfl), h right (Or.inr rfl)]
  | mul left right =>
      simp only [prunedVars]
      rw [h left (Or.inl rfl), h right (Or.inr rfl)]

/-- The Boolean node of the pruned translation: as `translateNode`, except
that a product with overlapping factors becomes `false`. -/
noncomputable def prunedNNF (support : Gate → Finset (Fin N)) :
    ArithNode (Fin N × Bool) Gate → NNFNode (Fin N) Gate
  | const _ => .top
  | var (i, b) => if b then .pos i else .neg i
  | add left right => .disj [left, right]
  | mul left right =>
      if Disjoint (support left) (support right) then .conj left right else .bot

theorem prunedNNF_isChild (support : Gate → Finset (Fin N))
    (node : ArithNode (Fin N × Bool) Gate) (child : Gate)
    (h : (node.prunedNNF support).IsChild child) : node.IsChild child := by
  cases node with
  | const c => exact absurd h id
  | var x =>
      obtain ⟨i, b⟩ := x
      simp only [prunedNNF] at h
      cases b <;> simp [NNFNode.IsChild] at h
  | add left right =>
      simp only [prunedNNF, NNFNode.IsChild, List.mem_cons, List.not_mem_nil,
        or_false] at h
      exact h
  | mul left right =>
      simp only [prunedNNF] at h
      split_ifs at h
      · exact h
      · exact absurd h id

end ArithNode

namespace ArithCircuit

open Classical in
/-- The syntactic support of the pruned translation. -/
noncomputable def prunedSupport (C : ArithCircuit (Fin N × Bool)) (gate : C.Gate) :
    Finset (Fin N) :=
  if C.poly gate = 0 then ∅ else
    (C.node gate).prunedVars fun child ↦
      if _h : (C.node gate).IsChild child then C.prunedSupport child else ∅
termination_by C.rank gate
decreasing_by exact C.child_rank gate child _h

variable (C : ArithCircuit (Fin N × Bool))

open Classical in
theorem prunedSupport_eq (gate : C.Gate) :
    C.prunedSupport gate =
      if C.poly gate = 0 then ∅ else (C.node gate).prunedVars C.prunedSupport := by
  rw [prunedSupport]
  split_ifs
  · rfl
  · apply ArithNode.prunedVars_congr
    intro child hchild
    simp [hchild]

open Classical in
/-- The node table of the pruned translation. -/
noncomputable def prunedNode (gate : C.Gate) : NNFNode (Fin N) C.Gate :=
  if C.poly gate = 0 then .bot else (C.node gate).prunedNNF C.prunedSupport

theorem prunedNode_isChild (gate child : C.Gate)
    (h : (C.prunedNode gate).IsChild child) : (C.node gate).IsChild child := by
  unfold prunedNode at h
  split_ifs at h
  · exact absurd h id
  · exact ArithNode.prunedNNF_isChild _ _ _ h

/-- The pruned translation as an acyclic node table. -/
noncomputable def prunedDescription : AcyclicNNFDescription (Fin N) C.Gate where
  output := C.output
  node := C.prunedNode
  rank := C.rank
  child_rank := fun gate child h ↦ C.child_rank gate child (C.prunedNode_isChild gate child h)

/-- The DNNF read off an arbitrary monotone circuit after pruning. -/
noncomputable def prunedDNNF : NNFCircuit (Fin N) :=
  C.prunedDescription.toCircuit

@[simp] theorem prunedDNNF_size : C.prunedDNNF.size = C.size := rfl

theorem prunedDescription_support (gate : C.Gate) :
    C.prunedDescription.support gate = C.prunedSupport gate := by
  induction gate using C.induction_rank with
  | _ gate ih =>
  rw [AcyclicNNFDescription.support_eq, prunedSupport_eq]
  change (C.prunedNode gate).Support _ = _
  unfold prunedNode
  split_ifs with h0
  · rfl
  · cases hnode : C.node gate with
    | const c => rfl
    | var v =>
        obtain ⟨i, b⟩ := v
        cases b <;> rfl
    | add left right =>
        simp only [ArithNode.prunedNNF, ArithNode.prunedVars, NNFNode.Support, List.foldl,
          Finset.empty_union]
        rw [ih left (by rw [hnode]; exact Or.inl rfl), ih right (by rw [hnode]; exact Or.inr rfl)]
    | mul left right =>
        simp only [ArithNode.prunedNNF, ArithNode.prunedVars]
        split_ifs with hdisj
        · simp only [NNFNode.Support]
          rw [ih left (by rw [hnode]; exact Or.inl rfl),
            ih right (by rw [hnode]; exact Or.inr rfl)]
        · rfl

theorem prunedDescription_conj_disjoint (gate left right : C.Gate)
    (h : C.prunedNode gate = .conj left right) :
    Disjoint (C.prunedDescription.support left) (C.prunedDescription.support right) := by
  rw [prunedDescription_support, prunedDescription_support]
  unfold prunedNode at h
  split_ifs at h with h0
  cases hnode : C.node gate with
  | const c =>
      rw [hnode] at h
      cases h
  | var v =>
      obtain ⟨i, b⟩ := v
      rw [hnode] at h
      cases b <;> simp [ArithNode.prunedNNF] at h
  | add l r =>
      rw [hnode] at h
      cases h
  | mul l r =>
      rw [hnode] at h
      simp only [ArithNode.prunedNNF] at h
      split_ifs at h with hdisj
      cases h
      exact hdisj

theorem prunedDNNF_isDNNF : C.prunedDNNF.IsDNNF := by
  intro gate left right h
  exact C.prunedDescription_conj_disjoint gate left right h

variable {C}

/-- The pruned support of a gate lies within the positions of its
polynomial. -/
theorem prunedSupport_subset (hmono : C.IsMonotone) :
    ∀ gate, C.prunedSupport gate ⊆ polyPositions (C.poly gate) := by
  intro gate
  induction gate using C.induction_rank with
  | _ gate ih =>
  rw [prunedSupport_eq]
  split_ifs with h0
  · exact Finset.empty_subset _
  · cases hnode : C.node gate with
    | const c => exact Finset.empty_subset _
    | var v =>
        obtain ⟨i, b⟩ := v
        intro j hj
        simp only [ArithNode.prunedVars, mem_singleton] at hj
        subst hj
        rw [mem_polyPositions, C.poly_eq gate, hnode]
        refine ⟨Finsupp.single (j, b) 1, ?_, b, ?_⟩
        · simp [ArithNode.eval, MvPolynomial.support_X]
        · simp
    | add left right =>
        have hl := ih left (by rw [hnode]; exact Or.inl rfl)
        have hr := ih right (by rw [hnode]; exact Or.inr rfl)
        have hsupp : (C.poly gate).support = (C.poly left).support ∪ (C.poly right).support := by
          rw [C.poly_eq gate, hnode]
          exact support_add_of_nonneg _ _ (C.coeff_nonneg hmono left)
            (C.coeff_nonneg hmono right)
        simp only [ArithNode.prunedVars]
        intro j hj
        rw [mem_polyPositions, hsupp]
        rcases Finset.mem_union.mp hj with hj | hj
        · obtain ⟨d, hd, b, hdb⟩ := (mem_polyPositions _ _).mp (hl hj)
          exact ⟨d, Finset.mem_union_left _ hd, b, hdb⟩
        · obtain ⟨d, hd, b, hdb⟩ := (mem_polyPositions _ _).mp (hr hj)
          exact ⟨d, Finset.mem_union_right _ hd, b, hdb⟩
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
        simp only [ArithNode.prunedVars]
        split_ifs with hdisj
        · intro j hj
          rw [mem_polyPositions, hprod]
          rcases Finset.mem_union.mp hj with hj | hj
          · obtain ⟨d, hd, b, hdb⟩ := (mem_polyPositions _ _).mp (hl hj)
            refine ⟨d + v, add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
              (C.coeff_nonneg hmono right) hd hv, b, ?_⟩
            simp only [Finsupp.add_apply]
            omega
          · obtain ⟨d, hd, b, hdb⟩ := (mem_polyPositions _ _).mp (hr hj)
            refine ⟨u + d, add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
              (C.coeff_nonneg hmono right) hu hd, b, ?_⟩
            simp only [Finsupp.add_apply]
            omega
        · exact Finset.empty_subset _

/-- At a contributing product of a circuit whose output monomials carry at
most one indicator per position, the two factors have disjoint pruned
supports: otherwise a monomial with two indicators at a common position
would extend to an output monomial. -/
theorem prunedSupport_disjoint_of_extends (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m (i, true) + m (i, false) ≤ 1)
    {gate left right : C.Gate} (hnode : C.node gate = .mul left right)
    (h : C.Extends gate) :
    Disjoint (C.prunedSupport left) (C.prunedSupport right) := by
  have hprod : C.poly gate = C.poly left * C.poly right := by
    rw [C.poly_eq gate, hnode]
    rfl
  by_contra hnd
  obtain ⟨i, hil, hir⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨d, hd, b₁, hdb⟩ :=
    (mem_polyPositions _ _).mp (prunedSupport_subset hmono left hil)
  obtain ⟨d', hd', b₂, hdb'⟩ :=
    (mem_polyPositions _ _).mp (prunedSupport_subset hmono right hir)
  have hmem : d + d' ∈ (C.poly gate).support := by
    rw [hprod]
    exact add_mem_support_mul_of_nonneg _ _ (C.coeff_nonneg hmono left)
      (C.coeff_nonneg hmono right) hd hd'
  obtain ⟨m', hm', hle⟩ := h (d + d') hmem
  have h1 := hout m' hm' i
  have ht : (d + d') (i, true) ≤ m' (i, true) := hle (i, true)
  have hf : (d + d') (i, false) ≤ m' (i, false) := hle (i, false)
  simp only [Finsupp.add_apply] at ht hf
  cases b₁ <;> cases b₂ <;> omega

/-- At every contributing gate the pruned translation is true at a Boolean
point exactly when the gate's polynomial is positive there. -/
theorem prunedSemantics_of_extends (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m (i, true) + m (i, false) ≤ 1) :
    ∀ gate, C.Extends gate → ∀ x,
      (C.prunedDescription.semantics gate x ↔
        0 < MvPolynomial.eval (boolPoint x) (C.poly gate)) := by
  intro gate
  induction gate using C.induction_rank with
  | _ gate ih =>
  intro hext x
  have hnn := C.eval_nonneg hmono (boolPoint x) (boolPoint_nonneg x)
  rw [AcyclicNNFDescription.semantics_eq]
  change (C.prunedNode gate).Holds x _ ↔ _
  unfold prunedNode
  split_ifs with h0
  · rw [h0, map_zero]
    simp [NNFNode.Holds]
  · cases hnode : C.node gate with
    | const c =>
        have hc : C.poly gate = MvPolynomial.C c := by
          rw [C.poly_eq gate, hnode]
          rfl
        rw [hc, eval_C]
        have hc0 : c ≠ 0 := fun h ↦ h0 (by rw [hc, h, map_zero])
        simp only [ArithNode.prunedNNF, NNFNode.Holds, true_iff]
        exact lt_of_le_of_ne (hmono gate c hnode) (Ne.symm hc0)
    | var v =>
        obtain ⟨i, b⟩ := v
        have hv : C.poly gate = X (i, b) := by
          rw [C.poly_eq gate, hnode]
          rfl
        rw [hv, eval_X]
        simp only [ArithNode.prunedNNF, boolPoint]
        cases b <;> cases hx : x i <;> simp [NNFNode.Holds, hx]
    | add left right =>
        obtain ⟨hl, hr⟩ := extends_add hmono hnode hext
        have hsum : C.poly gate = C.poly left + C.poly right := by
          rw [C.poly_eq gate, hnode]
          rfl
        rw [hsum, map_add]
        simp only [ArithNode.prunedNNF, NNFNode.Holds, List.mem_cons, List.not_mem_nil,
          or_false, exists_eq_or_imp, exists_eq_left]
        rw [ih left (by rw [hnode]; exact Or.inl rfl) hl x,
          ih right (by rw [hnode]; exact Or.inr rfl) hr x]
        exact (pos_add_iff_of_nonneg (hnn left) (hnn right)).symm
    | mul left right =>
        have hprod : C.poly gate = C.poly left * C.poly right := by
          rw [C.poly_eq gate, hnode]
          rfl
        have hl0 : C.poly left ≠ 0 := fun h ↦ h0 (by rw [hprod, h, zero_mul])
        have hr0 : C.poly right ≠ 0 := fun h ↦ h0 (by rw [hprod, h, mul_zero])
        obtain ⟨hl, hr⟩ := extends_mul hmono hnode hl0 hr0 hext
        have hdisj := prunedSupport_disjoint_of_extends hmono hout hnode hext
        simp only [ArithNode.prunedNNF, hdisj, ↓reduceIte, NNFNode.Holds]
        rw [hprod, map_mul, ih left (by rw [hnode]; exact Or.inl rfl) hl x,
          ih right (by rw [hnode]; exact Or.inr rfl) hr x]
        exact (pos_mul_iff_of_nonneg (hnn left) (hnn right)).symm

/-- The pruned DNNF computes the support of the output on the Boolean
points. -/
theorem prunedDNNF_computes (hmono : C.IsMonotone)
    (hout : ∀ m ∈ (C.poly C.output).support, ∀ i, m (i, true) + m (i, false) ≤ 1)
    (f : (Fin N → Bool) → Prop) (h : ∀ x, 0 < C.boolValue x ↔ f x) :
    C.prunedDNNF.Computes f := by
  intro x
  change C.prunedDescription.semantics C.output x ↔ f x
  rw [prunedSemantics_of_extends hmono hout C.output C.extends_output x]
  exact h x

end ArithCircuit

end paired

end DDNNFNegation
