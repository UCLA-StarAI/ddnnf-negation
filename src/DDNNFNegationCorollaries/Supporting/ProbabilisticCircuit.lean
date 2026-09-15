import DDNNFNegation
import DDNNFNegationCorollaries.Supporting.AcyclicCircuitBuilder

/-!
# Nonnegative decomposable probabilistic circuits

Circuits have univariate leaves, constants, sums, products, and constant
scalings. Separate predicates require nonnegative values at leaves and
constants and disjoint scopes at products. The support translation yields
a DNNF for positivity with three times as many gates.

`forget` replaces hidden-variable leaves by constants. Its value is
positive exactly when some hidden assignment makes the original value
positive; decomposability allows the witnesses at products to combine.
-/

namespace DDNNFNegation

open Finset

/-- One node of a probabilistic circuit. -/
inductive PCNode (V Gate : Type*) where
  | leaf (v : V) (h : Bool → ℝ)
  | const (c : ℝ)
  | scale (c : ℝ) (child : Gate)
  | add (left right : Gate)
  | mul (left right : Gate)

namespace PCNode

variable {V Gate : Type*}

/-- The value at a node, given the values of the children. -/
def eval (child : Gate → ℝ) (x : V → Bool) : PCNode V Gate → ℝ
  | leaf v h => h (x v)
  | const c => c
  | scale c g => c * child g
  | add l r => child l + child r
  | mul l r => child l * child r

/-- The variables below a node, given those of the children. -/
def Scope [DecidableEq V] (child : Gate → Finset V) : PCNode V Gate → Finset V
  | leaf v _ => {v}
  | const _ => ∅
  | scale _ g => child g
  | add l r => child l ∪ child r
  | mul l r => child l ∪ child r

/-- The child relation. -/
def IsChild (c : Gate) : PCNode V Gate → Prop
  | scale _ g => c = g
  | add l r => c = l ∨ c = r
  | mul l r => c = l ∨ c = r
  | _ => False

/-- Nonnegative leaf functions, constants and scale factors. -/
def IsNonneg : PCNode V Gate → Prop
  | leaf _ h => ∀ b, 0 ≤ h b
  | const c => 0 ≤ c
  | scale c _ => 0 ≤ c
  | _ => True

theorem eval_congr {f g : Gate → ℝ} (x : V → Bool) (node : PCNode V Gate)
    (h : ∀ c, node.IsChild c → f c = g c) : node.eval f x = node.eval g x := by
  cases node with
  | scale c child => simp only [eval]; rw [h child rfl]
  | add l r => simp only [eval]; rw [h l (Or.inl rfl), h r (Or.inr rfl)]
  | mul l r => simp only [eval]; rw [h l (Or.inl rfl), h r (Or.inr rfl)]
  | _ => rfl

theorem scope_congr [DecidableEq V] {f g : Gate → Finset V} (node : PCNode V Gate)
    (h : ∀ c, node.IsChild c → f c = g c) : node.Scope f = node.Scope g := by
  cases node with
  | scale c child => simp only [Scope]; rw [h child rfl]
  | add l r => simp only [Scope]; rw [h l (Or.inl rfl), h r (Or.inr rfl)]
  | mul l r => simp only [Scope]; rw [h l (Or.inl rfl), h r (Or.inr rfl)]
  | _ => rfl

end PCNode

/-- A finite acyclic probabilistic circuit: gates, an output, a node table
and a rank certifying acyclicity. -/
structure ProbCircuit (V : Type*) where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  node : Gate → PCNode V Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child, (node gate).IsChild child → rank child < rank gate

namespace ProbCircuit

variable {V : Type*} [DecidableEq V]

instance (P : ProbCircuit V) : Fintype P.Gate := P.gateFintype

instance (P : ProbCircuit V) : DecidableEq P.Gate := P.gateDecidableEq

noncomputable local instance {Gate : Type*} (node : PCNode V Gate) (child : Gate) :
    Decidable (node.IsChild child) := Classical.propDecidable _

variable (P : ProbCircuit V)

/-- The value of a gate on an assignment. -/
noncomputable def value (P : ProbCircuit V) (gate : P.Gate) (x : V → Bool) : ℝ :=
  (P.node gate).eval (fun child =>
    if _h : (P.node gate).IsChild child then value P child x else 0) x
termination_by P.rank gate
decreasing_by exact P.child_rank gate child _h

omit [DecidableEq V] in
theorem value_eq (gate : P.Gate) (x : V → Bool) :
    P.value gate x = (P.node gate).eval (fun child => P.value child x) x := by
  rw [value]
  apply PCNode.eval_congr
  intro c hc
  simp [hc]

/-- The syntactic scope: variables mentioned at or below a gate. -/
noncomputable def scope (P : ProbCircuit V) (gate : P.Gate) : Finset V :=
  (P.node gate).Scope fun child =>
    if _h : (P.node gate).IsChild child then scope P child else ∅
termination_by P.rank gate
decreasing_by exact P.child_rank gate child _h

theorem scope_eq (gate : P.Gate) : P.scope gate = (P.node gate).Scope P.scope := by
  rw [scope]
  apply PCNode.scope_congr
  intro c hc
  simp [hc]

/-- Number of gates. -/
def size : ℕ := Fintype.card P.Gate

/-- Every leaf function, constant and scale factor is nonnegative. -/
def IsNonneg : Prop := ∀ gate, (P.node gate).IsNonneg

/-- The two factors of every product depend on disjoint variables. -/
def IsDecomposable : Prop :=
  ∀ gate left right, P.node gate = .mul left right → Disjoint (P.scope left) (P.scope right)

omit [DecidableEq V] in
theorem induction_rank {Q : P.Gate → Prop}
    (h : ∀ gate, (∀ child, (P.node gate).IsChild child → Q child) → Q gate) : ∀ gate, Q gate := by
  intro gate
  induction hr : P.rank gate using Nat.strong_induction_on generalizing gate with
  | _ r ih =>
  exact h gate fun child hchild => ih _ (hr ▸ P.child_rank gate child hchild) child rfl

omit [DecidableEq V] in
theorem value_nonneg (hnn : P.IsNonneg) (gate : P.Gate) (x : V → Bool) : 0 ≤ P.value gate x := by
  induction gate using P.induction_rank with
  | _ gate ih =>
  rw [value_eq]
  have hnode := hnn gate
  cases hg : P.node gate with
  | leaf v h => rw [hg] at hnode; exact hnode (x v)
  | const c => rw [hg] at hnode; exact hnode
  | scale c child =>
    rw [hg] at hnode
    exact mul_nonneg hnode (ih child (by rw [hg]; rfl))
  | add l r =>
    exact add_nonneg (ih l (by rw [hg]; exact Or.inl rfl)) (ih r (by rw [hg]; exact Or.inr rfl))
  | mul l r =>
    exact mul_nonneg (ih l (by rw [hg]; exact Or.inl rfl)) (ih r (by rw [hg]; exact Or.inr rfl))

/-- The value depends only on the scope. -/
theorem value_congr_of_eqOn_scope (gate : P.Gate) (x y : V → Bool)
    (hxy : ∀ v ∈ P.scope gate, x v = y v) : P.value gate x = P.value gate y := by
  induction gate using P.induction_rank with
  | _ gate ih =>
  rw [value_eq, value_eq]
  have hscope := P.scope_eq gate
  cases hg : P.node gate with
  | leaf v h =>
    rw [hg] at hscope
    simp only [PCNode.eval]
    rw [hxy v (by rw [hscope]; simp [PCNode.Scope])]
  | const c => rfl
  | scale c child =>
    rw [hg] at hscope
    simp only [PCNode.eval]
    rw [ih child (by rw [hg]; rfl) (fun v hv => hxy v (by rw [hscope]; exact hv))]
  | add l r =>
    rw [hg] at hscope
    simp only [PCNode.eval]
    rw [ih l (by rw [hg]; exact Or.inl rfl)
        (fun v hv => hxy v (by rw [hscope]; exact Finset.mem_union_left _ hv)),
      ih r (by rw [hg]; exact Or.inr rfl)
        (fun v hv => hxy v (by rw [hscope]; exact Finset.mem_union_right _ hv))]
  | mul l r =>
    rw [hg] at hscope
    simp only [PCNode.eval]
    rw [ih l (by rw [hg]; exact Or.inl rfl)
        (fun v hv => hxy v (by rw [hscope]; exact Finset.mem_union_left _ hv)),
      ih r (by rw [hg]; exact Or.inr rfl)
        (fun v hv => hxy v (by rw [hscope]; exact Finset.mem_union_right _ hv))]

/-! ## The support translation -/

section Support

variable {N : ℕ} (P : ProbCircuit (Fin N))

/-- The gates of the support DNNF: one per circuit gate, and two literal
gates per circuit gate (used at the leaves). -/
abbrev SupportGate := P.Gate ⊕ (P.Gate × Bool)

/-- The Boolean node of a circuit gate. -/
noncomputable def supportNodeOf (gate : P.Gate) : PCNode (Fin N) P.Gate → NNFNode (Fin N) P.SupportGate
  | .leaf _ _ => .disj [.inr (gate, false), .inr (gate, true)]
  | .const c => if 0 < c then .top else .bot
  | .scale c child => if 0 < c then .disj [.inl child] else .bot
  | .add l r => .disj [.inl l, .inl r]
  | .mul l r => .conj (.inl l) (.inl r)

/-- The literal gate of a leaf. -/
noncomputable def literalNodeOf (b : Bool) : PCNode (Fin N) P.Gate → NNFNode (Fin N) P.SupportGate
  | .leaf v h => if 0 < h b then (if b then .pos v else .neg v) else .bot
  | _ => .bot

noncomputable def supportNode : P.SupportGate → NNFNode (Fin N) P.SupportGate
  | .inl gate => P.supportNodeOf gate (P.node gate)
  | .inr (gate, b) => P.literalNodeOf b (P.node gate)

def supportRank : P.SupportGate → ℕ
  | .inl gate => 2 * P.rank gate + 1
  | .inr (gate, _) => 2 * P.rank gate

theorem literalNodeOf_isChild (b : Bool) (node : PCNode (Fin N) P.Gate) (c : P.SupportGate)
    (h : (P.literalNodeOf b node).IsChild c) : False := by
  cases node with
  | leaf v hf =>
    simp only [literalNodeOf] at h
    split_ifs at h <;> exact h
  | _ => exact h

theorem supportNodeOf_isChild (gate : P.Gate) (node : PCNode (Fin N) P.Gate) (c : P.SupportGate)
    (h : (P.supportNodeOf gate node).IsChild c) :
    (∃ b, c = .inr (gate, b)) ∨ ∃ child, c = .inl child ∧ node.IsChild child := by
  cases node with
  | leaf v hf =>
    simp only [supportNodeOf, NNFNode.IsChild, List.mem_cons, List.not_mem_nil, or_false] at h
    left
    rcases h with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  | const c' =>
    simp only [supportNodeOf] at h
    split_ifs at h <;> exact h.elim
  | scale c' child =>
    simp only [supportNodeOf] at h
    split_ifs at h
    · simp only [NNFNode.IsChild, List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr ⟨child, h, rfl⟩
    · exact h.elim
  | add l r =>
    simp only [supportNodeOf, NNFNode.IsChild, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inr ⟨l, rfl, Or.inl rfl⟩
    · exact Or.inr ⟨r, rfl, Or.inr rfl⟩
  | mul l r =>
    simp only [supportNodeOf, NNFNode.IsChild] at h
    rcases h with rfl | rfl
    · exact Or.inr ⟨l, rfl, Or.inl rfl⟩
    · exact Or.inr ⟨r, rfl, Or.inr rfl⟩

theorem supportRank_child (gate child : P.SupportGate)
    (h : (P.supportNode gate).IsChild child) : P.supportRank child < P.supportRank gate := by
  cases gate with
  | inl g =>
    rcases P.supportNodeOf_isChild g (P.node g) child h with ⟨b, rfl⟩ | ⟨c, rfl, hc⟩
    · simp [supportRank]
    · simp only [supportRank]
      have := P.child_rank g c hc
      omega
  | inr gb =>
    obtain ⟨g, b⟩ := gb
    exact (P.literalNodeOf_isChild b (P.node g) child h).elim

/-- The support DNNF as an acyclic description. -/
noncomputable def supportDescription : AcyclicNNFDescription (Fin N) P.SupportGate where
  output := .inl P.output
  node := P.supportNode
  rank := P.supportRank
  child_rank := P.supportRank_child

/-- The support DNNF of a probabilistic circuit. -/
noncomputable def toDNNF : NNFCircuit (Fin N) := P.supportDescription.toCircuit

theorem toDNNF_size : P.toDNNF.size = 3 * P.size := by
  show Fintype.card P.SupportGate = 3 * Fintype.card P.Gate
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  ring

theorem supportDescription_node : P.supportDescription.node = P.supportNode := rfl

theorem toDNNF_output : P.toDNNF.output = .inl P.output := rfl

/-- The literal gates are true exactly when the leaf's function is positive
at the value the assignment gives the leaf's variable, and that value is
the gate's polarity. -/
theorem toDNNF_semantics_inr (gate : P.Gate) (b : Bool) (x : Fin N → Bool) :
    P.supportDescription.semantics (.inr (gate, b)) x ↔
      ∃ v h, P.node gate = .leaf v h ∧ 0 < h b ∧ x v = b := by
  rw [P.supportDescription.semantics_eq, supportDescription_node]
  simp only [supportNode]
  cases hg : P.node gate with
  | leaf v h =>
    simp only [literalNodeOf]
    by_cases hpos : 0 < h b
    · rw [if_pos hpos]
      have key : ((if b then NNFNode.pos v else NNFNode.neg v : NNFNode (Fin N) P.SupportGate).Holds x
          fun c => P.supportDescription.semantics c x) ↔ x v = b := by
        cases b <;> simp [NNFNode.Holds]
      rw [key]
      constructor
      · intro hx; exact ⟨v, h, rfl, hpos, hx⟩
      · rintro ⟨v', h', hvh, _, hx⟩
        cases hvh; exact hx
    · rw [if_neg hpos]
      simp only [NNFNode.Holds, false_iff, not_exists, not_and]
      intro v' h' hvh hpos'
      cases hvh; exact absurd hpos' hpos
  | const c => simp [literalNodeOf, NNFNode.Holds]
  | scale c child => simp [literalNodeOf, NNFNode.Holds]
  | add l r => simp [literalNodeOf, NNFNode.Holds]
  | mul l r => simp [literalNodeOf, NNFNode.Holds]

/-- The support translation is true exactly where the value is positive. -/
theorem toDNNF_semantics_inl (hnn : P.IsNonneg) (gate : P.Gate) (x : Fin N → Bool) :
    P.supportDescription.semantics (.inl gate) x ↔ 0 < P.value gate x := by
  induction gate using P.induction_rank with
  | _ gate ih =>
  rw [P.supportDescription.semantics_eq, supportDescription_node, value_eq]
  simp only [supportNode]
  have hnode := hnn gate
  cases hg : P.node gate with
  | leaf v h =>
    rw [hg] at hnode
    simp only [supportNodeOf, NNFNode.Holds, PCNode.eval, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, toDNNF_semantics_inr]
    constructor
    · rintro (⟨v', h', hvh, hpos, hx⟩ | ⟨v', h', hvh, hpos, hx⟩)
      · rw [hg] at hvh; cases hvh; rw [hx]; exact hpos
      · rw [hg] at hvh; cases hvh; rw [hx]; exact hpos
    · intro hpos
      cases hx : x v
      · left; exact ⟨v, h, hg, hx ▸ hpos, hx⟩
      · right; exact ⟨v, h, hg, hx ▸ hpos, hx⟩
  | const c =>
    simp only [supportNodeOf, PCNode.eval]
    split_ifs with hc <;> simp [NNFNode.Holds, hc]
  | scale c child =>
    rw [hg] at hnode
    have hcnn : 0 ≤ c := hnode
    have hchild : (P.node gate).IsChild child := by rw [hg]; rfl
    simp only [supportNodeOf, PCNode.eval]
    split_ifs with hc
    · simp only [NNFNode.Holds, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
      rw [ih child hchild]
      constructor
      · intro h; exact mul_pos hc h
      · intro h
        rcases lt_or_eq_of_le (P.value_nonneg hnn child x) with h'' | h''
        · exact h''
        · rw [← h'', mul_zero] at h; exact absurd h (lt_irrefl 0)
    · have hc0 : c = 0 := le_antisymm (not_lt.1 hc) hcnn
      simp [NNFNode.Holds, hc0]
  | add l r =>
    have hl : (P.node gate).IsChild l := by rw [hg]; exact Or.inl rfl
    have hr : (P.node gate).IsChild r := by rw [hg]; exact Or.inr rfl
    simp only [supportNodeOf, NNFNode.Holds, PCNode.eval, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left]
    rw [ih l hl, ih r hr]
    have h1 := P.value_nonneg hnn l x
    have h2 := P.value_nonneg hnn r x
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      linarith [hcon.1, hcon.2]
  | mul l r =>
    have hl : (P.node gate).IsChild l := by rw [hg]; exact Or.inl rfl
    have hr : (P.node gate).IsChild r := by rw [hg]; exact Or.inr rfl
    simp only [supportNodeOf, NNFNode.Holds, PCNode.eval]
    rw [ih l hl, ih r hr]
    have h1 := P.value_nonneg hnn l x
    have h2 := P.value_nonneg hnn r x
    constructor
    · rintro ⟨ha, hb⟩; exact mul_pos ha hb
    · intro h
      exact ⟨by
          rcases lt_or_eq_of_le h1 with h' | h'
          · exact h'
          · rw [← h', zero_mul] at h; exact absurd h (lt_irrefl 0),
        by
          rcases lt_or_eq_of_le h2 with h' | h'
          · exact h'
          · rw [← h', mul_zero] at h; exact absurd h (lt_irrefl 0)⟩

theorem toDNNF_computes (hnn : P.IsNonneg) :
    P.toDNNF.Computes fun x => 0 < P.value P.output x :=
  fun x => P.toDNNF_semantics_inl hnn P.output x

/-- The support of a gate of the translation is inside the scope of the
circuit gate. -/
theorem toDNNF_support_subset (gate : P.SupportGate) :
    P.supportDescription.support gate ⊆ P.scope (Sum.elim id Prod.fst gate) := by
  induction hr : P.supportRank gate using Nat.strong_induction_on generalizing gate with
  | _ r ih =>
  rw [P.supportDescription.support_eq, supportDescription_node]
  cases gate with
  | inl g =>
    simp only [supportNode, Sum.elim_inl, id]
    have hscope := P.scope_eq g
    cases hg : P.node g with
    | leaf v h =>
      rw [hg] at hscope
      simp only [supportNodeOf, NNFNode.Support, List.foldl_cons, List.foldl_nil,
        Finset.empty_union]
      have h1 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inr (g, false))
        (by simp [supportNode, supportNodeOf, hg, NNFNode.IsChild])) _ rfl
      have h2 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inr (g, true))
        (by simp [supportNode, supportNodeOf, hg, NNFNode.IsChild])) _ rfl
      simp only [Sum.elim_inr] at h1 h2
      exact Finset.union_subset h1 h2
    | const c =>
      simp only [supportNodeOf]
      split_ifs <;> simp [NNFNode.Support]
    | scale c child =>
      rw [hg] at hscope
      simp only [supportNodeOf]
      split_ifs
      · simp only [NNFNode.Support, List.foldl_cons, List.foldl_nil, Finset.empty_union]
        have h1 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inl child)
          (by simp [supportNode, supportNodeOf, NNFNode.IsChild, *])) _ rfl
        simp only [Sum.elim_inl, id] at h1
        rw [hscope]; exact h1
      · simp [NNFNode.Support]
    | add l r =>
      rw [hg] at hscope
      simp only [supportNodeOf, NNFNode.Support, List.foldl_cons, List.foldl_nil,
        Finset.empty_union]
      have h1 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inl l)
        (by simp [supportNode, supportNodeOf, hg, NNFNode.IsChild])) _ rfl
      have h2 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inl r)
        (by simp [supportNode, supportNodeOf, hg, NNFNode.IsChild])) _ rfl
      simp only [Sum.elim_inl, id] at h1 h2
      rw [hscope]
      exact Finset.union_subset_union h1 h2
    | mul l r =>
      rw [hg] at hscope
      simp only [supportNodeOf, NNFNode.Support]
      have h1 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inl l)
        (by simp [supportNode, supportNodeOf, hg, NNFNode.IsChild])) _ rfl
      have h2 := ih _ (hr ▸ P.supportRank_child (.inl g) (.inl r)
        (by simp [supportNode, supportNodeOf, hg, NNFNode.IsChild])) _ rfl
      simp only [Sum.elim_inl, id] at h1 h2
      rw [hscope]
      exact Finset.union_subset_union h1 h2
  | inr gb =>
    obtain ⟨g, b⟩ := gb
    simp only [supportNode, Sum.elim_inr]
    have hscope := P.scope_eq g
    cases hg : P.node g with
    | leaf v h =>
      rw [hg] at hscope
      simp only [literalNodeOf]
      rw [hscope]
      split_ifs <;> simp [NNFNode.Support, PCNode.Scope]
    | const c => simp [literalNodeOf, NNFNode.Support]
    | scale c child => simp [literalNodeOf, NNFNode.Support]
    | add l r => simp [literalNodeOf, NNFNode.Support]
    | mul l r => simp [literalNodeOf, NNFNode.Support]

theorem toDNNF_isDNNF (hdec : P.IsDecomposable) : P.toDNNF.IsDNNF := by
  intro gate left right hnode
  change P.supportNode gate = _ at hnode
  cases gate with
  | inl g =>
    simp only [supportNode] at hnode
    cases hg : P.node g with
    | mul l r =>
      rw [hg] at hnode
      simp only [supportNodeOf] at hnode
      obtain ⟨rfl, rfl⟩ := hnode
      have h1 := P.toDNNF_support_subset (.inl l)
      have h2 := P.toDNNF_support_subset (.inl r)
      simp only [Sum.elim_inl, id] at h1 h2
      exact Finset.disjoint_of_subset_left h1 (Finset.disjoint_of_subset_right h2 (hdec g l r hg))
    | leaf v h => rw [hg] at hnode; simp [supportNodeOf] at hnode
    | const c => rw [hg] at hnode; simp only [supportNodeOf] at hnode; split_ifs at hnode
    | scale c child =>
      rw [hg] at hnode; simp only [supportNodeOf] at hnode; split_ifs at hnode
    | add l r => rw [hg] at hnode; simp [supportNodeOf] at hnode
  | inr gb =>
    obtain ⟨g, b⟩ := gb
    simp only [supportNode] at hnode
    cases hg : P.node g with
    | leaf v h =>
      rw [hg] at hnode; simp only [literalNodeOf] at hnode
      split_ifs at hnode
    | const c => rw [hg] at hnode; cases hnode
    | scale c child => rw [hg] at hnode; cases hnode
    | add l r => rw [hg] at hnode; cases hnode
    | mul l r => rw [hg] at hnode; cases hnode

end Support

/-! ## Marginalizing hidden variables -/

section Forget

variable {W : Type*} [DecidableEq W] (P : ProbCircuit (V ⊕ W))

/-- The node of the marginal circuit: a hidden leaf becomes the sum of its
two values. -/
def forgetNode : PCNode (V ⊕ W) P.Gate → PCNode V P.Gate
  | .leaf (.inl v) h => .leaf v h
  | .leaf (.inr _) h => .const (h false + h true)
  | .const c => .const c
  | .scale c g => .scale c g
  | .add l r => .add l r
  | .mul l r => .mul l r

omit [DecidableEq V] [DecidableEq W] in
theorem forgetNode_isChild (node : PCNode (V ⊕ W) P.Gate) (c : P.Gate) :
    (P.forgetNode node).IsChild c ↔ node.IsChild c := by
  cases node with
  | leaf v h => cases v <;> rfl
  | _ => rfl

/-- The circuit over the visible variables. -/
abbrev forget : ProbCircuit V where
  Gate := P.Gate
  gateFintype := P.gateFintype
  gateDecidableEq := P.gateDecidableEq
  output := P.output
  node := fun g => P.forgetNode (P.node g)
  rank := P.rank
  child_rank := fun g c h => P.child_rank g c ((P.forgetNode_isChild _ _).1 h)

omit [DecidableEq V] [DecidableEq W] in
theorem forget_size : P.forget.size = P.size := rfl

omit [DecidableEq V] [DecidableEq W] in
theorem forget_isNonneg (hnn : P.IsNonneg) : P.forget.IsNonneg := by
  intro g
  have := hnn g
  show (P.forgetNode (P.node g)).IsNonneg
  cases hg : P.node g with
  | leaf v h =>
    rw [hg] at this
    cases v
    · exact this
    · exact add_nonneg (this false) (this true)
  | const c => rw [hg] at this; exact this
  | scale c child => rw [hg] at this; exact this
  | add l r => trivial
  | mul l r => trivial

theorem mem_forget_scope (g : P.Gate) (v : V) : v ∈ P.forget.scope g ↔ Sum.inl v ∈ P.scope g := by
  induction g using P.induction_rank with
  | _ g ih =>
  rw [P.forget.scope_eq, P.scope_eq]
  show v ∈ (P.forgetNode (P.node g)).Scope P.forget.scope ↔ _
  cases hg : P.node g with
  | leaf v' h =>
    cases v' with
    | inl v' => simp [forgetNode, PCNode.Scope]
    | inr w => simp [forgetNode, PCNode.Scope]
  | const c => simp [forgetNode, PCNode.Scope]
  | scale c child =>
    simp only [forgetNode, PCNode.Scope]
    exact ih child (by rw [hg]; rfl)
  | add l r =>
    simp only [forgetNode, PCNode.Scope, Finset.mem_union]
    rw [ih l (by rw [hg]; exact Or.inl rfl), ih r (by rw [hg]; exact Or.inr rfl)]
  | mul l r =>
    simp only [forgetNode, PCNode.Scope, Finset.mem_union]
    rw [ih l (by rw [hg]; exact Or.inl rfl), ih r (by rw [hg]; exact Or.inr rfl)]

theorem forget_isDecomposable (hdec : P.IsDecomposable) : P.forget.IsDecomposable := by
  intro g l r hnode
  have hg : P.node g = .mul l r := by
    revert hnode
    show P.forgetNode (P.node g) = .mul l r → _
    cases hg : P.node g with
    | leaf v h => cases v <;> simp [forgetNode]
    | const c => simp [forgetNode]
    | scale c child => simp [forgetNode]
    | add l' r' => simp [forgetNode]
    | mul l' r' =>
      simp only [forgetNode]
      rintro ⟨rfl, rfl⟩; rfl
  have hd := hdec g l r hg
  rw [Finset.disjoint_left] at hd ⊢
  intro v hv hv'
  rw [mem_forget_scope] at hv hv'
  exact hd hv hv'

/-- The marginal circuit is positive exactly when some assignment of the
hidden variables makes the original circuit positive. -/
theorem forget_value_pos_iff (hnn : P.IsNonneg) (hdec : P.IsDecomposable) (g : P.Gate)
    (x : V → Bool) :
    0 < P.forget.value g x ↔ ∃ y : W → Bool, 0 < P.value g (Sum.elim x y) := by
  induction g using P.induction_rank with
  | _ g ih =>
  rw [P.forget.value_eq]
  have hnode := hnn g
  have hval : ∀ y, P.value g (Sum.elim x y) = (P.node g).eval (fun c => P.value c (Sum.elim x y))
    (Sum.elim x y) := fun y => P.value_eq g _
  simp_rw [hval]
  show 0 < (P.forgetNode (P.node g)).eval (fun c => P.forget.value c x) x ↔ _
  cases hg : P.node g with
  | leaf v h =>
    rw [hg] at hnode
    cases v with
    | inl v => simp [forgetNode, PCNode.eval]
    | inr w =>
      simp only [forgetNode, PCNode.eval, Sum.elim_inr]
      constructor
      · intro hpos
        by_cases hf : 0 < h false
        · exact ⟨fun _ => false, hf⟩
        · exact ⟨fun _ => true, by
            have := hnode false
            have hf0 : h false = 0 := le_antisymm (not_lt.1 hf) this
            rw [hf0, zero_add] at hpos; exact hpos⟩
      · rintro ⟨y, hy⟩
        cases hyw : y w
        · rw [hyw] at hy; linarith [hnode true]
        · rw [hyw] at hy; linarith [hnode false]
  | const c => simp [forgetNode, PCNode.eval]
  | scale c child =>
    rw [hg] at hnode
    have hchild : (P.node g).IsChild child := by rw [hg]; rfl
    simp only [forgetNode, PCNode.eval]
    have hnn' := P.forget.value_nonneg (P.forget_isNonneg hnn) child x
    constructor
    · intro hpos
      have hc : 0 < c := by
        rcases lt_or_eq_of_le hnode with hc | hc
        · exact hc
        · rw [← hc, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      have hv : 0 < P.forget.value child x := by
        rcases lt_or_eq_of_le hnn' with hv | hv
        · exact hv
        · rw [← hv, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      obtain ⟨y, hy⟩ := (ih child hchild).1 hv
      exact ⟨y, mul_pos hc hy⟩
    · rintro ⟨y, hy⟩
      have hv := P.value_nonneg hnn child (Sum.elim x y)
      have hc : 0 < c := by
        rcases lt_or_eq_of_le hnode with hc | hc
        · exact hc
        · rw [← hc, zero_mul] at hy; exact absurd hy (lt_irrefl 0)
      have hv' : 0 < P.value child (Sum.elim x y) := by
        rcases lt_or_eq_of_le hv with hv' | hv'
        · exact hv'
        · rw [← hv', mul_zero] at hy; exact absurd hy (lt_irrefl 0)
      exact mul_pos hc ((ih child hchild).2 ⟨y, hv'⟩)
  | add l r =>
    have hl : (P.node g).IsChild l := by rw [hg]; exact Or.inl rfl
    have hr : (P.node g).IsChild r := by rw [hg]; exact Or.inr rfl
    simp only [forgetNode, PCNode.eval]
    have h1 := P.forget.value_nonneg (P.forget_isNonneg hnn) l x
    have h2 := P.forget.value_nonneg (P.forget_isNonneg hnn) r x
    constructor
    · intro hpos
      by_cases hlp : 0 < P.forget.value l x
      · obtain ⟨y, hy⟩ := (ih l hl).1 hlp
        exact ⟨y, by linarith [P.value_nonneg hnn r (Sum.elim x y)]⟩
      · have hrp : 0 < P.forget.value r x := by
          have : P.forget.value l x = 0 := le_antisymm (not_lt.1 hlp) h1
          rw [this, zero_add] at hpos; exact hpos
        obtain ⟨y, hy⟩ := (ih r hr).1 hrp
        exact ⟨y, by linarith [P.value_nonneg hnn l (Sum.elim x y)]⟩
    · rintro ⟨y, hy⟩
      have h1' := P.value_nonneg hnn l (Sum.elim x y)
      have h2' := P.value_nonneg hnn r (Sum.elim x y)
      by_cases hlp : 0 < P.value l (Sum.elim x y)
      · have := (ih l hl).2 ⟨y, hlp⟩; linarith
      · have hrp : 0 < P.value r (Sum.elim x y) := by
          have : P.value l (Sum.elim x y) = 0 := le_antisymm (not_lt.1 hlp) h1'
          rw [this, zero_add] at hy; exact hy
        have := (ih r hr).2 ⟨y, hrp⟩; linarith
  | mul l r =>
    have hl : (P.node g).IsChild l := by rw [hg]; exact Or.inl rfl
    have hr : (P.node g).IsChild r := by rw [hg]; exact Or.inr rfl
    have hdisj := hdec g l r hg
    simp only [forgetNode, PCNode.eval]
    have h1 := P.forget.value_nonneg (P.forget_isNonneg hnn) l x
    have h2 := P.forget.value_nonneg (P.forget_isNonneg hnn) r x
    constructor
    · intro hpos
      have hlp : 0 < P.forget.value l x := by
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      have hrp : 0 < P.forget.value r x := by
        rcases lt_or_eq_of_le h2 with h | h
        · exact h
        · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      obtain ⟨y1, hy1⟩ := (ih l hl).1 hlp
      obtain ⟨y2, hy2⟩ := (ih r hr).1 hrp
      -- combine the two witnesses along the disjoint scopes
      let y : W → Bool := fun w => if Sum.inr w ∈ P.scope l then y1 w else y2 w
      have e1 : P.value l (Sum.elim x y) = P.value l (Sum.elim x y1) := by
        apply P.value_congr_of_eqOn_scope
        intro v hv
        cases v with
        | inl v => rfl
        | inr w => simp [y, hv]
      have e2 : P.value r (Sum.elim x y) = P.value r (Sum.elim x y2) := by
        apply P.value_congr_of_eqOn_scope
        intro v hv
        cases v with
        | inl v => rfl
        | inr w =>
          have : Sum.inr w ∉ P.scope l := Finset.disjoint_right.1 hdisj hv
          simp [y, this]
      exact ⟨y, by rw [e1, e2]; exact mul_pos hy1 hy2⟩
    · rintro ⟨y, hy⟩
      have h1' := P.value_nonneg hnn l (Sum.elim x y)
      have h2' := P.value_nonneg hnn r (Sum.elim x y)
      have hlp : 0 < P.value l (Sum.elim x y) := by
        rcases lt_or_eq_of_le h1' with h | h
        · exact h
        · rw [← h, zero_mul] at hy; exact absurd hy (lt_irrefl 0)
      have hrp : 0 < P.value r (Sum.elim x y) := by
        rcases lt_or_eq_of_le h2' with h | h
        · exact h
        · rw [← h, mul_zero] at hy; exact absurd hy (lt_irrefl 0)
      exact mul_pos ((ih l hl).2 ⟨y, hlp⟩) ((ih r hr).2 ⟨y, hrp⟩)

end Forget

end ProbCircuit

end DDNNFNegation
