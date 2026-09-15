import DDNNFNegation.CircuitOperations

/-!
# Circuit preprocessing and size comparisons

Deduplicating disjunction inputs preserves the function and the circuit's
nodes. The resulting graph has a quadratic bound on its number of edges
in terms of its node count. Local support and rank lemmas justify the
transformation, and node-edge comparisons connect the internal edge-count
rectangle cover to the paper's node-count bound.
-/

namespace DDNNFNegation

open Finset

namespace NNFNode

variable {Var Gate : Type*}

/-- The inputs of a gate as a list; its length is the fan-in. -/
def childList : NNFNode Var Gate → List Gate
  | conj left right => [left, right]
  | disj children => children
  | _ => []

/-- The explicit child list has exactly the node's fan-in, including repeated disjuncts. -/
theorem length_childList (n : NNFNode Var Gate) :
    n.childList.length = n.fanIn := by
  cases n <;> rfl

/-- The child relation agrees with membership in the explicit child list. -/
theorem isChild_iff_mem_childList (n : NNFNode Var Gate) (c : Gate) :
    n.IsChild c ↔ c ∈ n.childList := by
  cases n <;> simp [IsChild, childList]

/-- Local truth is monotone in the truth of the children. -/
theorem holds_mono (v : Var → Bool) {p q : Gate → Prop} (n : NNFNode Var Gate)
    (h : ∀ c, n.IsChild c → p c → q c) : n.Holds v p → n.Holds v q := by
  cases n with
  | top => exact id
  | bot => exact id
  | pos x => exact id
  | neg x => exact id
  | conj left right =>
      simp only [Holds, IsChild] at h ⊢
      exact fun hh => ⟨h left (Or.inl rfl) hh.1, h right (Or.inr rfl) hh.2⟩
  | disj children =>
      simp only [Holds, IsChild] at h ⊢
      exact fun ⟨c, hc, hcp⟩ => ⟨c, hc, h c hc hcp⟩

/-- The image of an input under a relabeling is an input of the relabeled
gate. -/
theorem isChild_map {Gate' : Type*} (f : Gate → Gate') {n : NNFNode Var Gate}
    {c : Gate} (h : n.IsChild c) : (n.map f).IsChild (f c) := by
  cases n with
  | top => exact h.elim
  | bot => exact h.elim
  | pos x => exact h.elim
  | neg x => exact h.elim
  | conj left right =>
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | disj children => exact List.mem_map.mpr ⟨c, h, rfl⟩

/-- Variable relabeling preserves each node's number of incoming edges. -/
theorem fanIn_mapVariables {Var' : Type*} (f : Var → Var') (n : NNFNode Var Gate) :
    (n.mapVariables f).fanIn = n.fanIn := by
  cases n <;> rfl

/-- Fixing variables preserves the fan-in of every node. -/
theorem fanIn_restrictRightVariables {Extra : Type*} (fixed : Extra → Bool)
    (n : NNFNode (Var ⊕ Extra) Gate) :
    (n.restrictRightVariables fixed).fanIn = n.fanIn := by
  cases n with
  | top => rfl
  | bot => rfl
  | conj left right => rfl
  | disj children => rfl
  | pos x =>
      cases x with
      | inl x => rfl
      | inr y => cases hy : fixed y <;> simp [restrictRightVariables, fanIn, hy]
  | neg x =>
      cases x with
      | inl x => rfl
      | inr y => cases hy : fixed y <;> simp [restrictRightVariables, fanIn, hy]

section Support

variable [DecidableEq Var]

private theorem foldl_union_subset {p q : Gate → Finset Var} (children : List Gate)
    (initial initial' : Finset Var) (hinit : initial ⊆ initial')
    (h : ∀ c ∈ children, p c ⊆ q c) :
    children.foldl (fun result gate => result ∪ p gate) initial ⊆
      children.foldl (fun result gate => result ∪ q gate) initial' := by
  induction children generalizing initial initial' with
  | nil => exact hinit
  | cons c children ih =>
      simp only [List.foldl_cons]
      exact ih _ _ (union_subset_union hinit (h c (by simp)))
        (fun d hd => h d (by simp [hd]))

/-- Local support is monotone in the supports of the children. -/
theorem support_mono {p q : Gate → Finset Var} (n : NNFNode Var Gate)
    (h : ∀ c, n.IsChild c → p c ⊆ q c) : n.Support p ⊆ n.Support q := by
  cases n with
  | top => exact Subset.rfl
  | bot => exact Subset.rfl
  | pos x => exact Subset.rfl
  | neg x => exact Subset.rfl
  | conj left right =>
      simp only [Support, IsChild] at h ⊢
      exact union_subset_union (h left (Or.inl rfl)) (h right (Or.inr rfl))
  | disj children =>
      simp only [Support, IsChild] at h ⊢
      exact foldl_union_subset children ∅ ∅ Subset.rfl h

end Support

/-! ### Removing repeated inputs -/

section Dedup

variable [DecidableEq Gate]

/-- Remove repeated inputs of a disjunction. -/
def dedup : NNFNode Var Gate → NNFNode Var Gate
  | disj children => disj children.dedup
  | n => n

/-- Removing duplicate inputs introduces no new child references. -/
theorem isChild_of_isChild_dedup {n : NNFNode Var Gate} {c : Gate}
    (h : n.dedup.IsChild c) : n.IsChild c := by
  cases n with
  | disj children => simpa [dedup, IsChild] using h
  | top => exact h
  | bot => exact h
  | pos x => exact h
  | neg x => exact h
  | conj left right => exact h

/-- Repeating or removing a disjunct does not affect a node's truth value. -/
theorem holds_dedup (n : NNFNode Var Gate) (v : Var → Bool) (child : Gate → Prop) :
    n.dedup.Holds v child ↔ n.Holds v child := by
  cases n with
  | disj children => simp [dedup, Holds]
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | pos x => exact Iff.rfl
  | neg x => exact Iff.rfl
  | conj left right => exact Iff.rfl

/-- Removing duplicate disjuncts preserves the union of supports. -/
theorem support_dedup [DecidableEq Var] (n : NNFNode Var Gate)
    (s : Gate → Finset Var) : n.dedup.Support s = n.Support s := by
  cases n with
  | disj children =>
      simp only [dedup, Support]
      ext x
      rw [mem_foldl_union, mem_foldl_union]
      simp
  | top => rfl
  | bot => rfl
  | pos x => rfl
  | neg x => rfl
  | conj left right => rfl

/-- Removing repeated disjuncts cannot increase fan-in. -/
theorem fanIn_dedup_le [Fintype Gate] (n : NNFNode Var Gate) :
    n.dedup.fanIn ≤ Fintype.card Gate + 2 := by
  cases n with
  | disj children =>
      change children.dedup.length ≤ _
      exact (List.nodup_dedup children).length_le_card.trans (Nat.le_add_right _ _)
  | conj left right =>
      change 2 ≤ _
      omega
  | top => exact Nat.zero_le _
  | bot => exact Nat.zero_le _
  | pos x => exact Nat.zero_le _
  | neg x => exact Nat.zero_le _

/-- Input deduplication changes disjunction lists only, leaving conjunctions recognizable. -/
theorem dedup_eq_conj_iff (n : NNFNode Var Gate) (left right : Gate) :
    n.dedup = conj left right ↔ n = conj left right := by
  cases n with
  | disj children => simp [dedup]
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | pos x => exact Iff.rfl
  | neg x => exact Iff.rfl
  | conj a b => exact Iff.rfl

end Dedup

end NNFNode

/-- A left fold of unions starts from its initial set. -/
theorem foldl_union_eq_union_foldl {α β : Type*} [DecidableEq β]
    (l : List α) (s : α → Finset β) (init : Finset β) :
    l.foldl (fun result c ↦ result ∪ s c) init =
      init ∪ l.foldl (fun result c ↦ result ∪ s c) ∅ := by
  ext x
  rw [mem_foldl_union, Finset.mem_union, mem_foldl_union]
  simp

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

/-- One input has at most as many edges as the whole circuit. -/
theorem fanIn_le_edgeCount (C : NNFCircuit Var) (gate : C.Gate) :
    (C.node gate).fanIn ≤ C.edgeCount := by
  unfold edgeCount
  exact Finset.single_le_sum (f := fun gate ↦ (C.node gate).fanIn)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ gate)

/-! ### Gates against edges -/

/-- If every gate other than the output is an input of some gate, there are
at most one more gate than edges: the tutorial's "every gate other than the
output has an outgoing edge, so the number of gates is at most the number of
edges plus one". -/
theorem size_le_edgeCount_add_one (C : NNFCircuit Var)
    (h : ∀ gate, gate ≠ C.output → ∃ parent, (C.node parent).IsChild gate) :
    C.size ≤ C.edgeCount + 1 := by
  have hsub : (univ : Finset C.Gate) ⊆
      insert C.output
        (univ.biUnion fun parent ↦ (C.node parent).childList.toFinset) := by
    intro gate _
    by_cases hout : gate = C.output
    · rw [hout]
      exact mem_insert_self _ _
    · obtain ⟨parent, hparent⟩ := h gate hout
      apply mem_insert_of_mem
      rw [mem_biUnion]
      exact ⟨parent, mem_univ _, List.mem_toFinset.mpr
        ((NNFNode.isChild_iff_mem_childList _ _).mp hparent)⟩
  calc C.size = (univ : Finset C.Gate).card := Finset.card_univ.symm
    _ ≤ (insert C.output
          (univ.biUnion fun parent ↦ (C.node parent).childList.toFinset)).card :=
        card_le_card hsub
    _ ≤ (univ.biUnion fun parent ↦ (C.node parent).childList.toFinset).card + 1 :=
        card_insert_le _ _
    _ ≤ (∑ parent, (C.node parent).childList.toFinset.card) + 1 :=
        Nat.add_le_add_right card_biUnion_le 1
    _ ≤ (∑ parent, (C.node parent).childList.length) + 1 :=
        Nat.add_le_add_right
          (Finset.sum_le_sum fun parent _ ↦ List.toFinset_card_le _) 1
    _ = C.edgeCount + 1 := by
        simp only [edgeCount, NNFNode.length_childList]

/-! ### Circuits from a node map -/

section OfNodes

variable {Gate : Type*}

/-- Truth values computed from a node map with a fuel counter. -/
def holdsFuel (node : Gate → NNFNode Var Gate) (v : Var → Bool) :
    ℕ → Gate → Prop
  | 0, _ => False
  | n + 1, gate => (node gate).Holds v (fun child => holdsFuel node v n child)

/-- Supports computed from a node map with a fuel counter. -/
def supportFuel (node : Gate → NNFNode Var Gate) : ℕ → Gate → Finset Var
  | 0, _ => ∅
  | n + 1, gate => (node gate).Support (fun child => supportFuel node n child)

variable (node : Gate → NNFNode Var Gate) (rank : Gate → ℕ)
  (hrank : ∀ gate child, (node gate).IsChild child → rank child < rank gate)
include hrank

omit [DecidableEq Var] in
/-- Above the rank of a gate the fuel no longer matters. -/
theorem holdsFuel_stable (v : Var → Bool) :
    ∀ (n m : ℕ) (gate : Gate), rank gate < n → rank gate < m →
      (holdsFuel node v n gate ↔ holdsFuel node v m gate) := by
  intro n
  induction n with
  | zero =>
      intro m gate hn
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
      intro m gate hn hm
      cases m with
      | zero => exact absurd hm (Nat.not_lt_zero _)
      | succ m =>
          simp only [holdsFuel]
          apply NNFNode.holds_congr
          intro child hchild
          have := hrank gate child hchild
          exact ih m child (by omega) (by omega)

/-- Once the recursion budget exceeds the gate rank, increasing it leaves the computed
support unchanged. -/
theorem supportFuel_stable :
    ∀ (n m : ℕ) (gate : Gate), rank gate < n → rank gate < m →
      supportFuel node n gate = supportFuel node m gate := by
  intro n
  induction n with
  | zero =>
      intro m gate hn
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
      intro m gate hn hm
      cases m with
      | zero => exact absurd hm (Nat.not_lt_zero _)
      | succ m =>
          simp only [supportFuel]
          apply NNFNode.support_congr
          intro child hchild
          have := hrank gate child hchild
          exact ih m child (by omega) (by omega)

variable [Fintype Gate] [DecidableEq Gate]

/-- The circuit with the given nodes and ranks; its semantics and support
are computed by recursion on the rank. -/
def ofNodes (output : Gate) : NNFCircuit Var where
  Gate := Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := output
  node := node
  rank := rank
  child_rank := hrank
  semantics := fun gate v => holdsFuel node v (rank gate + 1) gate
  semantics_eq := by
    intro gate v
    simp only [holdsFuel]
    apply NNFNode.holds_congr
    intro child hchild
    exact holdsFuel_stable node rank hrank v _ _ child
      (hrank gate child hchild) (Nat.lt_succ_self _)
  support := fun gate => supportFuel node (rank gate + 1) gate
  support_eq := by
    intro gate
    simp only [supportFuel]
    apply NNFNode.support_congr
    intro child hchild
    exact supportFuel_stable node rank hrank _ _ child
      (hrank gate child hchild) (Nat.lt_succ_self _)

end OfNodes

/-! ### Edge counts of the variable relabelings -/

theorem edgeCount_transportGates {Gate' : Type*} [Fintype Gate'] [DecidableEq Gate']
    (C : NNFCircuit Var) (e : C.Gate ≃ Gate') :
    (C.transportGates e).edgeCount = C.edgeCount := by
  unfold edgeCount
  change ∑ gate : Gate', ((C.node (e.symm gate)).map e).fanIn =
    ∑ gate : C.Gate, (C.node gate).fanIn
  simp only [NNFNode.fanIn_map]
  exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

/-- Renumbering gates preserves the total edge count. -/
theorem edgeCount_toFinGates (C : NNFCircuit Var) :
    C.toFinGates.edgeCount = C.edgeCount :=
  edgeCount_transportGates C _

/-- Injective variable relabeling preserves the total edge count. -/
theorem edgeCount_mapVariables {Var' : Type*} [DecidableEq Var']
    (C : NNFCircuit Var) (e : Var ↪ Var') :
    (C.mapVariables e).edgeCount = C.edgeCount := by
  unfold edgeCount
  change ∑ gate : C.Gate, ((C.node gate).mapVariables e).fanIn = _
  simp only [NNFNode.fanIn_mapVariables]

/-- Fixing padding variables preserves the total edge count. -/
theorem edgeCount_restrictRightVariables {Extra : Type*} [DecidableEq Extra]
    (C : NNFCircuit (Var ⊕ Extra)) (fixed : Extra → Bool) :
    (C.restrictRightVariables fixed).edgeCount = C.edgeCount := by
  unfold edgeCount
  change ∑ gate : C.Gate, ((C.node gate).restrictRightVariables fixed).fanIn = _
  simp only [NNFNode.fanIn_restrictRightVariables]

/-- Adding unused variables costs no circuit edges. -/
theorem edgeCount_padRightVariables {Extra : Type*} [DecidableEq Extra]
    (C : NNFCircuit Var) :
    (C.padRightVariables (Extra := Extra)).edgeCount = C.edgeCount :=
  edgeCount_mapVariables C _

/-! ### Removing repeated inputs -/

/-- The circuit with the repeated inputs of every disjunction removed.  The
gates, the function computed at each gate, and the supports are unchanged;
each gate now has at most `size + 2` inputs. -/
def dedup (C : NNFCircuit Var) : NNFCircuit Var :=
  ofNodes (fun gate ↦ (C.node gate).dedup) C.rank
    (fun gate child hchild ↦
      C.child_rank gate child (NNFNode.isChild_of_isChild_dedup hchild))
    C.output

/-- Input deduplication preserves every gate's Boolean value. -/
theorem dedup_semantics (C : NNFCircuit Var) (gate : C.Gate) (v : Var → Bool) :
    C.dedup.semantics gate v ↔ C.semantics gate v := by
  refine C.semantics_unique (fun gate v ↦ C.dedup.semantics gate v) ?_ gate v
  intro gate v
  rw [C.dedup.semantics_eq gate v]
  exact NNFNode.holds_dedup (C.node gate) v _

/-- Input deduplication preserves every gate's variable support. -/
theorem dedup_support (C : NNFCircuit Var) (gate : C.Gate) :
    C.dedup.support gate = C.support gate := by
  refine C.support_unique (fun gate ↦ C.dedup.support gate) ?_ gate
  intro gate
  rw [C.dedup.support_eq gate]
  exact NNFNode.support_dedup (C.node gate) _

/-- Input deduplication preserves the function at the output. -/
theorem dedup_computes (C : NNFCircuit Var) {f : (Var → Bool) → Prop}
    (h : C.Computes f) : C.dedup.Computes f :=
  fun v ↦ (C.dedup_semantics C.output v).trans (h v)

/-- Input deduplication preserves disjoint conjunction supports. -/
theorem dedup_isDecomposable (C : NNFCircuit Var) (h : C.IsDecomposable) :
    C.dedup.IsDecomposable := by
  intro gate left right hnode
  have hnode' : C.node gate = .conj left right :=
    (NNFNode.dedup_eq_conj_iff (C.node gate) left right).mp hnode
  have hl := C.dedup_support left
  have hr := C.dedup_support right
  rw [hl, hr]
  exact h gate left right hnode'

/-- Input deduplication preserves the DNNF class. -/
theorem dedup_isDNNF (C : NNFCircuit Var) (h : C.IsDNNF) : C.dedup.IsDNNF :=
  C.dedup_isDecomposable h

/-- Removing duplicate inputs cannot increase the circuit's total edge count. -/
theorem edgeCount_dedup_le (C : NNFCircuit Var) :
    C.dedup.edgeCount ≤ C.size * (C.size + 2) := by
  unfold edgeCount
  change ∑ gate : C.Gate, ((C.node gate).dedup).fanIn ≤ _
  calc ∑ gate : C.Gate, ((C.node gate).dedup).fanIn
      ≤ ∑ _gate : C.Gate, (Fintype.card C.Gate + 2) :=
        Finset.sum_le_sum fun gate _ ↦ NNFNode.fanIn_dedup_le _
    _ = C.size * (C.size + 2) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rfl

end NNFCircuit

end DDNNFNegation
