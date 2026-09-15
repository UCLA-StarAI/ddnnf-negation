import DDNNFNegation.CircuitPreprocessing

/-!
# Binarizing disjunctions

`NNFCircuit.binarize` replaces each disjunction by a chain of binary
disjunctions ending in false. Conjunctions are already binary in this model.
The construction preserves the computed function and decomposability;
`edgeCount_binarize_le` bounds its edge count by twice the original edge
count. This supplies the fan-in reduction used in the rectangle-cover proof.
-/

namespace DDNNFNegation

open Finset

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

/-- Gates of the binarized circuit: for each gate `g` of `C`, the positions
`0, …, fanIn g` of its chain. -/
abbrev ChainGate (C : NNFCircuit Var) :=
  Σ gate : C.Gate, Fin ((C.node gate).fanIn + 1)

/-- The chain position standing for an original gate. -/
def chainRoot (C : NNFCircuit Var) (gate : C.Gate) : C.ChainGate :=
  ⟨gate, 0⟩

/-- The next position of a chain. -/
def chainNext (C : NNFCircuit Var) (x : C.ChainGate)
    (h : x.2.val < (C.node x.1).fanIn) : C.ChainGate :=
  ⟨x.1, ⟨x.2.val + 1, by omega⟩⟩

/-- The link at position `i` of the chain replacing a node, given the gate
for the rest of the chain. -/
def chainLink (C : NNFCircuit Var) (n : NNFNode Var C.Gate) (i : ℕ)
    (next : C.ChainGate) : NNFNode Var C.ChainGate :=
  match n with
  | .conj left right => .conj (C.chainRoot left) (C.chainRoot right)
  | .disj children =>
      if h : i < children.length then .disj [C.chainRoot children[i], next]
      else .disj []
  | _ => .bot

/-- The last position of a chain. -/
def chainLeaf (C : NNFCircuit Var) (n : NNFNode Var C.Gate) :
    NNFNode Var C.ChainGate :=
  match n with
  | .top => .top
  | .bot => .bot
  | .pos y => .pos y
  | .neg y => .neg y
  | .conj _ _ => .bot
  | .disj _ => .disj []

/-- The node at a chain position. -/
def chainNode (C : NNFCircuit Var) (x : C.ChainGate) : NNFNode Var C.ChainGate :=
  if h : x.2.val < (C.node x.1).fanIn then
    C.chainLink (C.node x.1) x.2.val (C.chainNext x h)
  else C.chainLeaf (C.node x.1)

/-- The root position of a gate's chain reproduces its expanded node. -/
theorem chainNode_root (C : NNFCircuit Var) (gate : C.Gate) :
    C.chainNode (C.chainRoot gate) =
      if h : 0 < (C.node gate).fanIn then
        C.chainLink (C.node gate) 0 (C.chainNext (C.chainRoot gate) h)
      else C.chainLeaf (C.node gate) := rfl

/-- A chain link encoding a conjunction refers to the roots of its two children. -/
theorem chainLink_conj (C : NNFCircuit Var) {gate left right : C.Gate}
    (hnode : C.node gate = .conj left right) (i : ℕ) (next : C.ChainGate) :
    C.chainLink (C.node gate) i next = .conj (C.chainRoot left) (C.chainRoot right) := by
  rw [hnode]
  rfl

/-- A chain link encoding a disjunction takes the next child or continues the suffix chain. -/
theorem chainLink_disj (C : NNFCircuit Var) {gate : C.Gate} {children : List C.Gate}
    (hnode : C.node gate = .disj children) (i : ℕ) (next : C.ChainGate) :
    C.chainLink (C.node gate) i next =
      if h : i < children.length then .disj [C.chainRoot children[i], next]
      else .disj [] := by
  rw [hnode]
  rfl

/-- The inputs of a chain link. -/
theorem isChild_chainLink (C : NNFCircuit Var) (n : NNFNode Var C.Gate) (i : ℕ)
    (next : C.ChainGate) {c : C.ChainGate} (hc : (C.chainLink n i next).IsChild c) :
    (∃ left right, n = .conj left right ∧
        (c = C.chainRoot left ∨ c = C.chainRoot right)) ∨
      (∃ children : List C.Gate, n = .disj children ∧
        ∃ hi : i < children.length, c = C.chainRoot children[i] ∨ c = next) := by
  cases n with
  | conj left right => exact Or.inl ⟨left, right, rfl, hc⟩
  | disj children =>
      refine Or.inr ⟨children, rfl, ?_⟩
      simp only [chainLink] at hc
      split_ifs at hc with hi
      · exact ⟨hi, by simpa [NNFNode.IsChild] using hc⟩
      · simp [NNFNode.IsChild] at hc
  | top => exact False.elim hc
  | bot => exact False.elim hc
  | pos y => exact False.elim hc
  | neg y => exact False.elim hc

/-- A chain link that is a conjunction copies a conjunction. -/
theorem chainLink_eq_conj (C : NNFCircuit Var) (n : NNFNode Var C.Gate) (i : ℕ)
    (next : C.ChainGate) {a b : C.ChainGate} (h : C.chainLink n i next = .conj a b) :
    ∃ left right, n = .conj left right ∧ a = C.chainRoot left ∧ b = C.chainRoot right := by
  cases n with
  | conj left right =>
      exact ⟨left, right, rfl, (NNFNode.conj.inj h).1.symm, (NNFNode.conj.inj h).2.symm⟩
  | disj children =>
      simp only [chainLink] at h
      split_ifs at h
  | top => simp [chainLink] at h
  | bot => simp [chainLink] at h
  | pos y => simp [chainLink] at h
  | neg y => simp [chainLink] at h

/-- Terminal chain positions have no child references. -/
theorem not_isChild_chainLeaf (C : NNFCircuit Var) (n : NNFNode Var C.Gate)
    (c : C.ChainGate) : ¬ (C.chainLeaf n).IsChild c := by
  cases n <;> simp [chainLeaf, NNFNode.IsChild]

/-- A terminal chain position is not a conjunction. -/
theorem chainLeaf_ne_conj (C : NNFCircuit Var) (n : NNFNode Var C.Gate)
    (a b : C.ChainGate) : C.chainLeaf n ≠ .conj a b := by
  cases n <;> simp [chainLeaf]

/-- Each chain link has at most two incoming edges. -/
theorem fanIn_chainLink_le (C : NNFCircuit Var) (n : NNFNode Var C.Gate) (i : ℕ)
    (next : C.ChainGate) : (C.chainLink n i next).fanIn ≤ 2 := by
  cases n with
  | conj left right => exact le_rfl
  | disj children =>
      simp only [chainLink]
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
  | top => exact Nat.zero_le _
  | bot => exact Nat.zero_le _
  | pos y => exact Nat.zero_le _
  | neg y => exact Nat.zero_le _

/-- A terminal chain position has zero fan-in. -/
theorem fanIn_chainLeaf (C : NNFCircuit Var) (n : NNFNode Var C.Gate) :
    (C.chainLeaf n).fanIn = 0 := by
  cases n <;> rfl

/-- Every node in the binary expansion has fan-in at most two. -/
theorem fanIn_chainNode_le (C : NNFCircuit Var) (x : C.ChainGate) :
    (C.chainNode x).fanIn ≤ if x.2.val < (C.node x.1).fanIn then 2 else 0 := by
  unfold chainNode
  split_ifs with h
  · exact C.fanIn_chainLink_le _ _ _
  · rw [C.fanIn_chainLeaf]

/-- Ranks of the chain positions: the original ranks, spread out so that a
whole chain fits between two consecutive original ranks. -/
def chainRank (C : NNFCircuit Var) (x : C.ChainGate) : ℕ :=
  C.rank x.1 * (C.edgeCount + 2) + (C.edgeCount + 1 - x.2.val)

/-- Following an original child reference to its chain root decreases the expanded rank. -/
theorem chainRoot_rank_lt (C : NNFCircuit Var) {gate child : C.Gate}
    (h : (C.node gate).IsChild child) (i : Fin ((C.node gate).fanIn + 1)) :
    C.chainRank (C.chainRoot child) < C.chainRank ⟨gate, i⟩ := by
  simp only [chainRank, chainRoot, Fin.val_zero, Nat.sub_zero]
  have hlt := C.child_rank gate child h
  have hi : i.val ≤ C.edgeCount := by
    have := i.isLt
    have := C.fanIn_le_edgeCount gate
    omega
  have hmul : C.rank child * (C.edgeCount + 2) + (C.edgeCount + 2) ≤
      C.rank gate * (C.edgeCount + 2) := by
    have := Nat.mul_le_mul_right (C.edgeCount + 2) hlt
    rwa [Nat.succ_mul] at this
  omega

/-- Moving along a suffix chain decreases the expanded rank. -/
theorem chainNext_rank_lt (C : NNFCircuit Var) (x : C.ChainGate)
    (h : x.2.val < (C.node x.1).fanIn) :
    C.chainRank (C.chainNext x h) < C.chainRank x := by
  simp only [chainRank, chainNext]
  have := C.fanIn_le_edgeCount x.1
  omega

/-- Both kinds of expanded child references decrease rank, certifying acyclicity. -/
theorem chain_child_rank (C : NNFCircuit Var) :
    ∀ x child, (C.chainNode x).IsChild child → C.chainRank child < C.chainRank x := by
  intro x child hchild
  unfold chainNode at hchild
  split_ifs at hchild with h
  · rcases C.isChild_chainLink _ _ _ hchild with
      ⟨left, right, hnode, rfl | rfl⟩ | ⟨children, hnode, hi, rfl | rfl⟩
    · exact C.chainRoot_rank_lt (by rw [hnode]; exact Or.inl rfl) x.2
    · exact C.chainRoot_rank_lt (by rw [hnode]; exact Or.inr rfl) x.2
    · have hmem : ∀ i (hi : i < children.length), (C.node x.1).IsChild children[i] := by
        intro i hi
        rw [hnode]
        exact List.getElem_mem hi
      exact C.chainRoot_rank_lt (hmem _ hi) x.2
    · exact C.chainNext_rank_lt x h
  · exact absurd hchild (C.not_isChild_chainLeaf _ _)

/-- The circuit with every disjunction replaced by a chain of binary
disjunctions. -/
def binarize (C : NNFCircuit Var) : NNFCircuit Var :=
  ofNodes C.chainNode C.chainRank C.chain_child_rank (C.chainRoot C.output)

/-- The node description of the binarized circuit is the chosen chain node. -/
theorem binarize_node (C : NNFCircuit Var) (x : C.ChainGate) :
    C.binarize.node x = C.chainNode x := rfl

/-- The expanded shared circuit has fan-in at most two at every gate. -/
theorem binarize_isFanInTwo (C : NNFCircuit Var) : C.binarize.IsFanInTwo := by
  intro x children hnode
  change C.chainNode x = .disj children at hnode
  have hle := C.fanIn_chainNode_le x
  rw [hnode] at hle
  exact hle.trans (by split_ifs <;> omega)

/-- Truth along a chain: position `i` of the chain of a disjunction is the
disjunction of the inputs from `i` on. -/
theorem binarize_chain_semantics (C : NNFCircuit Var) {gate : C.Gate}
    {cs : List C.Gate} (hnode : C.node gate = .disj cs) (v : Var → Bool) :
    ∀ d i (hi : i < (C.node gate).fanIn + 1), i + d = cs.length →
      (C.binarize.semantics ⟨gate, ⟨i, hi⟩⟩ v ↔
        ∃ c ∈ cs.drop i, C.binarize.semantics (C.chainRoot c) v) := by
  have hk : (C.node gate).fanIn = cs.length := by rw [hnode]; rfl
  intro d
  induction d with
  | zero =>
      intro i hi hd
      have hi' : i = cs.length := by omega
      subst hi'
      rw [C.binarize.semantics_eq ⟨gate, ⟨cs.length, hi⟩⟩ v]
      show (if h : cs.length < (C.node gate).fanIn then
          C.chainLink (C.node gate) cs.length (C.chainNext ⟨gate, ⟨cs.length, hi⟩⟩ h)
        else C.chainLeaf (C.node gate)).Holds v (fun y : C.ChainGate ↦ C.binarize.semantics y v) ↔ _
      rw [dif_neg (by omega), hnode]
      simp [chainLeaf, NNFNode.Holds, List.drop_length]
  | succ d ih =>
      intro i hi hd
      have hlt : i < cs.length := by omega
      have hfan : i < (C.node gate).fanIn := by omega
      rw [C.binarize.semantics_eq ⟨gate, ⟨i, hi⟩⟩ v]
      show (if h : i < (C.node gate).fanIn then
          C.chainLink (C.node gate) i (C.chainNext ⟨gate, ⟨i, hi⟩⟩ h)
        else C.chainLeaf (C.node gate)).Holds v (fun y : C.ChainGate ↦ C.binarize.semantics y v) ↔ _
      rw [dif_pos hfan, C.chainLink_disj hnode, dif_pos hlt]
      have hnext : C.chainNext ⟨gate, ⟨i, hi⟩⟩ hfan = ⟨gate, ⟨i + 1, by omega⟩⟩ := rfl
      rw [hnext, List.drop_eq_getElem_cons hlt]
      simp only [NNFNode.Holds, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left]
      rw [ih (i + 1) (by omega) (by omega)]

/-- At each original gate's root, the expanded circuit has the original truth value. -/
theorem binarize_semantics_root (C : NNFCircuit Var) (gate : C.Gate) (v : Var → Bool) :
    C.binarize.semantics (C.chainRoot gate) v ↔ C.semantics gate v := by
  refine C.semantics_unique (fun gate v ↦ C.binarize.semantics (C.chainRoot gate) v)
    ?_ gate v
  intro gate v
  cases hnode : C.node gate with
  | conj left right =>
      rw [C.binarize.semantics_eq (C.chainRoot gate) v, C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_pos (by rw [hnode]; exact Nat.zero_lt_two), C.chainLink_conj hnode]
      exact Iff.rfl
  | disj cs =>
      have hroot : C.chainRoot gate = ⟨gate, ⟨0, by omega⟩⟩ := rfl
      rw [hroot, C.binarize_chain_semantics hnode v cs.length 0 _ (by omega),
        List.drop_zero]
      exact Iff.rfl
  | top =>
      rw [C.binarize.semantics_eq (C.chainRoot gate) v, C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      exact Iff.rfl
  | bot =>
      rw [C.binarize.semantics_eq (C.chainRoot gate) v, C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      exact Iff.rfl
  | pos y =>
      rw [C.binarize.semantics_eq (C.chainRoot gate) v, C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      exact Iff.rfl
  | neg y =>
      rw [C.binarize.semantics_eq (C.chainRoot gate) v, C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      exact Iff.rfl

/-- Binarization preserves the computed output function. -/
theorem binarize_computes (C : NNFCircuit Var) {f : (Var → Bool) → Prop}
    (h : C.Computes f) : C.binarize.Computes f :=
  fun v ↦ (C.binarize_semantics_root C.output v).trans (h v)

/-- Supports along a chain. -/
theorem binarize_chain_support (C : NNFCircuit Var) {gate : C.Gate}
    {cs : List C.Gate} (hnode : C.node gate = .disj cs) :
    ∀ d i (hi : i < (C.node gate).fanIn + 1), i + d = cs.length →
      C.binarize.support ⟨gate, ⟨i, hi⟩⟩ =
        (cs.drop i).foldl
          (fun result c ↦ result ∪ C.binarize.support (C.chainRoot c)) ∅ := by
  have hk : (C.node gate).fanIn = cs.length := by rw [hnode]; rfl
  intro d
  induction d with
  | zero =>
      intro i hi hd
      have hi' : i = cs.length := by omega
      subst hi'
      rw [C.binarize.support_eq ⟨gate, ⟨cs.length, hi⟩⟩]
      show (if h : cs.length < (C.node gate).fanIn then
          C.chainLink (C.node gate) cs.length (C.chainNext ⟨gate, ⟨cs.length, hi⟩⟩ h)
        else C.chainLeaf (C.node gate)).Support (fun y : C.ChainGate ↦ C.binarize.support y) = _
      rw [dif_neg (by omega), hnode]
      simp [chainLeaf, NNFNode.Support, List.drop_length]
  | succ d ih =>
      intro i hi hd
      have hlt : i < cs.length := by omega
      have hfan : i < (C.node gate).fanIn := by omega
      rw [C.binarize.support_eq ⟨gate, ⟨i, hi⟩⟩]
      show (if h : i < (C.node gate).fanIn then
          C.chainLink (C.node gate) i (C.chainNext ⟨gate, ⟨i, hi⟩⟩ h)
        else C.chainLeaf (C.node gate)).Support (fun y : C.ChainGate ↦ C.binarize.support y) = _
      rw [dif_pos hfan, C.chainLink_disj hnode, dif_pos hlt]
      have hnext : C.chainNext ⟨gate, ⟨i, hi⟩⟩ hfan = ⟨gate, ⟨i + 1, by omega⟩⟩ := rfl
      rw [hnext, List.drop_eq_getElem_cons hlt]
      simp only [NNFNode.Support, List.foldl_cons, List.foldl_nil, Finset.empty_union]
      rw [ih (i + 1) (by omega) (by omega),
        foldl_union_eq_union_foldl _ _ (C.binarize.support (C.chainRoot cs[i]))]

/-- At each original gate's root, binarization preserves its variable support. -/
theorem binarize_support_root (C : NNFCircuit Var) (gate : C.Gate) :
    C.binarize.support (C.chainRoot gate) = C.support gate := by
  refine C.support_unique (fun gate ↦ C.binarize.support (C.chainRoot gate)) ?_ gate
  intro gate
  cases hnode : C.node gate with
  | conj left right =>
      rw [C.binarize.support_eq (C.chainRoot gate), C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_pos (by rw [hnode]; exact Nat.zero_lt_two), C.chainLink_conj hnode]
      rfl
  | disj cs =>
      have hroot : C.chainRoot gate = ⟨gate, ⟨0, by omega⟩⟩ := rfl
      rw [hroot, C.binarize_chain_support hnode cs.length 0 _ (by omega),
        List.drop_zero]
      rfl
  | top =>
      rw [C.binarize.support_eq (C.chainRoot gate), C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      rfl
  | bot =>
      rw [C.binarize.support_eq (C.chainRoot gate), C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      rfl
  | pos y =>
      rw [C.binarize.support_eq (C.chainRoot gate), C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      rfl
  | neg y =>
      rw [C.binarize.support_eq (C.chainRoot gate), C.binarize_node (C.chainRoot gate),
        chainNode_root, dif_neg (by rw [hnode]; exact Nat.lt_irrefl 0), hnode]
      rfl

/-- A conjunction of the binarized circuit is the copy of a conjunction of
the original. -/
theorem chainNode_eq_conj (C : NNFCircuit Var) {x : C.ChainGate} {a b : C.ChainGate}
    (hx : C.chainNode x = .conj a b) :
    ∃ left right, C.node x.1 = .conj left right ∧
      a = C.chainRoot left ∧ b = C.chainRoot right := by
  unfold chainNode at hx
  split_ifs at hx with h
  · exact C.chainLink_eq_conj _ _ _ hx
  · exact absurd hx (C.chainLeaf_ne_conj _ _ _)

/-- The expansion introduces only disjunction chains, preserving decomposability. -/
theorem binarize_isDecomposable (C : NNFCircuit Var) (h : C.IsDecomposable) :
    C.binarize.IsDecomposable := by
  intro x a b hx
  change C.chainNode x = .conj a b at hx
  obtain ⟨left, right, hnode, rfl, rfl⟩ := C.chainNode_eq_conj hx
  have hl := C.binarize_support_root left
  have hr := C.binarize_support_root right
  rw [hl, hr]
  exact h x.1 left right hnode

/-- Binarization preserves the DNNF class. -/
theorem binarize_isDNNF (C : NNFCircuit Var) (h : C.IsDNNF) : C.binarize.IsDNNF :=
  C.binarize_isDecomposable h

/-- The chain of a gate with `k` inputs has at most `2 k` edges. -/
theorem edgeCount_binarize_le (C : NNFCircuit Var) :
    C.binarize.edgeCount ≤ 2 * C.edgeCount := by
  unfold edgeCount
  change ∑ x : C.ChainGate, (C.chainNode x).fanIn ≤ 2 * ∑ gate : C.Gate, (C.node gate).fanIn
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro gate _
  calc ∑ i : Fin ((C.node gate).fanIn + 1), (C.chainNode ⟨gate, i⟩).fanIn
      ≤ ∑ i : Fin ((C.node gate).fanIn + 1),
          (if i.val < (C.node gate).fanIn then 2 else 0) :=
        Finset.sum_le_sum fun i _ ↦ C.fanIn_chainNode_le ⟨gate, i⟩
    _ = 2 * (C.node gate).fanIn := by
        rw [Fin.sum_univ_castSucc]
        simp [Finset.sum_const, mul_comm]

end NNFCircuit

end DDNNFNegation
