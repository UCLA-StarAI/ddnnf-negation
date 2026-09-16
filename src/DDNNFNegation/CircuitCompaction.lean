import DDNNFNegation.CircuitTransport

/-!
# Removing unused array positions

Keep the output and every position named as a child. This set is closed
under child references and has at most `edgeCount + 1` positions. Sorting
it preserves the topological order, evaluation, and decomposability. The
bound is needed when transporting edge-based size through the rectangular
binary expansion, whose storage cost depends on the array length.
-/

namespace DDNNFNegation

namespace Node

/-- Rename child positions, retaining the node label. -/
def map {Var : Type} {m n : ℕ} (f : Fin m → Fin n) : Node Var m → Node Var n
  | .const b => .const b
  | .lit x b => .lit x b
  | .and children => .and (children.image f)
  | .or children => .or (children.image f)

@[simp] theorem children_map {Var : Type} {m n : ℕ} (f : Fin m → Fin n)
    (node : Node Var m) : (node.map f).children = node.children.image f := by
  cases node <;> simp [map, children]

theorem evalLocal_map {Var : Type} {m n : ℕ} (f : Fin m → Fin n)
    (node : Node Var m) (v : Var → Bool) (g : Fin n → Bool) (h : Fin m → Bool)
    (heq : ∀ j ∈ node.children, g (f j) = h j) :
    (node.map f).evalLocal v (fun j ↦ g j.val) =
      node.evalLocal v (fun j ↦ h j.val) := by
  cases node with
  | const b => rfl
  | lit x b => rfl
  | and children =>
    apply Bool.eq_iff_iff.mpr
    simp only [map, evalLocal_and, Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun j hj ↦ by rw [heq j hj]
  | or children =>
    apply Bool.eq_iff_iff.mpr
    simp only [map, evalLocal_or, Finset.mem_image, exists_exists_and_eq_and]
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [heq j hj]

theorem supportLocal_map {Var : Type} [DecidableEq Var] {m n : ℕ}
    (f : Fin m → Fin n) (node : Node Var m)
    (g : Fin n → Finset Var) (h : Fin m → Finset Var)
    (heq : ∀ j ∈ node.children, g (f j) = h j) :
    (node.map f).supportLocal (fun j ↦ g j.val) =
      node.supportLocal (fun j ↦ h j.val) := by
  cases node with
  | const b => rfl
  | lit x b => rfl
  | and children | or children =>
    simp only [map, supportLocal_and, supportLocal_or]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and]
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [heq j hj]

end Node

namespace Circuit

variable {Var : Type} (C : Circuit Var)

/-- The output together with all positions used as inputs. -/
def usedPositions : Finset (Fin C.nodeCount) :=
  insert C.output (Finset.univ.biUnion fun i ↦ (C.node i).children)

theorem output_mem_usedPositions : C.output ∈ C.usedPositions := by
  simp [usedPositions]

theorem child_mem_usedPositions {i j : Fin C.nodeCount}
    (h : j ∈ (C.node i).children) : j ∈ C.usedPositions := by
  simp only [usedPositions, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  exact Or.inr ⟨i, h⟩

/-- The compact array lists retained positions in increasing order. -/
def compactEnum : Fin C.usedPositions.card ≃o C.usedPositions :=
  C.usedPositions.orderIsoOfFin rfl

/-- Rename a retained position; an unused position defaults to the output. -/
def compactIndex (i : Fin C.nodeCount) : Fin C.usedPositions.card :=
  C.compactEnum.symm (if h : i ∈ C.usedPositions then ⟨i, h⟩
    else ⟨C.output, C.output_mem_usedPositions⟩)

@[simp] theorem compactEnum_compactIndex (i : Fin C.nodeCount)
    (h : i ∈ C.usedPositions) : (C.compactEnum (C.compactIndex i)).val = i := by
  simp [compactIndex, h]

/-- Compact the array while preserving its topological order. -/
abbrev compact : Circuit Var where
  nodeCount := C.usedPositions.card
  node i := (C.node (C.compactEnum i).val).map C.compactIndex
  children_lt := by
    intro i j hj
    rw [Node.children_map, Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    apply C.compactEnum.lt_iff_lt.mp
    change (C.compactEnum (C.compactIndex k)).val < (C.compactEnum i).val
    rw [C.compactEnum_compactIndex k (C.child_mem_usedPositions hk)]
    exact C.children_lt _ _ hk
  output := C.compactIndex C.output

/-- The compact array has at most as many positions as the circuit's size. -/
theorem nodeCount_compact_le_size : C.compact.nodeCount ≤ C.size := by
  change C.usedPositions.card ≤ C.edgeCount + 1
  calc C.usedPositions.card ≤
      (Finset.univ.biUnion fun i ↦ (C.node i).children).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (∑ i, (C.node i).children.card) + 1 :=
      Nat.add_le_add_right (Finset.card_biUnion_le) 1
    _ = C.edgeCount + 1 := rfl

/-- Compaction preserves the value at every retained position. -/
theorem eval_compact (v : Var → Bool) :
    ∀ i, C.compact.eval v i = C.eval v (C.compactEnum i).val := by
  intro i
  induction hr : ((C.compactEnum i).val).val using Nat.strong_induction_on
      generalizing i with
  | h n ih =>
    have child (j : Fin C.nodeCount) (hj : j ∈ (C.node (C.compactEnum i).val).children) :
        C.compact.eval v (C.compactIndex j) = C.eval v j := by
      have hmem := C.child_mem_usedPositions hj
      have hlt := C.children_lt _ _ hj
      have heq := C.compactEnum_compactIndex j hmem
      have h := ih j.val (by simpa [← hr] using hlt) (C.compactIndex j)
        (by rw [heq])
      simpa only [heq] using h
    rw [C.compact.eval_eq, C.eval_eq]
    exact Node.evalLocal_map C.compactIndex _ v _ _ child

/-- Compaction preserves the support at every retained position. -/
theorem support_compact [DecidableEq Var] :
    ∀ i, C.compact.support i = C.support (C.compactEnum i).val := by
  intro i
  induction hr : ((C.compactEnum i).val).val using Nat.strong_induction_on
      generalizing i with
  | h n ih =>
    have child (j : Fin C.nodeCount) (hj : j ∈ (C.node (C.compactEnum i).val).children) :
        C.compact.support (C.compactIndex j) = C.support j := by
      have hmem := C.child_mem_usedPositions hj
      have hlt := C.children_lt _ _ hj
      have heq := C.compactEnum_compactIndex j hmem
      have h := ih j.val (by simpa [← hr] using hlt) (C.compactIndex j)
        (by rw [heq])
      simpa only [heq] using h
    rw [C.compact.support_eq, C.support_eq]
    exact Node.supportLocal_map C.compactIndex _ _ _ child

/-- Compaction preserves the computed Boolean function. -/
theorem compact_computes {f : (Var → Bool) → Bool} (h : C.Computes f) :
    C.compact.Computes f := by
  intro v
  rw [C.eval_compact]
  change C.eval v (C.compactEnum (C.compactIndex C.output)).val = f v
  rw [C.compactEnum_compactIndex C.output C.output_mem_usedPositions]
  exact h v

/-- Compaction preserves disjoint supports at conjunctions. -/
theorem compact_isDNNF [DecidableEq Var] (h : C.IsDNNF) : C.compact.IsDNNF := by
  intro i children hn left hl right hr hne
  change (C.node (C.compactEnum i).val).map C.compactIndex = .and children at hn
  cases hnode : C.node (C.compactEnum i).val <;> simp only [hnode, Node.map] at hn <;> try cases hn
  case and inputs =>
    obtain ⟨l, hlin, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨r, hrin, rfl⟩ := Finset.mem_image.mp hr
    rw [C.support_compact, C.support_compact,
      C.compactEnum_compactIndex l (C.child_mem_usedPositions (i := (C.compactEnum i).val) (by simpa [hnode, Node.children] using hlin)),
      C.compactEnum_compactIndex r (C.child_mem_usedPositions (i := (C.compactEnum i).val) (by simpa [hnode, Node.children] using hrin))]
    exact h _ _ hnode l hlin r hrin (fun heq ↦ hne (congrArg C.compactIndex heq))

/-- A finite-set input list has at most one reference per array position. -/
theorem size_le_two_mul_nodeCount_sq : C.size ≤ 2 * C.nodeCount ^ 2 := by
  have he : C.edgeCount ≤ C.nodeCount * C.nodeCount := by
    calc C.edgeCount ≤ ∑ _i : Fin C.nodeCount, C.nodeCount := by
          apply Finset.sum_le_sum
          intro i _
          exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
      _ = C.nodeCount * C.nodeCount := by simp
  have hp : 0 < C.nodeCount := C.output.pos
  unfold size
  nlinarith

end Circuit
end DDNNFNegation
