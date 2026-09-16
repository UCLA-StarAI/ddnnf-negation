import DDNNFNegationCorollaries.Supporting.ArithmeticCircuits

/-! # Pruning arithmetic circuits for edge-based size bounds -/

namespace DDNNFNegation

namespace ArithCircuit

variable {V : Type*} [DecidableEq V] (C : ArithCircuit V)

/-- A Boolean graph with the same child references; labels are irrelevant. -/
def graphNode : ArithNode V C.Gate → NNFNode Unit C.Gate
  | .add l r => .disj [l, r]
  | .mul l r => .conj l r
  | _ => .top

@[simp] theorem graphNode_child (node : ArithNode V C.Gate) (g : C.Gate) :
    (C.graphNode node).IsChild g ↔ node.IsChild g := by
  cases node <;> simp [graphNode, NNFNode.IsChild, ArithNode.IsChild]

/-- The graph used to identify gates in the output's dependency closure. -/
noncomputable abbrev graph : NNFCircuit Unit :=
  { NNFCircuit.ofNodes (fun g ↦ C.graphNode (C.node g)) C.rank
    (fun g c h ↦ C.child_rank g c ((C.graphNode_child _ _).mp h)) C.output with Gate := C.Gate, gateFintype := C.gateFintype, gateDecidableEq := C.gateDecidableEq }

/-- Each retained arithmetic child is retained by graph pruning. -/
theorem child_reachable (g : C.graph.ReachableGate) {c : C.Gate}
    (hc : (C.node g.val).IsChild c) : C.graph.Reachable c :=
  g.property.child ((C.graphNode_child _ _).mpr hc)

/-- The arithmetic circuit restricted to the output's dependency closure. -/
noncomputable def compact : ArithCircuit V where
  Gate := C.graph.ReachableGate
  gateFintype := Fintype.ofFinite _
  gateDecidableEq := Classical.decEq _
  output := ⟨C.output, C.graph.reachable_output⟩
  node g := (C.node g.val).map C.graph.toReachable
  rank g := C.rank g.val
  child_rank := by
    intro g c hc
    cases hn : C.node g.val with
    | const k | var x => simp [hn, ArithNode.map, ArithNode.IsChild] at hc
    | add l r | mul l r =>
      simp only [hn, ArithNode.map, ArithNode.IsChild] at hc
      rcases hc with rfl | rfl
      · rw [C.graph.toReachable_of_reachable (C.child_reachable g (by simp [hn, ArithNode.IsChild]))]
        change C.rank l < C.rank g.val
        exact C.child_rank _ _ (by simp [hn, ArithNode.IsChild])
      · rw [C.graph.toReachable_of_reachable (C.child_reachable g (by simp [hn, ArithNode.IsChild]))]
        change C.rank r < C.rank g.val
        exact C.child_rank _ _ (by simp [hn, ArithNode.IsChild])
  poly g := C.poly g.val
  poly_eq := by
    intro g
    rw [C.poly_eq]
    cases hn : C.node g.val with
    | const k | var x => rfl
    | add l r | mul l r =>
      have hl := C.graph.toReachable_of_reachable (C.child_reachable g (c := l) (by simp [hn, ArithNode.IsChild]))
      have hr := C.graph.toReachable_of_reachable (C.child_reachable g (c := r) (by simp [hn, ArithNode.IsChild]))
      simp [ArithNode.map, ArithNode.eval, hl, hr]
  vars g := C.vars g.val
  vars_eq := by
    intro g
    rw [C.vars_eq]
    cases hn : C.node g.val with
    | const k | var x => rfl
    | add l r | mul l r =>
      have hl := C.graph.toReachable_of_reachable (C.child_reachable g (c := l) (by simp [hn, ArithNode.IsChild]))
      have hr := C.graph.toReachable_of_reachable (C.child_reachable g (c := r) (by simp [hn, ArithNode.IsChild]))
      simp [ArithNode.map, ArithNode.Vars, hl, hr]

/-- Compaction preserves the polynomial at the output. -/
@[simp] theorem compact_poly : C.compact.poly C.compact.output = C.poly C.output := rfl

/-- Compaction preserves nonnegative constants. -/
theorem compact_isMonotone (h : C.IsMonotone) : C.compact.IsMonotone := by
  intro g k hk
  change (C.node g.val).map C.graph.toReachable = .const k at hk
  cases hn : C.node g.val <;> simp only [hn, ArithNode.map] at hk <;> try cases hk
  exact h _ _ hn

/-- The retained gate count is bounded by edges plus one. -/
theorem compact_nodeCount_le_size : C.compact.nodeCount ≤ C.size := by
  have he : C.graph.edgeCount = ∑ g, (C.node g).fanIn := by
    apply Finset.sum_congr rfl
    intro g _
    change (C.graphNode (C.node g)).fanIn = _
    cases C.node g <;> rfl
  calc C.compact.nodeCount = C.graph.prune.nodeCount := Fintype.card_congr (Equiv.refl _)
    _ ≤ C.graph.prune.edgeCount + 1 := C.graph.prune_nodeCount_le
    _ ≤ C.graph.edgeCount + 1 := Nat.add_le_add_right C.graph.edgeCount_prune_le 1
    _ = C.size := by rw [he]; rfl

/-- Pruning preserves disjoint position sets at products. -/
theorem compact_isPairDisjoint {N : ℕ} (A : ArithCircuit (Fin N × Bool))
    (h : A.IsPairDisjoint) : A.compact.IsPairDisjoint := by
  intro g l r hn
  change (A.node g.val).map A.graph.toReachable = .mul l r at hn
  cases hg : A.node g.val <;> simp only [hg, ArithNode.map] at hn <;> try cases hn
  case mul a b =>
    have ha := A.graph.toReachable_of_reachable
      (A.child_reachable g (c := a) (by simp [hg, ArithNode.IsChild]))
    have hb := A.graph.toReachable_of_reachable
      (A.child_reachable g (c := b) (by simp [hg, ArithNode.IsChild]))
    change Disjoint (positions (A.vars (A.graph.toReachable a).val))
      (positions (A.vars (A.graph.toReachable b).val))
    rw [ha, hb]
    exact h _ _ _ hg

end ArithCircuit
end DDNNFNegation
