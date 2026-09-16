import DDNNFNegation.CircuitPreprocessing

/-!
# Keeping the output's dependency closure

Follow input references from the output and retain precisely the gates
encountered. Pruning preserves the output function, decomposability, and
determinism and cannot increase either size measure. The retained graph
has at most one more node than edges, which relates the two internal
size bounds.
-/

namespace DDNNFNegation

open Finset

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

/-- One dependency step from a gate to one of its inputs. -/
def Step (C : NNFCircuit Var) (parent child : C.Gate) : Prop :=
  (C.node parent).IsChild child

/-- Gates reached by following input references from the output. -/
def Reachable (C : NNFCircuit Var) (gate : C.Gate) : Prop :=
  Relation.ReflTransGen C.Step C.output gate

/-- The output is retained by pruning. -/
theorem reachable_output (C : NNFCircuit Var) : C.Reachable C.output :=
  Relation.ReflTransGen.refl

/-- Every child of a retained gate is retained, so pruning preserves all references needed
at the output. -/
theorem Reachable.child {C : NNFCircuit Var} {parent child : C.Gate}
    (h : C.Reachable parent) (hchild : (C.node parent).IsChild child) :
    C.Reachable child :=
  h.tail hchild

/-- The gates of the pruned circuit. -/
abbrev ReachableGate (C : NNFCircuit Var) := {gate : C.Gate // C.Reachable gate}

noncomputable instance (C : NNFCircuit Var) : Fintype C.ReachableGate :=
  Fintype.ofFinite _

open Classical in
/-- A gate's copy in the pruned circuit.  An unreachable gate, which is
never the input of a reachable gate, is sent to the output. -/
noncomputable def toReachable (C : NNFCircuit Var) (gate : C.Gate) :
    C.ReachableGate :=
  if h : C.Reachable gate then ⟨gate, h⟩ else ⟨C.output, C.reachable_output⟩

/-- On a retained gate, the pruning map is its inclusion in the retained gate type. -/
theorem toReachable_of_reachable (C : NNFCircuit Var) {gate : C.Gate}
    (h : C.Reachable gate) : C.toReachable gate = ⟨gate, h⟩ := by
  unfold toReachable
  exact dif_pos h

/-- The node of a reachable gate, with its inputs renamed. -/
noncomputable def pruneNode (C : NNFCircuit Var) (gate : C.ReachableGate) :
    NNFNode Var C.ReachableGate :=
  (C.node gate.1).map C.toReachable

/-- A child still has smaller rank after restricting to reachable gates. -/
theorem prune_child_rank (C : NNFCircuit Var) :
    ∀ gate child, (C.pruneNode gate).IsChild child →
      C.rank child.1 < C.rank gate.1 := by
  intro gate child hchild
  obtain ⟨source, hsource, rfl⟩ :=
    NNFNode.isChild_map_exists _ _ _ hchild
  rw [C.toReachable_of_reachable (gate.2.child hsource)]
  exact C.child_rank gate.1 source hsource

/-- The circuit restricted to the gates that can reach the output. -/
noncomputable def prune (C : NNFCircuit Var) : NNFCircuit Var :=
  ofNodes C.pruneNode (fun gate ↦ C.rank gate.1) C.prune_child_rank
    ⟨C.output, C.reachable_output⟩

/-- Every retained gate has its original Boolean value. -/
theorem prune_semantics (C : NNFCircuit Var) :
    ∀ (gate : C.ReachableGate) (v : Var → Bool),
      C.prune.semantics gate v ↔ C.semantics gate.1 v := by
  suffices key : ∀ n, ∀ gate : C.ReachableGate, C.rank gate.1 < n →
      ∀ v, (C.prune.semantics gate v ↔ C.semantics gate.1 v) from
    fun gate v ↦ key _ gate (Nat.lt_succ_self _) v
  intro n
  induction n with
  | zero =>
      intro gate h
      exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro gate hgate v
      rw [C.prune.semantics_eq gate v, C.semantics_eq gate.1 v]
      refine (NNFNode.holds_map (C.node gate.1) C.toReachable v _).trans ?_
      apply NNFNode.holds_congr
      intro child hchild
      rw [C.toReachable_of_reachable (gate.2.child hchild)]
      exact ih ⟨child, gate.2.child hchild⟩
        (by show C.rank child < n; have := C.child_rank gate.1 child hchild; omega) v

/-- Every retained gate has its original variable support. -/
theorem prune_support (C : NNFCircuit Var) :
    ∀ gate : C.ReachableGate, C.prune.support gate = C.support gate.1 := by
  suffices key : ∀ n, ∀ gate : C.ReachableGate, C.rank gate.1 < n →
      C.prune.support gate = C.support gate.1 from
    fun gate ↦ key _ gate (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero =>
      intro gate h
      exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro gate hgate
      rw [C.prune.support_eq gate, C.support_eq gate.1]
      refine (NNFNode.support_map (C.node gate.1) C.toReachable _).trans ?_
      apply NNFNode.support_congr
      intro child hchild
      rw [C.toReachable_of_reachable (gate.2.child hchild)]
      exact ih ⟨child, gate.2.child hchild⟩
        (by show C.rank child < n; have := C.child_rank gate.1 child hchild; omega)

/-- Deleting gates outside the output dependency graph preserves the computed function. -/
theorem prune_computes (C : NNFCircuit Var) {f : (Var → Bool) → Prop}
    (h : C.Computes f) : C.prune.Computes f :=
  fun v ↦ (C.prune_semantics ⟨C.output, C.reachable_output⟩ v).trans (h v)

/-- Pruning preserves disjoint supports at conjunctions. -/
theorem prune_isDecomposable (C : NNFCircuit Var) (h : C.IsDecomposable) :
    C.prune.IsDecomposable := by
  intro gate left right hnode
  change (C.node gate.1).map C.toReachable = .conj left right at hnode
  cases hn : C.node gate.1 with
  | conj a b =>
      rw [hn] at hnode
      simp only [NNFNode.map] at hnode
      obtain ⟨rfl, rfl⟩ := hnode
      have ha : (C.node gate.1).IsChild a := by rw [hn]; exact Or.inl rfl
      have hb : (C.node gate.1).IsChild b := by rw [hn]; exact Or.inr rfl
      rw [C.toReachable_of_reachable (gate.2.child ha),
        C.toReachable_of_reachable (gate.2.child hb)]
      have ha' := C.prune_support ⟨a, gate.2.child ha⟩
      have hb' := C.prune_support ⟨b, gate.2.child hb⟩
      rw [ha', hb']
      exact h gate.1 a b hn
  | top => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | bot => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | pos x => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | neg x => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | disj children => rw [hn] at hnode; simp [NNFNode.map] at hnode

/-- Pruning preserves mutual exclusion at disjunctions. -/
theorem prune_isDeterministic (C : NNFCircuit Var) (h : C.IsDeterministic) :
    C.prune.IsDeterministic := by
  intro gate children hnode left hleft right hright hne v
  change (C.node gate.1).map C.toReachable = .disj children at hnode
  cases hn : C.node gate.1 with
  | disj cs =>
      rw [hn] at hnode
      simp only [NNFNode.map] at hnode
      injection hnode with hnode
      subst hnode
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hleft
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hright
      have hca : (C.node gate.1).IsChild a := by rw [hn]; exact ha
      have hcb : (C.node gate.1).IsChild b := by rw [hn]; exact hb
      rw [C.toReachable_of_reachable (gate.2.child hca),
        C.toReachable_of_reachable (gate.2.child hcb)] at hne ⊢
      have ha' := C.prune_semantics ⟨a, gate.2.child hca⟩ v
      have hb' := C.prune_semantics ⟨b, gate.2.child hcb⟩ v
      rw [ha', hb']
      exact h gate.1 cs hn a ha b hb (fun hab ↦ hne (by subst hab; rfl)) v
  | top => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | bot => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | pos x => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | neg x => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | conj a b => rw [hn] at hnode; simp [NNFNode.map] at hnode

/-- Pruning preserves the deterministic DNNF class. -/
theorem prune_isDeterministicDNNF (C : NNFCircuit Var)
    (h : C.IsDeterministicDNNF) : C.prune.IsDeterministicDNNF :=
  ⟨C.prune_isDecomposable h.1, C.prune_isDeterministic h.2⟩

/-- Pruning preserves the DNNF class. -/
theorem prune_isDNNF (C : NNFCircuit Var) (h : C.IsDNNF) : C.prune.IsDNNF :=
  C.prune_isDecomposable h

/-- Deleting unreachable gates preserves the fan-in-two condition. -/
theorem prune_isFanInTwo (C : NNFCircuit Var) (h : C.IsFanInTwo) :
    C.prune.IsFanInTwo := by
  intro gate children hnode
  change (C.node gate.1).map C.toReachable = .disj children at hnode
  cases hn : C.node gate.1 with
  | disj cs =>
      rw [hn] at hnode
      simp only [NNFNode.map] at hnode
      injection hnode with hnode
      subst hnode
      exact (List.length_map _).trans_le (h gate.1 cs hn)
  | top => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | bot => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | pos x => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | neg x => rw [hn] at hnode; simp [NNFNode.map] at hnode
  | conj a b => rw [hn] at hnode; simp [NNFNode.map] at hnode

/-- Pruning removes edges only. -/
theorem edgeCount_prune_le (C : NNFCircuit Var) :
    C.prune.edgeCount ≤ C.edgeCount := by
  classical
  unfold edgeCount
  change ∑ gate : C.ReachableGate, ((C.node gate.1).map C.toReachable).fanIn ≤
    ∑ gate : C.Gate, (C.node gate).fanIn
  simp only [NNFNode.fanIn_map]
  rw [← Finset.sum_subtype (univ.filter fun gate ↦ C.Reachable gate) (by simp)
    (fun gate ↦ (C.node gate).fanIn)]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- In the pruned circuit every gate other than the output is the input of
some gate, so there are at most one more gate than edges. -/
theorem prune_nodeCount_le (C : NNFCircuit Var) :
    C.prune.nodeCount ≤ C.prune.edgeCount + 1 := by
  apply nodeCount_le_edgeCount_add_one
  intro gate hgate
  rcases Relation.ReflTransGen.cases_tail gate.2 with heq | ⟨parent, hparent, hstep⟩
  · exact absurd (Subtype.ext heq) hgate
  · refine ⟨⟨parent, hparent⟩, ?_⟩
    change ((C.node parent).map C.toReachable).IsChild gate
    have hgate' : C.toReachable gate.1 = gate := C.toReachable_of_reachable gate.2
    rw [← hgate']
    exact NNFNode.isChild_map _ hstep

/-- Removing unreachable nodes bounds the retained node count by the original size. -/
theorem prune_nodeCount_le_size (C : NNFCircuit Var) : C.prune.nodeCount ≤ C.size :=
  C.prune_nodeCount_le.trans (Nat.add_le_add_right C.edgeCount_prune_le 1)

end NNFCircuit

end DDNNFNegation
