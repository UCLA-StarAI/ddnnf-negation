import DDNNFNegationCorollaries.Supporting.ProbabilisticCircuit
import DDNNFNegationCorollaries.Supporting.ArithmeticCircuits

/-!
# A support translation preserving edge-based size

A Boolean univariate leaf has one of four supports, each represented by a
single constant or literal. Thus translating positivity needs no extra
edges at leaves, including a zero-edge circuit.
-/

namespace DDNNFNegation

namespace ProbCircuit

variable {N : ℕ} (P : ProbCircuit (Fin N))

/-- Translate a univariate support to one Boolean node. -/
noncomputable def smallSupportNode : PCNode (Fin N) P.Gate → NNFNode (Fin N) P.Gate
  | .leaf v h => if 0 < h false then (if 0 < h true then .top else .neg v)
      else (if 0 < h true then .pos v else .bot)
  | .const c => if 0 < c then .top else .bot
  | .scale c g => if 0 < c then .disj [g] else .bot
  | .add l r => .disj [l, r]
  | .mul l r => .conj l r

/-- The support translation introduces no child references. -/
theorem smallSupportNode_child (node : PCNode (Fin N) P.Gate) (c : P.Gate) :
    (P.smallSupportNode node).IsChild c → node.IsChild c := by
  cases node <;> simp only [smallSupportNode] <;>
    (try split_ifs) <;> simp_all [NNFNode.IsChild, PCNode.IsChild]

/-- Boolean support on the original gate set. -/
noncomputable abbrev toSmallDNNF : NNFCircuit (Fin N) :=
  { NNFCircuit.ofNodes (fun g ↦ P.smallSupportNode (P.node g)) P.rank
    (fun g c h ↦ P.child_rank g c (P.smallSupportNode_child _ _ h)) P.output with Gate := P.Gate }

/-- Every translated gate is true exactly where its original value is positive. -/
theorem toSmallDNNF_semantics (hnn : P.IsNonneg) (g : P.Gate) (x : Fin N → Bool) :
    P.toSmallDNNF.semantics g x ↔ 0 < P.value g x := by
  induction g using P.induction_rank with
  | _ g ih =>
    rw [P.toSmallDNNF.semantics_eq, P.value_eq]
    change (P.smallSupportNode (P.node g)).Holds x _ ↔ _
    cases hg : P.node g with
    | leaf v h =>
      simp only [smallSupportNode, PCNode.eval]
      split_ifs <;> cases hx : x v <;> simp_all [NNFNode.Holds]
    | const c =>
      simp only [smallSupportNode, PCNode.eval]
      split_ifs <;> simp_all [NNFNode.Holds]
    | scale c k =>
      have hk := ih k (by rw [hg]; rfl)
      have hc : 0 ≤ c := by simpa [hg, PCNode.IsNonneg] using hnn g
      have hv := P.value_nonneg hnn k x
      simp only [smallSupportNode, PCNode.eval]
      split_ifs with hpos
      · change (∃ j ∈ [k], P.toSmallDNNF.semantics j x) ↔ 0 < c * P.value k x
        simp only [List.mem_singleton, exists_eq_left]
        exact hk.trans (by simpa only [hpos, true_and] using
          (ArithCircuit.pos_mul_iff_of_nonneg hc hv).symm)
      · have hc0 : c = 0 := by linarith
        simp [NNFNode.Holds, hc0]
    | add l r =>
      have hl := ih l (by rw [hg]; exact Or.inl rfl)
      have hr := ih r (by rw [hg]; exact Or.inr rfl)
      change (∃ j ∈ [l, r], P.toSmallDNNF.semantics j x) ↔ 0 < P.value l x + P.value r x
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
      exact (or_congr hl hr).trans
        (ArithCircuit.pos_add_iff_of_nonneg (P.value_nonneg hnn l x) (P.value_nonneg hnn r x)).symm
    | mul l r =>
      have hl := ih l (by rw [hg]; exact Or.inl rfl)
      have hr := ih r (by rw [hg]; exact Or.inr rfl)
      change (P.toSmallDNNF.semantics l x ∧ P.toSmallDNNF.semantics r x) ↔ 0 < P.value l x * P.value r x
      exact (and_congr hl hr).trans
        (ArithCircuit.pos_mul_iff_of_nonneg (P.value_nonneg hnn l x) (P.value_nonneg hnn r x)).symm

/-- Boolean support uses a subset of the original variable scope. -/
theorem toSmallDNNF_support_subset (g : P.Gate) :
    P.toSmallDNNF.support g ⊆ P.scope g := by
  induction g using P.induction_rank with
  | _ g ih =>
    rw [P.toSmallDNNF.support_eq, P.scope_eq]
    change (P.smallSupportNode (P.node g)).Support _ ⊆ _
    cases hg : P.node g with
    | leaf v h =>
      simp only [smallSupportNode]
      split_ifs <;> simp [NNFNode.Support, PCNode.Scope]
    | const c =>
      simp only [smallSupportNode]
      split_ifs <;> simp [NNFNode.Support]
    | scale c k =>
      simp only [smallSupportNode]
      split_ifs
      · simp only [NNFNode.Support, List.foldl_cons, List.foldl_nil,
          Finset.empty_union, PCNode.Scope]
        exact ih k (by rw [hg]; rfl)
      · simp [NNFNode.Support]
    | add l r | mul l r =>
      have hl := ih l (by rw [hg]; exact Or.inl rfl)
      have hr := ih r (by rw [hg]; exact Or.inr rfl)
      simpa [smallSupportNode, NNFNode.Support, PCNode.Scope] using
        Finset.union_subset_union hl hr

/-- Positivity preserves decomposability. -/
theorem toSmallDNNF_isDNNF (hdec : P.IsDecomposable) : P.toSmallDNNF.IsDNNF := by
  intro g l r hn
  change P.smallSupportNode (P.node g) = .conj l r at hn
  cases hg : P.node g with
  | leaf v h => rw [hg] at hn; simp only [smallSupportNode] at hn; split_ifs at hn
  | const c => rw [hg] at hn; simp only [smallSupportNode] at hn; split_ifs at hn
  | scale c k => rw [hg] at hn; simp only [smallSupportNode] at hn; split_ifs at hn
  | add a b => rw [hg] at hn; cases hn
  | mul a b =>
    rw [hg] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact Finset.disjoint_of_subset_left (P.toSmallDNNF_support_subset l)
      (Finset.disjoint_of_subset_right (P.toSmallDNNF_support_subset r) (hdec g l r hg))

/-- The direct support translation cannot increase size. -/
theorem toSmallDNNF_size_le : P.toSmallDNNF.size ≤ P.size := by
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro g _
  change (P.smallSupportNode (P.node g)).fanIn ≤ (P.node g).fanIn
  cases P.node g <;> simp only [smallSupportNode] <;>
    (try split_ifs) <;> simp [NNFNode.fanIn, PCNode.fanIn]

end ProbCircuit
end DDNNFNegation
