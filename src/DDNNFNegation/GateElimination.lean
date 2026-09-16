import DDNNFNegation.RectangleExtraction
import DDNNFNegation.Binarization
import DDNNFNegation.Prune
import TutorialBox

/-!
# Rectangle covers by gate elimination

This is the gate-elimination argument underlying the rectangle-cover bound
of Bova, Capelli, Mengel, and Slivovsky, Theorem 6. For a circuit of fan-in
at most two, descend through supports to find a balanced rectangle. Setting
the selected gate to false removes the assignments covered by that
rectangle and decreases the number of nonfalse gates. Induction gives a
cover indexed by gates.

Pruning and binarization yield the internal edge-count bound
`rectangle_cover`. The paper's edges-plus-one conclusion is
`balanced_rectangle_cover` in `RectangleReduction.lean`.
-/

namespace DDNNFNegation

open Finset

noncomputable section

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

/-! ### Relabeling a gate by the constant false -/

/-- The circuit with gate `g` relabeled by the constant false. -/
def eliminate (C : NNFCircuit Var) (g : C.Gate) : NNFCircuit Var :=
  ofNodes (fun h ↦ if h = g then .bot else C.node h) C.rank
    (by
      intro gate child hchild
      by_cases hg : gate = g
      · rw [if_pos hg] at hchild
        exact hchild.elim
      · rw [if_neg hg] at hchild
        exact C.child_rank gate child hchild)
    C.output

/-- Eliminating a gate replaces that gate by false. -/
theorem eliminate_node_self (C : NNFCircuit Var) (g : C.Gate) :
    (C.eliminate g).node g = .bot := if_pos rfl

/-- Eliminating a gate leaves every other node description unchanged. -/
theorem eliminate_node_of_ne (C : NNFCircuit Var) {g h : C.Gate} (hne : h ≠ g) :
    (C.eliminate g).node h = C.node h := if_neg hne

/-- Truth in the eliminated circuit implies truth in the original. -/
theorem eliminate_semantics_imp (C : NNFCircuit Var) (g : C.Gate) :
    ∀ (h : C.Gate) (v : Var → Bool), (C.eliminate g).semantics h v → C.semantics h v := by
  suffices key : ∀ n, ∀ h : C.Gate, C.rank h < n → ∀ v,
      (C.eliminate g).semantics h v → C.semantics h v from
    fun h v ↦ key _ h (Nat.lt_succ_self _) v
  intro n
  induction n with
  | zero =>
      intro h hn
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
      intro h hn v hsem
      rw [(C.eliminate g).semantics_eq h v] at hsem
      rw [C.semantics_eq h v]
      by_cases hg : h = g
      · rw [hg, C.eliminate_node_self g] at hsem
        exact hsem.elim
      · rw [C.eliminate_node_of_ne hg] at hsem
        exact NNFNode.holds_mono v (C.node h)
          (fun c hc ↦ ih c (by have := C.child_rank h c hc; omega) v) hsem

/-- Supports can only shrink under elimination. -/
theorem eliminate_support_subset (C : NNFCircuit Var) (g : C.Gate) :
    ∀ h : C.Gate, (C.eliminate g).support h ⊆ C.support h := by
  suffices key : ∀ n, ∀ h : C.Gate, C.rank h < n →
      (C.eliminate g).support h ⊆ C.support h from
    fun h ↦ key _ h (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero =>
      intro h hn
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
      intro h hn
      rw [(C.eliminate g).support_eq h, C.support_eq h]
      by_cases hg : h = g
      · rw [hg, C.eliminate_node_self g]
        exact Finset.empty_subset _
      · rw [C.eliminate_node_of_ne hg]
        exact NNFNode.support_mono (C.node h)
          (fun c hc ↦ ih c (by have := C.child_rank h c hc; omega))

/-- Replacing one gate by false preserves disjoint conjunction supports. -/
theorem eliminate_isDecomposable (C : NNFCircuit Var) (g : C.Gate)
    (h : C.IsDecomposable) : (C.eliminate g).IsDecomposable := by
  intro gate left right hnode
  by_cases hg : gate = g
  · rw [hg, C.eliminate_node_self g] at hnode
    cases hnode
  · rw [C.eliminate_node_of_ne hg] at hnode
    exact Finset.disjoint_of_subset_left (C.eliminate_support_subset g left)
      (Finset.disjoint_of_subset_right (C.eliminate_support_subset g right)
        (h gate left right hnode))

/-- Replacing one gate by false cannot increase fan-in. -/
theorem eliminate_isFanInTwo (C : NNFCircuit Var) (g : C.Gate)
    (h : C.IsFanInTwo) : (C.eliminate g).IsFanInTwo := by
  intro gate children hnode
  by_cases hg : gate = g
  · rw [hg, C.eliminate_node_self g] at hnode
    cases hnode
  · rw [C.eliminate_node_of_ne hg] at hnode
    exact h gate children hnode

/-- **Gate elimination.**  An assignment satisfying a gate either satisfies
`g` together with an outside context from `g` up to that gate, or still
satisfies the gate after `g` is relabeled false. -/
theorem semantics_eliminate_or_context (C : NNFCircuit Var) (g : C.Gate) :
    ∀ (h : C.Gate) (v : Var → Bool), C.semantics h v →
      (C.semantics g v ∧ C.HasContext g v h) ∨ (C.eliminate g).semantics h v := by
  suffices key : ∀ n, ∀ h : C.Gate, C.rank h < n → ∀ v, C.semantics h v →
      (C.semantics g v ∧ C.HasContext g v h) ∨ (C.eliminate g).semantics h v from
    fun h v ↦ key _ h (Nat.lt_succ_self _) v
  intro n
  induction n with
  | zero =>
      intro h hn
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
      intro h hn v hsem
      by_cases hg : h = g
      · subst hg
        exact Or.inl ⟨hsem, .here⟩
      rw [(C.eliminate g).semantics_eq h v, C.eliminate_node_of_ne hg]
      rw [C.semantics_eq h v] at hsem
      cases hnode : C.node h with
      | top => exact Or.inr trivial
      | bot =>
          rw [hnode] at hsem
          exact hsem.elim
      | pos x =>
          rw [hnode] at hsem
          exact Or.inr hsem
      | neg x =>
          rw [hnode] at hsem
          exact Or.inr hsem
      | conj left right =>
          rw [hnode] at hsem
          obtain ⟨hl, hr⟩ := hsem
          have hlrank : C.rank left < n := by
            have := C.child_rank h left (by rw [hnode]; exact Or.inl rfl)
            omega
          have hrrank : C.rank right < n := by
            have := C.child_rank h right (by rw [hnode]; exact Or.inr rfl)
            omega
          rcases ih left hlrank v hl with ⟨hgsem, hctx⟩ | hl'
          · exact Or.inl ⟨hgsem, .conjLeft hnode hctx hr⟩
          rcases ih right hrrank v hr with ⟨hgsem, hctx⟩ | hr'
          · exact Or.inl ⟨hgsem, .conjRight hnode hl hctx⟩
          exact Or.inr ⟨hl', hr'⟩
      | disj children =>
          rw [hnode] at hsem
          obtain ⟨c, hc, hcsem⟩ := hsem
          have hcrank : C.rank c < n := by
            have := C.child_rank h c (by rw [hnode]; exact hc)
            omega
          rcases ih c hcrank v hcsem with ⟨hgsem, hctx⟩ | hc'
          · exact Or.inl ⟨hgsem, .disj hnode hc hctx⟩
          · exact Or.inr ⟨c, hc, hc'⟩

/-! ### Counting the gates that are not the constant false -/

open Classical in
/-- The number of gates of a node map that are not the constant false. -/
def liveCountOf {Gate : Type*} [Fintype Gate] (node : Gate → NNFNode Var Gate) : ℕ :=
  (univ.filter fun h ↦ node h ≠ .bot).card

/-- The number of gates that are not the constant false. -/
def liveCount (C : NNFCircuit Var) : ℕ := liveCountOf C.node

open Classical in
/-- The number of non-false gates is at most the circuit's total gate count. -/
theorem liveCount_le_nodeCount (C : NNFCircuit Var) : C.liveCount ≤ C.nodeCount := by
  unfold liveCount liveCountOf nodeCount
  exact (Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ)

open Classical in
/-- An output node other than the false constant witnesses a positive live count. -/
theorem liveCount_pos (C : NNFCircuit Var) (h : C.node C.output ≠ .bot) :
    0 < C.liveCount := by
  unfold liveCount liveCountOf
  exact Finset.card_pos.mpr ⟨C.output, by simpa using h⟩

/-- The live-count measure after elimination is the measure evaluated with the selected gate
forced false. -/
theorem liveCount_eliminate (C : NNFCircuit Var) (g : C.Gate) :
    (C.eliminate g).liveCount = liveCountOf (fun h ↦ if h = g then .bot else C.node h) :=
  rfl

omit [DecidableEq Var] in
open Classical in
/-- Forcing a previously non-false gate to false strictly decreases the live-count measure. -/
theorem liveCountOf_lt {Gate : Type*} [Fintype Gate] [DecidableEq Gate]
    (node : Gate → NNFNode Var Gate) (g : Gate) (hg : node g ≠ .bot) :
    liveCountOf (fun h ↦ if h = g then .bot else node h) < liveCountOf node := by
  unfold liveCountOf
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨g, ?_, ?_⟩
    · simpa using hg
    · simp
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    by_cases hhg : h = g
    · rw [if_pos hhg] at hh
      exact absurd rfl hh
    · rw [if_neg hhg] at hh
      exact hh

/-- Eliminating a node other than the false constant decreases the induction measure. -/
theorem liveCount_eliminate_lt (C : NNFCircuit Var) (g : C.Gate) (hg : C.node g ≠ .bot) :
    (C.eliminate g).liveCount < C.liveCount := by
  rw [liveCount_eliminate]
  exact liveCountOf_lt C.node g hg

/-! ### Descent to a gate with balanced support -/

variable [Fintype Var]

/-- In a fan-in-two circuit, a gate with large support has an input carrying
at least half of its support. -/
theorem exists_child_support_half (C : NNFCircuit Var) (hVar : 2 ≤ Fintype.card Var)
    (hfan : C.IsFanInTwo) (g : C.Gate) (hlarge : C.HasLargeSupport g) :
    ∃ c, (C.node g).IsChild c ∧ (C.support g).card ≤ 2 * (C.support c).card := by
  change 2 * Fintype.card Var < 3 * (C.support g).card at hlarge
  rw [C.support_eq g] at hlarge ⊢
  cases hnode : C.node g with
  | top =>
      rw [hnode] at hlarge
      simp [NNFNode.Support] at hlarge
  | bot =>
      rw [hnode] at hlarge
      simp [NNFNode.Support] at hlarge
  | pos x =>
      rw [hnode] at hlarge
      simp [NNFNode.Support] at hlarge
      omega
  | neg x =>
      rw [hnode] at hlarge
      simp [NNFNode.Support] at hlarge
      omega
  | conj left right =>
      rw [hnode] at hlarge
      simp only [NNFNode.Support] at hlarge ⊢
      have hcard := Finset.card_union_le (C.support left) (C.support right)
      by_cases hl : (C.support right).card ≤ (C.support left).card
      · exact ⟨left, Or.inl rfl, by omega⟩
      · exact ⟨right, Or.inr rfl, by omega⟩
  | disj children =>
      rw [hnode] at hlarge
      have hlen := hfan g children hnode
      rcases children with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · simp [NNFNode.Support] at hlarge
      · refine ⟨a, List.mem_singleton_self a, ?_⟩
        simp only [NNFNode.Support, List.foldl_cons, List.foldl_nil, Finset.empty_union]
        omega
      · simp only [NNFNode.Support, List.foldl_cons, List.foldl_nil,
          Finset.empty_union] at hlarge ⊢
        have hcard := Finset.card_union_le (C.support a) (C.support b)
        by_cases hab : (C.support b).card ≤ (C.support a).card
        · exact ⟨a, by simp [NNFNode.IsChild], by omega⟩
        · exact ⟨b, by simp [NNFNode.IsChild], by omega⟩
      · simp at hlen

/-- Descent from a gate with large support reaches a gate with balanced
support. -/
theorem exists_balanced_below_of_large (C : NNFCircuit Var)
    (hVar : 2 ≤ Fintype.card Var) (hfan : C.IsFanInTwo) :
    ∀ g, C.HasLargeSupport g → ∃ h, C.HasBalancedSupport h := by
  suffices key : ∀ n, ∀ g : C.Gate, C.rank g < n → C.HasLargeSupport g →
      ∃ h, C.HasBalancedSupport h from
    fun g ↦ key _ g (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero =>
      intro g hn
      exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
      intro g hn hlarge
      obtain ⟨c, hc, hhalf⟩ := C.exists_child_support_half hVar hfan g hlarge
      have hcsmall : ¬ C.HasSmallSupport c := by
        change ¬ 3 * (C.support c).card < Fintype.card Var
        change 2 * Fintype.card Var < 3 * (C.support g).card at hlarge
        omega
      by_cases hclarge : C.HasLargeSupport c
      · exact ih c (by have := C.child_rank g c hc; omega) hclarge
      · exact ⟨c, C.hasBalancedSupport_of_not_small_not_large c hcsmall hclarge⟩

/-- A set holding at most two thirds of the variables lies in a balanced
cut. -/
theorem exists_balanced_superset_of_not_large (hVar : 2 ≤ Fintype.card Var)
    {S : Finset Var} (hS : 3 * S.card ≤ 2 * Fintype.card Var) :
    ∃ cut : Finset Var, S ⊆ cut ∧ IsBalanced cut := by
  by_cases hsmall : 3 * S.card < Fintype.card Var
  · exact exists_balanced_superset_of_small hVar hsmall
  · refine ⟨S, Finset.Subset.rfl, ?_, ?_⟩
    · omega
    · rw [Finset.card_compl]
      have := Finset.card_le_univ S
      omega

/-- The satisfying set of the output as one rectangle over a padded cut. -/
def outputRectangle (C : NNFCircuit Var) (cut : Finset Var) : BooleanRectangle Var :=
  separatedRectangle cut (C.semantics C.output) (fun _ ↦ True)

/-- The rectangle at the output gate consists exactly of its satisfying assignments. -/
theorem mem_outputRectangle_iff (C : NNFCircuit Var) {cut : Finset Var}
    (hcut : C.support C.output ⊆ cut) (v : Var → Bool) :
    v ∈ (C.outputRectangle cut).assignments ↔ C.semantics C.output v := by
  unfold outputRectangle
  rw [mem_separatedRectangle_iff _ _ _ ?_ (fun _ _ _ ↦ Iff.rfl)]
  · simp
  · intro v w hagree
    exact C.semantics_congr_of_eqOn_support _ v w (fun x hx ↦ hagree x (hcut hx))

/-! ### The cover -/

/-- **The balanced rectangle cover of a fan-in-two DNNF**, by gate
elimination: at most one rectangle per gate that is not the constant
false. -/
theorem exists_balancedRectangleCover_of_fanInTwo (hVar : 2 ≤ Fintype.card Var) :
    ∀ (k : ℕ) (C : NNFCircuit Var), C.liveCount ≤ k → C.IsDecomposable → C.IsFanInTwo →
      ∃ (r : ℕ) (R : Fin r → BooleanRectangle Var), r ≤ C.liveCount ∧
        (∀ j, (R j).IsBalanced) ∧
        (∀ j v, v ∈ (R j).assignments → C.semantics C.output v) ∧
        (∀ v, C.semantics C.output v → ∃ j, v ∈ (R j).assignments) := by
  intro k
  induction k with
  | zero =>
      intro C hk hdecomp hfan
      refine ⟨0, Fin.elim0, Nat.zero_le _, fun j ↦ j.elim0, fun j ↦ j.elim0, ?_⟩
      intro v hv
      exfalso
      have hbot : C.node C.output = .bot := by
        by_contra hne
        have := C.liveCount_pos hne
        omega
      rw [C.semantics_eq, hbot] at hv
      exact hv
  | succ k ih =>
      intro C hk hdecomp hfan
      by_cases hbot : C.node C.output = .bot
      · refine ⟨0, Fin.elim0, Nat.zero_le _, fun j ↦ j.elim0, fun j ↦ j.elim0, ?_⟩
        intro v hv
        rw [C.semantics_eq, hbot] at hv
        exact hv.elim
      by_cases hlarge : C.HasLargeSupport C.output
      · obtain ⟨h, hbal⟩ := C.exists_balanced_below_of_large hVar hfan C.output hlarge
        have hhbot : C.node h ≠ .bot := by
          intro hh
          have hsupp : C.support h = ∅ := by
            rw [C.support_eq, hh]
            rfl
          have := hbal.1
          rw [hsupp, Finset.card_empty] at this
          omega
        have hlt := C.liveCount_eliminate_lt h hhbot
        obtain ⟨r, R, hr, hRbal, hRsound, hRcomplete⟩ :=
          ih (C.eliminate h) (by omega) (C.eliminate_isDecomposable h hdecomp)
            (C.eliminate_isFanInTwo h hfan)
        refine ⟨r + 1, Fin.cons (C.gateRectangle h) R, by omega, ?_, ?_, ?_⟩
        · rw [Fin.forall_fin_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨hbal, hRbal⟩
        · rw [Fin.forall_fin_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          refine ⟨?_, ?_⟩
          · intro v hv
            rw [C.mem_gateRectangle_iff hdecomp] at hv
            exact hv.2.sound hv.1
          · intro i v hv
            exact C.eliminate_semantics_imp h C.output v (hRsound i v hv)
        · intro v hv
          rcases C.semantics_eliminate_or_context h C.output v hv with ⟨hsem, hctx⟩ | hv'
          · refine ⟨0, ?_⟩
            rw [Fin.cons_zero, C.mem_gateRectangle_iff hdecomp]
            exact ⟨hsem, hctx⟩
          · obtain ⟨i, hi⟩ := hRcomplete v hv'
            refine ⟨i.succ, ?_⟩
            rw [Fin.cons_succ]
            exact hi
      · obtain ⟨cut, hsub, hbal⟩ := exists_balanced_superset_of_not_large hVar
          (S := C.support C.output)
          (by change ¬ 2 * Fintype.card Var < 3 * _ at hlarge; omega)
        refine ⟨1, fun _ ↦ C.outputRectangle cut, C.liveCount_pos hbot, ?_, ?_, ?_⟩
        · intro _
          exact hbal
        · intro _ v hv
          exact (C.mem_outputRectangle_iff hsub v).mp hv
        · intro v hv
          exact ⟨0, (C.mem_outputRectangle_iff hsub v).mpr hv⟩

/-- The cover of a fan-in-two DNNF as a `BalancedRectangleCover`, with at
most one rectangle per gate. -/
@[tutorial_box "thm:tutorial-gate-cover"]
theorem gate_rectangle_cover (C : NNFCircuit Var)
    (hVar : 2 ≤ Fintype.card Var) (hdecomp : C.IsDNNF) (hfan : C.IsFanInTwo)
    {f : (Var → Bool) → Prop} (hcomputes : C.Computes f) :
    ∃ (r : ℕ) (_ : BalancedRectangleCover f (Fin r)), r ≤ C.nodeCount := by
  obtain ⟨r, R, hr, hbal, hsound, hcomplete⟩ :=
    exists_balancedRectangleCover_of_fanInTwo hVar C.liveCount C le_rfl hdecomp hfan
  exact ⟨r, ⟨R, hbal, fun j v hv ↦ (hcomputes v).mp (hsound j v hv),
    fun v hv ↦ hcomplete v ((hcomputes v).mpr hv)⟩, hr.trans C.liveCount_le_nodeCount⟩

/-- Every DNNF over `N ≥ 2` variables with `s` edges has a balanced
rectangle cover with at most `2*s + 1` members. Binarize, prune gates
outside the output's dependency closure, then use one rectangle per gate.
The edges-plus-one conclusion is in `RectangleReduction.lean`. -/
theorem rectangle_cover (C : NNFCircuit Var)
    (hVar : 2 ≤ Fintype.card Var) (hdecomp : C.IsDNNF)
    {f : (Var → Bool) → Prop} (hcomputes : C.Computes f) :
    ∃ (r : ℕ) (_ : BalancedRectangleCover f (Fin r)), r ≤ 2 * C.edgeCount + 1 := by
  obtain ⟨r, cover, hr⟩ := C.binarize.prune.gate_rectangle_cover hVar
    (C.binarize.prune_isDNNF (C.binarize_isDNNF hdecomp))
    (C.binarize.prune_isFanInTwo C.binarize_isFanInTwo)
    (C.binarize.prune_computes (C.binarize_computes hcomputes))
  refine ⟨r, cover, ?_⟩
  calc r ≤ C.binarize.prune.nodeCount := hr
    _ ≤ C.binarize.prune.edgeCount + 1 := C.binarize.prune_nodeCount_le
    _ ≤ C.binarize.edgeCount + 1 := Nat.add_le_add_right C.binarize.edgeCount_prune_le 1
    _ ≤ 2 * C.edgeCount + 1 := Nat.add_le_add_right C.edgeCount_binarize_le 1

end NNFCircuit

end

end DDNNFNegation
