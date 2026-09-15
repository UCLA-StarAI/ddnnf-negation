import DDNNFNegation.Circuit
import DDNNFNegation.Rectangles

/-!
# Satisfying contexts and balanced rectangles

A context records a path from a gate toward a designated target and the
sibling conditions needed along that path. It does not require the target
itself to be satisfied. In a decomposable circuit, the context depends only
on variables outside the target's support. Combining it with satisfaction
of the target therefore gives a rectangle. Support-size lemmas identify
balanced cuts for the gate-elimination argument.
-/

namespace DDNNFNegation

open Finset

noncomputable section

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

private theorem subset_foldl_union_left
    {Gate : Type*} (support : Gate → Finset Var)
    (children : List Gate) (initial : Finset Var) :
    initial ⊆ children.foldl (fun result gate ↦ result ∪ support gate) initial := by
  induction children generalizing initial with
  | nil => exact Subset.rfl
  | cons gate children ih =>
      exact subset_union_left.trans (ih (initial ∪ support gate))

private theorem subset_foldl_union_of_mem
    {Gate : Type*} (support : Gate → Finset Var)
    {child : Gate} {children : List Gate} (initial : Finset Var)
    (hchild : child ∈ children) :
    support child ⊆
      children.foldl (fun result gate ↦ result ∪ support gate) initial := by
  induction children generalizing initial with
  | nil => simp at hchild
  | cons gate children ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hchild with heq | hchild
      · subst child
        exact subset_union_right.trans
          (subset_foldl_union_left support children (initial ∪ support gate))
      · exact ih (initial ∪ support gate) hchild

/-- Syntactic support is monotone along every circuit edge. -/
theorem support_subset_of_isChild (C : NNFCircuit Var)
    {gate child : C.Gate} (hchild : (C.node gate).IsChild child) :
    C.support child ⊆ C.support gate := by
  rw [C.support_eq gate]
  cases hnode : C.node gate with
  | top => rw [hnode] at hchild; contradiction
  | bot => rw [hnode] at hchild; contradiction
  | pos x => rw [hnode] at hchild; contradiction
  | neg x => rw [hnode] at hchild; contradiction
  | conj left right =>
      rw [hnode] at hchild
      change C.support child ⊆ C.support left ∪ C.support right
      rcases hchild with rfl | rfl
      · exact subset_union_left
      · exact subset_union_right
  | disj children =>
      rw [hnode] at hchild
      change C.support child ⊆
        children.foldl (fun result gate ↦ result ∪ C.support gate) ∅
      exact subset_foldl_union_of_mem C.support ∅ hchild

/-- Circuit semantics at a gate depends only on that gate's syntactic
support. -/
theorem semantics_congr_of_eqOn_support (C : NNFCircuit Var)
    (gate : C.Gate) (v w : Var → Bool)
    (hagree : ∀ x ∈ C.support gate, v x = w x) :
    C.semantics gate v ↔ C.semantics gate w := by
  rw [C.semantics_eq gate v, C.semantics_eq gate w]
  cases hnode : C.node gate with
  | top => simp [NNFNode.Holds]
  | bot => simp [NNFNode.Holds]
  | pos x =>
      have hx : x ∈ C.support gate := by
        rw [C.support_eq gate, hnode]
        simp [NNFNode.Support]
      simp only [NNFNode.Holds]
      rw [hagree x hx]
  | neg x =>
      have hx : x ∈ C.support gate := by
        rw [C.support_eq gate, hnode]
        simp [NNFNode.Support]
      simp only [NNFNode.Holds]
      rw [hagree x hx]
  | conj left right =>
      have hleft : (C.node gate).IsChild left := by
        simp [hnode, NNFNode.IsChild]
      have hright : (C.node gate).IsChild right := by
        simp [hnode, NNFNode.IsChild]
      have hagreeLeft : ∀ x ∈ C.support left, v x = w x := fun x hx ↦
        hagree x (C.support_subset_of_isChild hleft hx)
      have hagreeRight : ∀ x ∈ C.support right, v x = w x := fun x hx ↦
        hagree x (C.support_subset_of_isChild hright hx)
      simp only [NNFNode.Holds]
      exact and_congr
        (C.semantics_congr_of_eqOn_support left v w hagreeLeft)
        (C.semantics_congr_of_eqOn_support right v w hagreeRight)
  | disj children =>
      simp only [NNFNode.Holds]
      constructor
      · rintro ⟨child, hmem, hsem⟩
        refine ⟨child, hmem, ?_⟩
        apply (C.semantics_congr_of_eqOn_support child v w ?_).mp hsem
        intro x hx
        apply hagree x
        exact C.support_subset_of_isChild (by simpa [hnode, NNFNode.IsChild]) hx
      · rintro ⟨child, hmem, hsem⟩
        refine ⟨child, hmem, ?_⟩
        apply (C.semantics_congr_of_eqOn_support child v w ?_).mpr hsem
        intro x hx
        apply hagree x
        exact C.support_subset_of_isChild (by simpa [hnode, NNFNode.IsChild]) hx
termination_by C.rank gate
decreasing_by
  all_goals apply C.child_rank gate
  all_goals simp_all [NNFNode.IsChild]

/-- A context along a path from `current` to `target`. At conjunctions,
the sibling must be satisfied; at disjunctions, the path selects a child.
The relation stops at `target` without requiring its satisfaction. -/
inductive HasContext (C : NNFCircuit Var) (target : C.Gate)
    (v : Var → Bool) : C.Gate → Prop
  | here : HasContext C target v target
  | conjLeft {gate left right} :
      C.node gate = .conj left right →
      HasContext C target v left → C.semantics right v →
      HasContext C target v gate
  | conjRight {gate left right} :
      C.node gate = .conj left right →
      C.semantics left v → HasContext C target v right →
      HasContext C target v gate
  | disj {gate children child} :
      C.node gate = .disj children → child ∈ children →
      HasContext C target v child → HasContext C target v gate

namespace HasContext

/-- The target support lies inside the support of every gate reached by its
outside context. -/
theorem support_subset {C : NNFCircuit Var} {target current : C.Gate}
    {v : Var → Bool} (h : C.HasContext target v current) :
    C.support target ⊆ C.support current := by
  induction h with
  | here => exact Subset.rfl
  | conjLeft hnode _ _ ih =>
      exact ih.trans (C.support_subset_of_isChild (by simp [hnode, NNFNode.IsChild]))
  | conjRight hnode _ _ ih =>
      exact ih.trans (C.support_subset_of_isChild (by simp [hnode, NNFNode.IsChild]))
  | disj hnode hmem _ ih =>
      exact ih.trans (C.support_subset_of_isChild (by simpa [hnode, NNFNode.IsChild]))

/-- A satisfied target together with a satisfied outside context makes the
current gate true. -/
theorem sound {C : NNFCircuit Var} {target current : C.Gate}
    {v : Var → Bool} (h : C.HasContext target v current)
    (htarget : C.semantics target v) : C.semantics current v := by
  induction h with
  | here => exact htarget
  | conjLeft hnode _ hright ih =>
      rw [C.semantics_eq, hnode]
      exact ⟨ih, hright⟩
  | conjRight hnode hleft _ ih =>
      rw [C.semantics_eq, hnode]
      exact ⟨hleft, ih⟩
  | disj hnode hmem _ ih =>
      rw [C.semantics_eq, hnode]
      exact ⟨_, hmem, ih⟩

/-- The outside context of a gate depends only on variables outside that
gate's support. -/
theorem congr_of_eqOutside
    {C : NNFCircuit Var} (hdecomp : C.IsDecomposable)
    {target current : C.Gate} {v w : Var → Bool}
    (h : C.HasContext target v current)
    (hagree : ∀ x, x ∉ C.support target → v x = w x) :
    C.HasContext target w current := by
  induction h with
  | here => exact .here
  | @conjLeft gate left right hnode hcontext hright ih =>
      apply HasContext.conjLeft hnode ih
      apply (C.semantics_congr_of_eqOn_support right v w ?_).mp hright
      intro x hxright
      apply hagree x
      intro hxtarget
      have hxleft := hcontext.support_subset hxtarget
      exact (Finset.disjoint_left.mp (hdecomp gate left right hnode)) hxleft hxright
  | @conjRight gate left right hnode hleft hcontext ih =>
      apply HasContext.conjRight hnode
      · apply (C.semantics_congr_of_eqOn_support left v w ?_).mp hleft
        intro x hxleft
        apply hagree x
        intro hxtarget
        have hxright := hcontext.support_subset hxtarget
        exact (Finset.disjoint_left.mp (hdecomp gate left right hnode)) hxleft hxright
      · exact ih
  | disj hnode hmem _ ih => exact .disj hnode hmem ih

end HasContext

end NNFCircuit

/-- A predicate on assignments depends only on the coordinates in `S`. -/
def DependsOnlyOn {Var : Type*} (S : Finset Var)
    (p : (Var → Bool) → Prop) : Prop :=
  ∀ v w, (∀ x ∈ S, v x = w x) → (p v ↔ p w)

/-- All restrictions to `S` that occur among assignments satisfying `p`. -/
def satisfyingRestrictions
    {Var : Type*} [Fintype Var] [DecidableEq Var]
  (S : Finset Var) (p : (Var → Bool) → Prop) : Finset (S → Bool) := by
  classical
  exact Finset.univ.filter fun part ↦
    ∃ v, p v ∧ ∀ x : S, v x = part x

/-- The product of two predicates living on opposite sides of a cut. -/
def separatedRectangle
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (S : Finset Var) (leftPred rightPred : (Var → Bool) → Prop) :
    BooleanRectangle Var where
  cut := S
  left := satisfyingRestrictions S leftPred
  right := satisfyingRestrictions Sᶜ rightPred

@[simp] theorem mem_satisfyingRestrictions
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (S : Finset Var) (p : (Var → Bool) → Prop) (part : S → Bool) :
    part ∈ satisfyingRestrictions S p ↔
      ∃ v, p v ∧ ∀ x : S, v x = part x := by
  classical
  simp [satisfyingRestrictions]

/-- Membership in a rectangle built from two separated predicates is exactly
their conjunction. -/
theorem mem_separatedRectangle_iff
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (S : Finset Var) (leftPred rightPred : (Var → Bool) → Prop)
    (hleft : DependsOnlyOn S leftPred)
    (hright : DependsOnlyOn Sᶜ rightPred) (v : Var → Bool) :
    v ∈ (separatedRectangle S leftPred rightPred).assignments ↔
      leftPred v ∧ rightPred v := by
  classical
  rw [BooleanRectangle.assignments, mem_assignmentRectangle]
  change
    (assignmentPartitionEquiv S v).1 ∈ satisfyingRestrictions S leftPred ∧
      (assignmentPartitionEquiv S v).2 ∈ satisfyingRestrictions Sᶜ rightPred ↔ _
  constructor
  · rintro ⟨hL, hR⟩
    rw [mem_satisfyingRestrictions] at hL hR
    obtain ⟨vL, hvL, hagreeL⟩ := hL
    obtain ⟨vR, hvR, hagreeR⟩ := hR
    constructor
    · apply (hleft vL v ?_).mp hvL
      intro x hx
      exact (hagreeL ⟨x, hx⟩).trans (by rfl)
    · apply (hright vR v ?_).mp hvR
      intro x hx
      exact (hagreeR ⟨x, hx⟩).trans (by rfl)
  · rintro ⟨hL, hR⟩
    constructor
    · rw [mem_satisfyingRestrictions]
      exact ⟨v, hL, fun _ ↦ rfl⟩
    · rw [mem_satisfyingRestrictions]
      exact ⟨v, hR, fun _ ↦ rfl⟩

namespace NNFCircuit

variable {Var : Type*} [Fintype Var] [DecidableEq Var]

/-- Support smaller than one third of all variables. -/
def HasSmallSupport (C : NNFCircuit Var) (gate : C.Gate) : Prop :=
  3 * (C.support gate).card < Fintype.card Var

/-- Support larger than two thirds of all variables. -/
def HasLargeSupport (C : NNFCircuit Var) (gate : C.Gate) : Prop :=
  2 * Fintype.card Var < 3 * (C.support gate).card

/-- Support that itself gives a one-third-balanced cut. -/
def HasBalancedSupport (C : NNFCircuit Var) (gate : C.Gate) : Prop :=
  IsBalanced (C.support gate)

/-- A support that is neither too small nor too large is balanced. -/
theorem hasBalancedSupport_of_not_small_not_large (C : NNFCircuit Var)
    (gate : C.Gate) (hsmall : ¬C.HasSmallSupport gate)
    (hlarge : ¬C.HasLargeSupport gate) : C.HasBalancedSupport gate := by
  change ¬3 * (C.support gate).card < Fintype.card Var at hsmall
  change ¬2 * Fintype.card Var < 3 * (C.support gate).card at hlarge
  constructor
  · exact Nat.le_of_not_gt hsmall
  · rw [Finset.card_compl]
    have hcard : (C.support gate).card ≤ Fintype.card Var :=
      Finset.card_le_univ _
    omega

/-- The integer `N / 3 + 1` is a balanced side size whenever `N ≥ 2`. -/
theorem oneThirdTarget_balanced (hVar : 2 ≤ Fintype.card Var)
    {cut : Finset Var} (hcard : cut.card = Fintype.card Var / 3 + 1) :
    IsBalanced cut := by
  constructor
  · omega
  · rw [Finset.card_compl, hcard]
    omega

/-- A small set can be padded to a balanced cut. -/
theorem exists_balanced_superset_of_small
    (hVar : 2 ≤ Fintype.card Var) {S : Finset Var}
    (hsmall : 3 * S.card < Fintype.card Var) :
    ∃ cut : Finset Var, S ⊆ cut ∧ IsBalanced cut := by
  have hScard : S.card ≤ Fintype.card Var / 3 := by omega
  have htarget : Fintype.card Var / 3 + 1 ≤ Fintype.card Var := by omega
  obtain ⟨cut, hSsub, hcard⟩ :=
    Finset.exists_superset_card_eq
      (s := S) (n := Fintype.card Var / 3 + 1) (by omega) htarget
  exact ⟨cut, hSsub,
    oneThirdTarget_balanced hVar hcard⟩

omit [Fintype Var] in
/-- The semantics below a gate depends only on its support. -/
theorem semantics_dependsOnlyOn (C : NNFCircuit Var) (gate : C.Gate) :
    DependsOnlyOn (C.support gate) (C.semantics gate) := by
  intro v w hagree
  exact C.semantics_congr_of_eqOn_support gate v w hagree

/-- The outside context of a gate depends only on the complementary
coordinates. -/
theorem context_dependsOnlyOn_compl (C : NNFCircuit Var)
    (hdecomp : C.IsDecomposable) (gate : C.Gate) :
    DependsOnlyOn (C.support gate)ᶜ
      (fun v ↦ C.HasContext gate v C.output) := by
  intro v w hagree
  constructor
  · intro hcontext
    apply hcontext.congr_of_eqOutside hdecomp
    intro x hx
    exact hagree x (by simpa using hx)
  · intro hcontext
    apply hcontext.congr_of_eqOutside hdecomp
    intro x hx
    exact (hagree x (by simpa using hx)).symm

/-- The assignments whose satisfying outside context contains `gate`. -/
def gateRectangle (C : NNFCircuit Var) (gate : C.Gate) :
    BooleanRectangle Var :=
  separatedRectangle (C.support gate) (C.semantics gate)
    (fun v ↦ C.HasContext gate v C.output)

@[simp] theorem mem_gateRectangle_iff (C : NNFCircuit Var)
    (hdecomp : C.IsDecomposable) (gate : C.Gate) (v : Var → Bool) :
    v ∈ (C.gateRectangle gate).assignments ↔
      C.semantics gate v ∧ C.HasContext gate v C.output := by
  exact mem_separatedRectangle_iff _ _ _
    (C.semantics_dependsOnlyOn gate)
    (C.context_dependsOnlyOn_compl hdecomp gate) v

end NNFCircuit

end

end DDNNFNegation
