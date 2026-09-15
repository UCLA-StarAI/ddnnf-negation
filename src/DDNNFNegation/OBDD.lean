import DDNNFNegation.Circuit
import TutorialBox

/-!
# Read-once decision diagrams and their circuit translation

A read-once decision diagram tests each variable at most once along a path.
The generic model below does not require a common variable order. The
layered construction used for an outer term does use one order: its states
record the partial sums needed to evaluate that term.

The translation to d-DNNF allocates five gates per original diagram node,
including terminal nodes. The semantics, decomposability, determinism, and
size lemmas justify its use in the easy-side bound.
-/

namespace DDNNFNegation

open Finset

/-- One node of a binary decision DAG. -/
inductive OBDDNode (Var Gate : Type*) where
  | accept
  | reject
  | decision (x : Var) (low high : Gate)

namespace OBDDNode

/-- Local Boolean semantics: a decision node selects the child indexed by its input bit. -/
def Holds {Var Gate : Type*} (v : Var → Bool) (child : Gate → Prop) :
    OBDDNode Var Gate → Prop
  | accept => True
  | reject => False
  | decision x low high =>
      (v x = false ∧ child low) ∨
      (v x = true ∧ child high)

/-- The variables used locally by a decision node and its child subdiagrams. -/
def Support {Var Gate : Type*} [DecidableEq Var]
    (child : Gate → Finset Var) : OBDDNode Var Gate → Finset Var
  | accept => ∅
  | reject => ∅
  | decision x low high =>
      insert x (child low ∪ child high)

/-- The immediate dependency relation of a decision-diagram node. -/
def IsChild {Var Gate : Type*} (child : Gate) : OBDDNode Var Gate → Prop
  | decision _ low high => child = low ∨ child = high
  | _ => False

end OBDDNode

/-- A finite shared read-once decision DAG.  `readOnce` is the exact local
condition needed for decomposability after expansion. -/
structure ReadOnceOBDD (Var : Type*) [DecidableEq Var] where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  node : Gate → OBDDNode Var Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child,
    (node gate).IsChild child → rank child < rank gate
  semantics : Gate → (Var → Bool) → Prop
  semantics_eq : ∀ gate v,
    semantics gate v ↔ (node gate).Holds v (fun child ↦ semantics child v)
  support : Gate → Finset Var
  support_eq : ∀ gate,
    support gate = (node gate).Support support
  readOnce : ∀ gate x low high,
    node gate = .decision x low high →
      x ∉ support low ∧ x ∉ support high

namespace ReadOnceOBDD

variable {Var : Type*} [DecidableEq Var]

instance {Var : Type*} [DecidableEq Var] (B : ReadOnceOBDD Var) :
    Fintype B.Gate := B.gateFintype

instance {Var : Type*} [DecidableEq Var] (B : ReadOnceOBDD Var) :
    DecidableEq B.Gate := B.gateDecidableEq

/-- The number of shared OBDD nodes, counting each gate once. -/
def size {Var : Type*} [DecidableEq Var] (B : ReadOnceOBDD Var) : ℕ :=
  Fintype.card B.Gate

/-- The output of the OBDD agrees with the stated predicate on every Boolean assignment. -/
def Computes {Var : Type*} [DecidableEq Var] (B : ReadOnceOBDD Var)
    (f : (Var → Bool) → Prop) : Prop :=
  ∀ v, B.semantics B.output v ↔ f v

/-- The five shared gate roles allocated to each diagram node, including sinks. -/
inductive ExpansionKind where
  | main
  | low
  | high
  | neg
  | pos
  deriving DecidableEq

private def expansionKindEquiv : ExpansionKind ≃ Fin 5 where
  toFun
    | .main => 0
    | .low => 1
    | .high => 2
    | .neg => 3
    | .pos => 4
  invFun
    | ⟨0, _⟩ => .main
    | ⟨1, _⟩ => .low
    | ⟨2, _⟩ => .high
    | ⟨3, _⟩ => .neg
    | ⟨4, _⟩ => .pos
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

noncomputable instance : Fintype ExpansionKind :=
  Fintype.ofEquiv (Fin 5) expansionKindEquiv.symm

/-- Gate positions in the constant-size NNF expansion of each shared OBDD node. -/
abbrev ExpandedGate (B : ReadOnceOBDD Var) := ExpansionKind × B.Gate

private def expandedNode (B : ReadOnceOBDD Var) :
    ExpandedGate B → NNFNode Var (ExpandedGate B)
  | (.main, gate) =>
      match B.node gate with
      | .accept => .top
      | .reject => .bot
      | .decision _ _ _ => .disj [(.low, gate), (.high, gate)]
  | (.low, gate) =>
      match B.node gate with
      | .decision _ child _ => .conj (.neg, gate) (.main, child)
      | _ => .bot
  | (.high, gate) =>
      match B.node gate with
      | .decision _ _ child => .conj (.pos, gate) (.main, child)
      | _ => .bot
  | (.neg, gate) =>
      match B.node gate with
      | .decision x _ _ => .neg x
      | _ => .bot
  | (.pos, gate) =>
      match B.node gate with
      | .decision x _ _ => .pos x
      | _ => .bot

private def expandedRank (B : ReadOnceOBDD Var) : ExpandedGate B → ℕ
  | (.main, gate) => 3 * B.rank gate + 2
  | (.low, gate) => 3 * B.rank gate + 1
  | (.high, gate) => 3 * B.rank gate + 1
  | (.neg, _) => 0
  | (.pos, _) => 0

private def expandedSemantics (B : ReadOnceOBDD Var) :
    ExpandedGate B → (Var → Bool) → Prop
  | (.main, gate), v => B.semantics gate v
  | (.low, gate), v =>
      match B.node gate with
      | .decision x child _ =>
          v x = false ∧ B.semantics child v
      | _ => False
  | (.high, gate), v =>
      match B.node gate with
      | .decision x _ child =>
          v x = true ∧ B.semantics child v
      | _ => False
  | (.neg, gate), v =>
      match B.node gate with
      | .decision x _ _ => v x = false
      | _ => False
  | (.pos, gate), v =>
      match B.node gate with
      | .decision x _ _ => v x = true
      | _ => False

private def expandedSupport (B : ReadOnceOBDD Var) :
    ExpandedGate B → Finset Var
  | (.main, gate) => B.support gate
  | (.low, gate) =>
      match B.node gate with
      | .decision x child _ => insert x (B.support child)
      | _ => ∅
  | (.high, gate) =>
      match B.node gate with
      | .decision x _ child => insert x (B.support child)
      | _ => ∅
  | (.neg, gate) | (.pos, gate) =>
      match B.node gate with
      | .decision x _ _ => {x}
      | _ => ∅

private theorem expanded_child_rank (B : ReadOnceOBDD Var)
    (gate child : ExpandedGate B)
    (hchild : (expandedNode B gate).IsChild child) :
    expandedRank B child < expandedRank B gate := by
  rcases gate with ⟨kind, gate⟩
  cases kind
  · cases hnode : B.node gate with
    | accept => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
    | reject => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
    | decision x low high =>
        simp [expandedNode, NNFNode.IsChild, hnode] at hchild
        rcases hchild with rfl | rfl <;> simp [expandedRank]
  · cases hnode : B.node gate with
    | accept => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
    | reject => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
    | decision x low high =>
        simp [expandedNode, NNFNode.IsChild, hnode] at hchild
        rcases hchild with rfl | rfl
        · simp [expandedRank]
        · have hr := B.child_rank gate low (by
            simp [hnode, OBDDNode.IsChild])
          simp [expandedRank]
          omega
  · cases hnode : B.node gate with
    | accept => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
    | reject => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
    | decision x low high =>
        simp [expandedNode, NNFNode.IsChild, hnode] at hchild
        rcases hchild with rfl | rfl
        · simp [expandedRank]
        · have hr := B.child_rank gate high (by
            simp [hnode, OBDDNode.IsChild])
          simp [expandedRank]
          omega
  · cases hnode : B.node gate <;>
      simp [expandedNode, NNFNode.IsChild, hnode] at hchild
  · cases hnode : B.node gate <;>
      simp [expandedNode, NNFNode.IsChild, hnode] at hchild

private theorem expanded_semantics_eq (B : ReadOnceOBDD Var)
    (gate : ExpandedGate B) (v : Var → Bool) :
    expandedSemantics B gate v ↔
      (expandedNode B gate).Holds v
        (fun child ↦ expandedSemantics B child v) := by
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hnode : B.node gate <;>
    simp [expandedNode, expandedSemantics, NNFNode.Holds, hnode]
  all_goals
    rw [B.semantics_eq]
    simp [OBDDNode.Holds, hnode]

private theorem expanded_support_eq (B : ReadOnceOBDD Var)
    (gate : ExpandedGate B) :
    expandedSupport B gate =
      (expandedNode B gate).Support (expandedSupport B) := by
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hnode : B.node gate <;>
    simp [expandedNode, expandedSupport, NNFNode.Support, hnode]
  all_goals
    rw [B.support_eq]
    simp [OBDDNode.Support, hnode]

/-- The shared NNF expansion of a read-once decision DAG. -/
noncomputable def toNNFCircuit (B : ReadOnceOBDD Var) : NNFCircuit Var where
  Gate := ExpandedGate B
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := (.main, B.output)
  node := expandedNode B
  rank := expandedRank B
  child_rank := expanded_child_rank B
  semantics := expandedSemantics B
  semantics_eq := expanded_semantics_eq B
  support := expandedSupport B
  support_eq := expanded_support_eq B

/-- The shared NNF expansion computes the original decision-diagram function. -/
theorem toNNFCircuit_computes (B : ReadOnceOBDD Var)
    (f : (Var → Bool) → Prop) (hf : B.Computes f) :
    (B.toNNFCircuit).Computes f := by
  intro v
  exact hf v

/-- Read-once paths keep the decision variable outside both suffix supports, making the
expansion decomposable. -/
theorem toNNFCircuit_decomposable (B : ReadOnceOBDD Var) :
    (B.toNNFCircuit).IsDecomposable := by
  intro gate left right hnode
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hdecision : B.node gate <;>
    simp [toNNFCircuit, expandedNode, hdecision] at hnode
  all_goals
    injection hnode with hleft hright
    subst left
    subst right
    simp [toNNFCircuit, expandedSupport, hdecision,
      Finset.disjoint_singleton_left]
  all_goals first
    | exact (B.readOnce _ _ _ _ hdecision).1
    | exact (B.readOnce _ _ _ _ hdecision).2

/-- Opposite decision literals make the two branches mutually exclusive. -/
theorem toNNFCircuit_deterministic (B : ReadOnceOBDD Var) :
    (B.toNNFCircuit).IsDeterministic := by
  intro gate children hnode left hleft right hright hne v
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hdecision : B.node gate <;>
    simp [toNNFCircuit, expandedNode, hdecision] at hnode
  injection hnode with hchildren
  subst children
  obtain rfl | rfl := List.mem_pair.mp hleft <;>
    obtain rfl | rfl := List.mem_pair.mp hright
  · exact absurd rfl hne
  · simp only [toNNFCircuit, expandedSemantics, hdecision]
    rintro ⟨⟨hfalse, _⟩, htrue, _⟩
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  · simp only [toNNFCircuit, expandedSemantics, hdecision]
    rintro ⟨⟨htrue, _⟩, hfalse, _⟩
    exact Bool.noConfusion (htrue.symm.trans hfalse)
  · exact absurd rfl hne

/-- Every finite shared read-once OBDD becomes a deterministic DNNF. -/
theorem toNNFCircuit_isDeterministicDNNF (B : ReadOnceOBDD Var) :
    (B.toNNFCircuit).IsDeterministicDNNF :=
  ⟨B.toNNFCircuit_decomposable, B.toNNFCircuit_deterministic⟩

/-- The expansion uses exactly five gate roles per original shared node. -/
theorem toNNFCircuit_size (B : ReadOnceOBDD Var) :
    B.toNNFCircuit.size = 5 * B.size := by
  rw [NNFCircuit.size, ReadOnceOBDD.size]
  change Fintype.card (ExpansionKind × B.Gate) =
    5 * Fintype.card B.Gate
  rw [Fintype.card_prod, Fintype.card_congr expansionKindEquiv,
    Fintype.card_fin]

/-- Every disjunction of the expansion has two inputs. -/
theorem toNNFCircuit_isFanInTwo (B : ReadOnceOBDD Var) :
    B.toNNFCircuit.IsFanInTwo := by
  intro gate children hnode
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hdecision : B.node gate <;>
    simp [toNNFCircuit, expandedNode, hdecision] at hnode
  injection hnode with hchildren
  subst hchildren
  exact le_rfl

/-- The expansion has at most ten edges per original node: the tutorial's
"constant number of edges per decision node". -/
theorem toNNFCircuit_edgeCount_le (B : ReadOnceOBDD Var) :
    B.toNNFCircuit.edgeCount ≤ 10 * B.size := by
  calc B.toNNFCircuit.edgeCount ≤ 2 * B.toNNFCircuit.size :=
        B.toNNFCircuit.edgeCount_le_two_mul_size B.toNNFCircuit_isFanInTwo
    _ = 10 * B.size := by
        rw [toNNFCircuit_size]
        ring

end ReadOnceOBDD

/-- The tutorial's OBDD conversion: the explicit shared expansion preserves
the function, is a deterministic DNNF, and has at most ten edges per OBDD node.
This is a circuit-size statement, not a running-time theorem for BDD Apply. -/
theorem obdd_to_dDNNF {Var : Type*} [DecidableEq Var]
    (B : ReadOnceOBDD Var) (f : (Var → Bool) → Prop) (hf : B.Computes f) :
    B.toNNFCircuit.Computes f ∧ B.toNNFCircuit.IsDeterministicDNNF ∧
      B.toNNFCircuit.edgeCount ≤ 10 * B.size :=
  ⟨B.toNNFCircuit_computes f hf, B.toNNFCircuit_isDeterministicDNNF,
    B.toNNFCircuit_edgeCount_le⟩

namespace LayeredOBDD

/-- Run a transition system from layer `i` through the last input bit. -/
def runFrom {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (v : Fin N → Bool) (i : ℕ) (state : State) : State :=
  if h : i < N then
    runFrom step v (i + 1)
      (step ⟨i, h⟩ state (v ⟨i, h⟩))
  else state
termination_by N - i
decreasing_by omega

/-- Before the last layer, running the machine reads the next bit and continues from its
successor state. -/
theorem runFrom_of_lt {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (v : Fin N → Bool) (i : ℕ) (state : State)
    (h : i < N) :
    runFrom step v i state =
      runFrom step v (i + 1)
        (step ⟨i, h⟩ state (v ⟨i, h⟩)) := by
  rw [runFrom]
  simp [h]

/-- The contribution of the input suffix beginning at position `i`. -/
def suffixSum {N : ℕ} {State : Type*} [AddCommMonoid State]
    (column : Fin N → State) (v : Fin N → Bool) (i : ℕ) : State :=
  ∑ j ∈ Finset.univ.filter (fun j ↦ i ≤ j.1),
    if v j then column j else 0

/-- Split a nonempty suffix sum into its first selected column and the remaining suffix. -/
theorem suffixSum_of_lt {N : ℕ} {State : Type*} [AddCommMonoid State]
    (column : Fin N → State) (v : Fin N → Bool) (i : ℕ) (h : i < N) :
    suffixSum column v i =
      (if v ⟨i, h⟩ then column ⟨i, h⟩ else 0) +
        suffixSum column v (i + 1) := by
  unfold suffixSum
  let current : Fin N := ⟨i, h⟩
  have hsets : Finset.univ.filter (fun j : Fin N ↦ i ≤ j.1) =
      insert current (Finset.univ.filter (fun j : Fin N ↦ i + 1 ≤ j.1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hij
      by_cases heq : j = current
      · exact Or.inl heq
      · right
        have hne : j.1 ≠ i := by
          intro hval
          apply heq
          exact Fin.ext hval
        omega
    · rintro (rfl | hj)
      · exact Nat.le_refl i
      · omega
  rw [hsets, Finset.sum_insert]
  simp [current]

/-- After the final input position the remaining column sum is zero. -/
theorem suffixSum_eq_zero_of_end {N : ℕ} {State : Type*}
    [AddCommMonoid State] (column : Fin N → State) (v : Fin N → Bool)
    (i : ℕ) (h : N ≤ i) : suffixSum column v i = 0 := by
  unfold suffixSum
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  omega

/-- Additive transitions compute the initial state plus the suffix subset
sum. -/
theorem runFrom_add_eq {N : ℕ} {State : Type*} [AddCommMonoid State]
    (column : Fin N → State) (v : Fin N → Bool)
    (i : ℕ) (state : State) :
    runFrom (fun j state bit ↦ state + if bit then column j else 0)
        v i state =
      state + suffixSum column v i := by
  rw [runFrom]
  split
  · rename_i h
    rw [runFrom_add_eq column v (i + 1)]
    rw [suffixSum_of_lt column v i h]
    simp [add_assoc]
  · rename_i h
    rw [suffixSum_eq_zero_of_end column v i (by omega)]
    simp
termination_by N - i
decreasing_by omega

/-- Starting at the first layer accumulates the full selected-column sum in the initial
state. -/
theorem runFrom_add_at_zero {N : ℕ} {State : Type*}
    [AddCommMonoid State] (column : Fin N → State) (v : Fin N → Bool) :
    runFrom (fun j state bit ↦ state + if bit then column j else 0)
        v 0 0 =
      ∑ j, if v j then column j else 0 := by
  rw [runFrom_add_eq]
  simp [suffixSum]

/-- A layer is represented by an element of `Fin (N + 1)`. -/
abbrev Layer (N : ℕ) := Fin (N + 1)

/-- One OBDD node for each layer and finite state. -/
abbrev Gate (N : ℕ) (State : Type*) := Layer N × State

private def nextLayer {N : ℕ} (i : Layer N) (h : i.1 < N) : Layer N :=
  ⟨i.1 + 1, by omega⟩

private def node {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) : Gate N State → OBDDNode (Fin N) (Gate N State)
  | (i, state) =>
      if h : i.1 < N then
        .decision ⟨i.1, h⟩
          (nextLayer i h, step ⟨i.1, h⟩ state false)
          (nextLayer i h, step ⟨i.1, h⟩ state true)
      else if accept state then .accept else .reject

private def rank {N : ℕ} {State : Type*} : Gate N State → ℕ :=
  fun gate ↦ N - gate.1.1

private def semantics {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) : Gate N State → (Fin N → Bool) → Prop :=
  fun gate v ↦
    accept (runFrom step v gate.1.1 gate.2) = true

private def support {N : ℕ} {State : Type*} :
    Gate N State → Finset (Fin N) :=
  fun gate ↦ Finset.univ.filter (fun j ↦ gate.1.1 ≤ j.1)

private theorem child_rank {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (gate child : Gate N State)
    (hchild : (node step accept gate).IsChild child) :
    rank child < rank gate := by
  rcases gate with ⟨i, state⟩
  simp only [node] at hchild
  split at hchild
  · rcases hchild with rfl | rfl <;> simp [rank, nextLayer] <;> omega
  · split at hchild <;> simp [OBDDNode.IsChild] at hchild

private theorem semantics_eq {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (gate : Gate N State) (v : Fin N → Bool) :
    semantics step accept gate v ↔
      (node step accept gate).Holds v
        (fun child ↦ semantics step accept child v) := by
  rcases gate with ⟨i, state⟩
  simp only [node]
  split
  · rename_i h
    change accept (runFrom step v i.1 state) = true ↔ _
    rw [runFrom_of_lt step v i.1 state h]
    cases hv : v ⟨i.1, h⟩ <;>
      simp [semantics, OBDDNode.Holds, hv, nextLayer]
  · rename_i h
    change accept (runFrom step v i.1 state) = true ↔ _
    rw [runFrom]
    simp only [h, ↓reduceDIte]
    split <;> simp_all [OBDDNode.Holds]

private theorem support_eq {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (gate : Gate N State) :
    support gate = (node step accept gate).Support support := by
  rcases gate with ⟨i, state⟩
  simp only [node]
  split
  · rename_i h
    ext j
    simp only [support, OBDDNode.Support, nextLayer, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_union]
    constructor
    · intro hij
      by_cases heq : j = ⟨i.1, h⟩
      · exact Or.inl heq
      · right
        have hne : j.1 ≠ i.1 := by
          intro hval
          apply heq
          exact Fin.ext hval
        have hsucc : i.1 + 1 ≤ j.1 := by omega
        exact Or.inl (by simpa [support] using hsucc)
    · rintro (heq | hleft | hright)
      · simp [heq]
      · have hleft' : i.1 + 1 ≤ j.1 := by
          simpa [support] using hleft
        omega
      · have hright' : i.1 + 1 ≤ j.1 := by
          simpa [support] using hright
        omega
  · rename_i h
    have hi : i.1 = N := by omega
    split <;> ext j <;> simp [support, OBDDNode.Support, hi]

private theorem readOnce {N : ℕ} {State : Type*}
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (gate : Gate N State)
    (x : Fin N) (low high : Gate N State)
    (hnode : node step accept gate = .decision x low high) :
    x ∉ support low ∧ x ∉ support high := by
  rcases gate with ⟨i, state⟩
  simp only [node] at hnode
  split at hnode
  · rename_i h
    injection hnode with hx hlow hhigh
    subst x
    subst low
    subst high
    simp [support, nextLayer]
  · split at hnode <;> contradiction

/-- The read-once OBDD represented by a layered transition system. -/
noncomputable def ofTransition {N : ℕ} {State : Type*}
    [Fintype State] [DecidableEq State]
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) : ReadOnceOBDD (Fin N) where
  Gate := Gate N State
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := (⟨0, by omega⟩, start)
  node := node step accept
  rank := rank
  child_rank := child_rank step accept
  semantics := semantics step accept
  semantics_eq := semantics_eq step accept
  support := support
  support_eq := support_eq step accept
  readOnce := readOnce step accept

/-- The layered construction uses one shared node for each layer-state pair. -/
theorem ofTransition_size {N : ℕ} {State : Type*}
    [Fintype State] [DecidableEq State]
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) :
    (ofTransition step accept start).size =
      (N + 1) * Fintype.card State := by
  rw [ReadOnceOBDD.size]
  change Fintype.card (Layer N × State) = _
  rw [Fintype.card_prod]
  simp [Layer]

end LayeredOBDD

end DDNNFNegation
