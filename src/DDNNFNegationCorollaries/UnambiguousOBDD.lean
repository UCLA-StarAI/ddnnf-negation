import DDNNFNegation.Separation
import TutorialBox

/-!
# Unambiguous OBDDs

The paper's unambiguous OBDD corollary. A guess node joins the term
OBDDs in a common variable order; disjoint terms make the result
unambiguous. The main theorem supplies the DNNF lower bound for
the complement. Size counts nodes.
-/

namespace DDNNFNegation

open Finset

/-! ## Nodes -/

/-- One node of a nondeterministic branching program. -/
inductive BPNode (Var Gate : Type*) where
  | accept
  | reject
  | decision (x : Var) (low high : Gate)
  | guess (children : List Gate)

namespace BPNode

variable {Var Gate Gate' : Type*}

/-- Local semantics: a decision follows the successor selected by the input
bit, a guess node accepts when some successor does. -/
def Holds (v : Var → Bool) (child : Gate → Prop) : BPNode Var Gate → Prop
  | accept => True
  | reject => False
  | decision x low high =>
      (v x = false ∧ child low) ∨ (v x = true ∧ child high)
  | guess children => ∃ gate ∈ children, child gate

/-- Local support: the decision variable and everything below. -/
def Support [DecidableEq Var] (child : Gate → Finset Var) :
    BPNode Var Gate → Finset Var
  | accept => ∅
  | reject => ∅
  | decision x low high => insert x (child low ∪ child high)
  | guess children =>
      children.foldl (fun result gate ↦ result ∪ child gate) ∅

/-- The successor relation. -/
def IsChild (child : Gate) : BPNode Var Gate → Prop
  | decision _ low high => child = low ∨ child = high
  | guess children => child ∈ children
  | _ => False

/-- Rename the successor references. -/
def map (f : Gate → Gate') : BPNode Var Gate → BPNode Var Gate'
  | accept => accept
  | reject => reject
  | decision x low high => decision x (f low) (f high)
  | guess children => guess (children.map f)

/-- Rename the decision variable. -/
def mapVar {Var' : Type*} (e : Var → Var') : BPNode Var Gate → BPNode Var' Gate
  | accept => accept
  | reject => reject
  | decision x low high => decision (e x) low high
  | guess children => guess children

theorem holds_map (f : Gate → Gate') (node : BPNode Var Gate) (v : Var → Bool)
    (child : Gate' → Prop) :
    (node.map f).Holds v child ↔ node.Holds v (fun gate ↦ child (f gate)) := by
  cases node <;> simp [map, Holds]

theorem support_map [DecidableEq Var] (f : Gate → Gate') (node : BPNode Var Gate)
    (child : Gate' → Finset Var) :
    (node.map f).Support child = node.Support (fun gate ↦ child (f gate)) := by
  cases node <;> simp [map, Support, List.foldl_map]

theorem isChild_map_exists (f : Gate → Gate') (node : BPNode Var Gate)
    (child : Gate') (hchild : (node.map f).IsChild child) :
    ∃ source, node.IsChild source ∧ f source = child := by
  cases node <;> simp [map, IsChild] at hchild ⊢
  · rcases hchild with rfl | rfl <;> simp
  · obtain ⟨source, hmem, rfl⟩ := hchild
    exact ⟨source, hmem, rfl⟩

theorem isChild_mapVar {Var' : Type*} (e : Var → Var') (node : BPNode Var Gate)
    (child : Gate) : (node.mapVar e).IsChild child ↔ node.IsChild child := by
  cases node <;> simp [mapVar, IsChild]

end BPNode

/-- Mapping a finite union along an embedding. -/
theorem map_foldl_union {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (e : β ↪ γ) (l : List α) (child : α → Finset β) (acc : Finset β) :
    (l.foldl (fun result j ↦ result ∪ child j) acc).map e =
      l.foldl (fun result j ↦ result ∪ (child j).map e) (acc.map e) := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
      simp only [List.foldl_cons]
      rw [ih, Finset.map_union]

/-! ## Programs -/

/-- A finite shared nondeterministic read-once branching program. -/
structure BranchingProgram (Var : Type*) [DecidableEq Var] where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  node : Gate → BPNode Var Gate
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

namespace BranchingProgram

variable {Var : Type*} [DecidableEq Var]

instance (B : BranchingProgram Var) : Fintype B.Gate := B.gateFintype

instance (B : BranchingProgram Var) : DecidableEq B.Gate := B.gateDecidableEq

/-- Number of nodes. -/
def size (B : BranchingProgram Var) : ℕ :=
  Fintype.card B.Gate

/-- The program accepts exactly the assignments satisfying `f`. -/
def Computes (B : BranchingProgram Var) (f : (Var → Bool) → Prop) : Prop :=
  ∀ v, B.semantics B.output v ↔ f v

/-- Distinct successors of a guess node never both accept. -/
def IsUnambiguous (B : BranchingProgram Var) : Prop :=
  ∀ gate children, B.node gate = .guess children →
    ∀ left, left ∈ children → ∀ right, right ∈ children →
      left ≠ right → ∀ v,
        ¬(B.semantics left v ∧ B.semantics right v)

/-- Below a decision on `x`, only variables later than `x` in `order` are
tested: the program reads its variables in that order. -/
def IsOrdered (B : BranchingProgram Var) (order : Var → ℕ) : Prop :=
  ∀ gate x low high, B.node gate = .decision x low high →
    ∀ y, (y ∈ B.support low ∨ y ∈ B.support high) → order x < order y

/-! ### Expansion into a DNNF -/

/-- The five gate roles of the expansion of one node. -/
inductive ProgramExpansionKind where
  | main
  | low
  | high
  | neg
  | pos
  deriving DecidableEq

private def programExpansionKindEquiv : ProgramExpansionKind ≃ Fin 5 where
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
  left_inv := by
    intro kind
    cases kind <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

noncomputable instance : Fintype ProgramExpansionKind :=
  Fintype.ofEquiv (Fin 5) programExpansionKindEquiv.symm

/-- Gate positions of the expansion. -/
abbrev ExpandedGate (B : BranchingProgram Var) := ProgramExpansionKind × B.Gate

private def expandedNode (B : BranchingProgram Var) :
    ExpandedGate B → NNFNode Var (ExpandedGate B)
  | (.main, gate) =>
      match B.node gate with
      | .accept => .top
      | .reject => .bot
      | .decision _ _ _ => .disj [(.low, gate), (.high, gate)]
      | .guess children => .disj (children.map (fun child ↦ (.main, child)))
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

private def expandedRank (B : BranchingProgram Var) : ExpandedGate B → ℕ
  | (.main, gate) => 3 * B.rank gate + 2
  | (.low, gate) => 3 * B.rank gate + 1
  | (.high, gate) => 3 * B.rank gate + 1
  | (.neg, _) => 0
  | (.pos, _) => 0

private def expandedSemantics (B : BranchingProgram Var) :
    ExpandedGate B → (Var → Bool) → Prop
  | (.main, gate), v => B.semantics gate v
  | (.low, gate), v =>
      match B.node gate with
      | .decision x child _ => v x = false ∧ B.semantics child v
      | _ => False
  | (.high, gate), v =>
      match B.node gate with
      | .decision x _ child => v x = true ∧ B.semantics child v
      | _ => False
  | (.neg, gate), v =>
      match B.node gate with
      | .decision x _ _ => v x = false
      | _ => False
  | (.pos, gate), v =>
      match B.node gate with
      | .decision x _ _ => v x = true
      | _ => False

private def expandedSupport (B : BranchingProgram Var) :
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

private theorem expanded_child_rank (B : BranchingProgram Var)
    (gate child : ExpandedGate B)
    (hchild : (expandedNode B gate).IsChild child) :
    expandedRank B child < expandedRank B gate := by
  rcases gate with ⟨kind, gate⟩
  cases kind with
  | main =>
      cases hnode : B.node gate with
      | accept => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | reject => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | decision x low high =>
          simp [expandedNode, NNFNode.IsChild, hnode] at hchild
          rcases hchild with rfl | rfl <;> simp [expandedRank]
      | guess children =>
          simp only [expandedNode, NNFNode.IsChild, hnode, List.mem_map] at hchild
          obtain ⟨source, hsource, rfl⟩ := hchild
          have hr := B.child_rank gate source (by simp [hnode, BPNode.IsChild, hsource])
          simp only [expandedRank]
          omega
  | low =>
      cases hnode : B.node gate with
      | accept => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | reject => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | guess children => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | decision x low high =>
          simp [expandedNode, NNFNode.IsChild, hnode] at hchild
          rcases hchild with rfl | rfl
          · simp [expandedRank]
          · have hr := B.child_rank gate low (by simp [hnode, BPNode.IsChild])
            simp only [expandedRank]
            omega
  | high =>
      cases hnode : B.node gate with
      | accept => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | reject => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | guess children => simp [expandedNode, NNFNode.IsChild, hnode] at hchild
      | decision x low high =>
          simp [expandedNode, NNFNode.IsChild, hnode] at hchild
          rcases hchild with rfl | rfl
          · simp [expandedRank]
          · have hr := B.child_rank gate high (by simp [hnode, BPNode.IsChild])
            simp only [expandedRank]
            omega
  | neg =>
      cases hnode : B.node gate <;>
        simp [expandedNode, NNFNode.IsChild, hnode] at hchild
  | pos =>
      cases hnode : B.node gate <;>
        simp [expandedNode, NNFNode.IsChild, hnode] at hchild

private theorem expanded_semantics_eq (B : BranchingProgram Var)
    (gate : ExpandedGate B) (v : Var → Bool) :
    expandedSemantics B gate v ↔
      (expandedNode B gate).Holds v
        (fun child ↦ expandedSemantics B child v) := by
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hnode : B.node gate <;>
    simp [expandedNode, expandedSemantics, NNFNode.Holds, hnode]
  all_goals
    rw [B.semantics_eq]
    simp [BPNode.Holds, hnode]

private theorem expanded_support_eq (B : BranchingProgram Var)
    (gate : ExpandedGate B) :
    expandedSupport B gate =
      (expandedNode B gate).Support (expandedSupport B) := by
  rcases gate with ⟨kind, gate⟩
  cases kind <;> cases hnode : B.node gate <;>
    simp [expandedNode, expandedSupport, NNFNode.Support, hnode, List.foldl_map]
  all_goals
    rw [B.support_eq]
    simp [BPNode.Support, hnode]

/-- The NNF expansion of a read-once branching program: a decision becomes
`(¬x ∧ low) ∨ (x ∧ high)`, a guess becomes a disjunction. -/
noncomputable def toNNFCircuit (B : BranchingProgram Var) : NNFCircuit Var where
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

theorem toNNFCircuit_computes (B : BranchingProgram Var)
    (f : (Var → Bool) → Prop) (hf : B.Computes f) :
    B.toNNFCircuit.Computes f := by
  intro v
  exact hf v

/-- Read-once programs expand into decomposable circuits: the only
conjunctions pair a decision literal with the successor's subcircuit, and
the variable is not tested there. -/
theorem toNNFCircuit_isDNNF (B : BranchingProgram Var) :
    B.toNNFCircuit.IsDNNF := by
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

theorem toNNFCircuit_size (B : BranchingProgram Var) :
    B.toNNFCircuit.size = 5 * B.size := by
  rw [NNFCircuit.size, size]
  change Fintype.card (ProgramExpansionKind × B.Gate) = 5 * Fintype.card B.Gate
  rw [Fintype.card_prod, Fintype.card_congr programExpansionKindEquiv,
    Fintype.card_fin]

/-! ### Renaming variables -/

section mapVar

variable {Var' : Type*} [DecidableEq Var']

/-- Rename the variables along a bijection.  The node graph is unchanged;
the program reads `e x` where the original read `x`. -/
noncomputable def mapVar (B : BranchingProgram Var) (e : Var ≃ Var') :
    BranchingProgram Var' where
  Gate := B.Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := B.output
  node := fun gate ↦ (B.node gate).mapVar e
  rank := B.rank
  child_rank := by
    intro gate child hchild
    exact B.child_rank gate child ((BPNode.isChild_mapVar e _ child).mp hchild)
  semantics := fun gate v ↦ B.semantics gate (v ∘ e)
  semantics_eq := by
    intro gate v
    rw [B.semantics_eq gate (v ∘ e)]
    cases B.node gate <;> simp [BPNode.mapVar, BPNode.Holds]
  support := fun gate ↦ (B.support gate).map e.toEmbedding
  support_eq := by
    intro gate
    conv_lhs => rw [B.support_eq gate]
    cases B.node gate with
    | accept => simp [BPNode.mapVar, BPNode.Support]
    | reject => simp [BPNode.mapVar, BPNode.Support]
    | decision x low high =>
        simp [BPNode.mapVar, BPNode.Support, Finset.map_insert, Finset.map_union]
    | guess children =>
        simp only [BPNode.mapVar, BPNode.Support]
        rw [map_foldl_union, Finset.map_empty]
  readOnce := by
    intro gate x low high hnode
    cases hlocal : B.node gate with
    | accept => simp [BPNode.mapVar, hlocal] at hnode
    | reject => simp [BPNode.mapVar, hlocal] at hnode
    | guess children => simp [BPNode.mapVar, hlocal] at hnode
    | decision x' low' high' =>
        simp only [BPNode.mapVar, hlocal] at hnode
        injection hnode with hx hlow hhigh
        subst hx
        subst hlow
        subst hhigh
        have hro := B.readOnce gate x' low' high' hlocal
        simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
        exact hro

theorem mapVar_size (B : BranchingProgram Var) (e : Var ≃ Var') :
    (B.mapVar e).size = B.size := rfl

theorem mapVar_computes (B : BranchingProgram Var) (e : Var ≃ Var')
    {f : (Var → Bool) → Prop} (h : B.Computes f) :
    (B.mapVar e).Computes (fun v ↦ f (v ∘ e)) := by
  intro v
  exact h (v ∘ e)

theorem mapVar_isUnambiguous (B : BranchingProgram Var) (e : Var ≃ Var')
    (h : B.IsUnambiguous) : (B.mapVar e).IsUnambiguous := by
  intro gate children hnode left hleft right hright hne v
  cases hlocal : B.node gate <;> simp [mapVar, BPNode.mapVar, hlocal] at hnode
  injection hnode with hchildren
  subst hchildren
  exact h gate _ hlocal left hleft right hright hne (v ∘ e)

theorem mapVar_isOrdered (B : BranchingProgram Var) (e : Var ≃ Var')
    (order : Var → ℕ) (h : B.IsOrdered order) :
    (B.mapVar e).IsOrdered (fun y ↦ order (e.symm y)) := by
  intro gate x low high hnode y hy
  cases hlocal : B.node gate with
  | accept => simp [mapVar, BPNode.mapVar, hlocal] at hnode
  | reject => simp [mapVar, BPNode.mapVar, hlocal] at hnode
  | guess children => simp [mapVar, BPNode.mapVar, hlocal] at hnode
  | decision x' low' high' =>
      simp only [mapVar, BPNode.mapVar, hlocal] at hnode
      injection hnode with hx hlow hhigh
      subst hx
      subst hlow
      subst hhigh
      simp only [Equiv.symm_apply_apply]
      change y ∈ (B.support low').map e.toEmbedding ∨
        y ∈ (B.support high').map e.toEmbedding at hy
      rcases hy with hy | hy
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
        simpa using h gate x' low' high' hlocal z (Or.inl hz)
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
        simpa using h gate x' low' high' hlocal z (Or.inr hz)

end mapVar

/-! ### A guess node above a family of programs -/

section guessUnion

variable {J : Type*} [Fintype J]

/-- A node of one member of a family of programs. -/
abbrev ComponentGate (B : J → BranchingProgram Var) :=
  Σ j, (B j).Gate

/-- The family's nodes plus one root guess node (`none`). -/
abbrev UnionGate (B : J → BranchingProgram Var) :=
  Option (ComponentGate B)

private noncomputable def rootChildren (B : J → BranchingProgram Var) :
    List (UnionGate B) :=
  (Finset.univ : Finset J).toList.map (fun j ↦ some ⟨j, (B j).output⟩)

private noncomputable def unionNode (B : J → BranchingProgram Var) :
    UnionGate B → BPNode Var (UnionGate B)
  | none => .guess (rootChildren B)
  | some ⟨j, gate⟩ => ((B j).node gate).map (fun child ↦ some ⟨j, child⟩)

private noncomputable def unionMaxRank (B : J → BranchingProgram Var) : ℕ :=
  Finset.univ.sup (fun gate : ComponentGate B ↦ (B gate.1).rank gate.2)

private noncomputable def unionRank (B : J → BranchingProgram Var) :
    UnionGate B → ℕ
  | none => unionMaxRank B + 1
  | some ⟨j, gate⟩ => (B j).rank gate

private def unionSemantics (B : J → BranchingProgram Var) :
    UnionGate B → (Var → Bool) → Prop
  | none, v => ∃ j, (B j).semantics (B j).output v
  | some ⟨j, gate⟩, v => (B j).semantics gate v

private noncomputable def unionSupport (B : J → BranchingProgram Var) :
    UnionGate B → Finset Var
  | none => Finset.univ.biUnion (fun j ↦ (B j).support (B j).output)
  | some ⟨j, gate⟩ => (B j).support gate

private theorem mem_rootChildren (B : J → BranchingProgram Var)
    (gate : UnionGate B) :
    gate ∈ rootChildren B ↔ ∃ j, gate = some ⟨j, (B j).output⟩ := by
  simp only [rootChildren, List.mem_map, Finset.mem_toList, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

private theorem union_child_rank (B : J → BranchingProgram Var)
    (gate child : UnionGate B)
    (hchild : (unionNode B gate).IsChild child) :
    unionRank B child < unionRank B gate := by
  cases gate with
  | none =>
      simp only [unionNode, BPNode.IsChild] at hchild
      obtain ⟨j, rfl⟩ := (mem_rootChildren B child).mp hchild
      simp only [unionRank]
      have hle : (B j).rank (B j).output ≤ unionMaxRank B :=
        Finset.le_sup (f := fun gate : ComponentGate B ↦ (B gate.1).rank gate.2)
          (Finset.mem_univ (⟨j, (B j).output⟩ : ComponentGate B))
      omega
  | some component =>
      rcases component with ⟨j, gate⟩
      obtain ⟨source, hsource, rfl⟩ :=
        BPNode.isChild_map_exists _ ((B j).node gate) child hchild
      simpa [unionRank] using (B j).child_rank gate source hsource

private theorem union_semantics_eq (B : J → BranchingProgram Var)
    (gate : UnionGate B) (v : Var → Bool) :
    unionSemantics B gate v ↔
      (unionNode B gate).Holds v (fun child ↦ unionSemantics B child v) := by
  cases gate with
  | none =>
      simp only [unionNode, BPNode.Holds, unionSemantics]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨some ⟨j, (B j).output⟩, (mem_rootChildren B _).mpr ⟨j, rfl⟩, hj⟩
      · rintro ⟨child, hchild, hsem⟩
        obtain ⟨j, rfl⟩ := (mem_rootChildren B child).mp hchild
        exact ⟨j, hsem⟩
  | some component =>
      rcases component with ⟨j, gate⟩
      simp only [unionNode]
      rw [BPNode.holds_map]
      exact (B j).semantics_eq gate v

private theorem union_support_eq (B : J → BranchingProgram Var)
    (gate : UnionGate B) :
    unionSupport B gate = (unionNode B gate).Support (unionSupport B) := by
  cases gate with
  | none =>
      simp only [unionNode, BPNode.Support, unionSupport]
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_foldl_union,
        Finset.notMem_empty, false_or]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨some ⟨j, (B j).output⟩, (mem_rootChildren B _).mpr ⟨j, rfl⟩, hj⟩
      · rintro ⟨child, hchild, hy⟩
        obtain ⟨j, rfl⟩ := (mem_rootChildren B child).mp hchild
        exact ⟨j, hy⟩
  | some component =>
      rcases component with ⟨j, gate⟩
      simp only [unionNode]
      rw [BPNode.support_map]
      exact (B j).support_eq gate

private theorem union_readOnce (B : J → BranchingProgram Var)
    (gate : UnionGate B) (x : Var) (low high : UnionGate B)
    (hnode : unionNode B gate = .decision x low high) :
    x ∉ unionSupport B low ∧ x ∉ unionSupport B high := by
  cases gate with
  | none => simp [unionNode] at hnode
  | some component =>
      rcases component with ⟨j, gate⟩
      cases hlocal : (B j).node gate with
      | accept => simp [unionNode, BPNode.map, hlocal] at hnode
      | reject => simp [unionNode, BPNode.map, hlocal] at hnode
      | guess children => simp [unionNode, BPNode.map, hlocal] at hnode
      | decision x' low' high' =>
          simp only [unionNode, BPNode.map, hlocal] at hnode
          injection hnode with hx hlow hhigh
          subst hx
          subst hlow
          subst hhigh
          exact (B j).readOnce gate x' low' high' hlocal

/-- One guess node above a family of programs: the nondeterministic choice
of a member, followed by that member's program. -/
noncomputable def guessUnion [DecidableEq J] (B : J → BranchingProgram Var) :
    BranchingProgram Var where
  Gate := UnionGate B
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := none
  node := unionNode B
  rank := unionRank B
  child_rank := union_child_rank B
  semantics := unionSemantics B
  semantics_eq := union_semantics_eq B
  support := unionSupport B
  support_eq := union_support_eq B
  readOnce := union_readOnce B

theorem guessUnion_computes [DecidableEq J] (B : J → BranchingProgram Var)
    (f : J → (Var → Bool) → Prop) (hcomputes : ∀ j, (B j).Computes (f j)) :
    (guessUnion B).Computes (fun v ↦ ∃ j, f j v) := by
  intro v
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (hcomputes j v).mp hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (hcomputes j v).mpr hj⟩

theorem guessUnion_size [DecidableEq J] (B : J → BranchingProgram Var) :
    (guessUnion B).size = (∑ j, (B j).size) + 1 := by
  show Fintype.card (Option (Σ j, (B j).Gate)) = _
  rw [Fintype.card_option, Fintype.card_sigma]
  rfl

/-- The union is unambiguous when each member is and distinct members never
accept the same assignment. -/
theorem guessUnion_isUnambiguous [DecidableEq J] (B : J → BranchingProgram Var)
    (hunamb : ∀ j, (B j).IsUnambiguous)
    (hdisjoint : ∀ j k, j ≠ k → ∀ v,
      ¬((B j).semantics (B j).output v ∧ (B k).semantics (B k).output v)) :
    (guessUnion B).IsUnambiguous := by
  intro gate children hnode left hleft right hright hne v
  cases gate with
  | none =>
      simp only [guessUnion, unionNode] at hnode
      injection hnode with hchildren
      subst hchildren
      obtain ⟨j, rfl⟩ := (mem_rootChildren B left).mp hleft
      obtain ⟨k, rfl⟩ := (mem_rootChildren B right).mp hright
      have hjk : j ≠ k := by
        rintro rfl
        exact hne rfl
      exact hdisjoint j k hjk v
  | some component =>
      rcases component with ⟨j, gate⟩
      cases hlocal : (B j).node gate with
      | accept => simp [guessUnion, unionNode, BPNode.map, hlocal] at hnode
      | reject => simp [guessUnion, unionNode, BPNode.map, hlocal] at hnode
      | decision x low high =>
          simp [guessUnion, unionNode, BPNode.map, hlocal] at hnode
      | guess children' =>
          simp only [guessUnion, unionNode, BPNode.map, hlocal] at hnode
          injection hnode with hchildren
          subst hchildren
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hleft
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hright
          have hlr : l ≠ r := fun heq ↦ hne (by rw [heq])
          exact hunamb j gate _ hlocal l hl r hr hlr v

/-- The union reads in an order when every member does. -/
theorem guessUnion_isOrdered [DecidableEq J] (B : J → BranchingProgram Var)
    (order : Var → ℕ)
    (hordered : ∀ j, (B j).IsOrdered order) :
    (guessUnion B).IsOrdered order := by
  intro gate x low high hnode y hy
  cases gate with
  | none => simp [guessUnion, unionNode] at hnode
  | some component =>
      rcases component with ⟨j, gate⟩
      cases hlocal : (B j).node gate with
      | accept => simp [guessUnion, unionNode, BPNode.map, hlocal] at hnode
      | reject => simp [guessUnion, unionNode, BPNode.map, hlocal] at hnode
      | guess children => simp [guessUnion, unionNode, BPNode.map, hlocal] at hnode
      | decision x' low' high' =>
          simp only [guessUnion, unionNode, BPNode.map, hlocal] at hnode
          injection hnode with hx hlow hhigh
          subst hx
          subst hlow
          subst hhigh
          exact hordered j gate x' low' high' hlocal y hy

end guessUnion

end BranchingProgram

/-! ## Deterministic OBDDs are branching programs -/

namespace OBDDNode

variable {Var Gate : Type*}

/-- A decision-diagram node as a branching-program node. -/
def toBPNode : OBDDNode Var Gate → BPNode Var Gate
  | accept => .accept
  | reject => .reject
  | decision x low high => .decision x low high

end OBDDNode

namespace ReadOnceOBDD

variable {Var : Type*} [DecidableEq Var]

/-- A read-once OBDD is a branching program without guess nodes. -/
noncomputable def toBranchingProgram (B : ReadOnceOBDD Var) :
    BranchingProgram Var where
  Gate := B.Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := B.output
  node := fun gate ↦ (B.node gate).toBPNode
  rank := B.rank
  child_rank := by
    intro gate child hchild
    apply B.child_rank gate child
    cases hlocal : B.node gate <;>
      simp [OBDDNode.toBPNode, BPNode.IsChild, OBDDNode.IsChild, hlocal] at hchild ⊢
    exact hchild
  semantics := B.semantics
  semantics_eq := by
    intro gate v
    rw [B.semantics_eq gate v]
    cases B.node gate <;> simp [OBDDNode.toBPNode, BPNode.Holds, OBDDNode.Holds]
  support := B.support
  support_eq := by
    intro gate
    conv_lhs => rw [B.support_eq gate]
    cases B.node gate <;> simp [OBDDNode.toBPNode, BPNode.Support, OBDDNode.Support]
  readOnce := by
    intro gate x low high hnode
    apply B.readOnce gate x low high
    cases hlocal : B.node gate <;> simp [OBDDNode.toBPNode, hlocal] at hnode
    obtain ⟨rfl, rfl, rfl⟩ := hnode
    rfl

theorem toBranchingProgram_size (B : ReadOnceOBDD Var) :
    B.toBranchingProgram.size = B.size := rfl

/-- A decision of the program is a decision of the diagram. -/
theorem toBranchingProgram_node_decision (B : ReadOnceOBDD Var)
    (gate : B.Gate) (x : Var) (low high : B.Gate)
    (hnode : B.toBranchingProgram.node gate = .decision x low high) :
    B.node gate = .decision x low high := by
  revert hnode
  cases hlocal : B.node gate <;> intro hnode <;>
    simp [toBranchingProgram, OBDDNode.toBPNode, hlocal] at hnode
  obtain ⟨rfl, rfl, rfl⟩ := hnode
  rfl

theorem toBranchingProgram_computes (B : ReadOnceOBDD Var)
    {f : (Var → Bool) → Prop} (h : B.Computes f) :
    B.toBranchingProgram.Computes f := h

/-- A program without guess nodes is trivially unambiguous. -/
theorem toBranchingProgram_isUnambiguous (B : ReadOnceOBDD Var) :
    B.toBranchingProgram.IsUnambiguous := by
  intro gate children hnode
  cases hlocal : B.node gate <;>
    simp [toBranchingProgram, OBDDNode.toBPNode, hlocal] at hnode

end ReadOnceOBDD

/-- A layered OBDD reads the positions in increasing order: below a
decision at one layer only later positions are tested. -/
theorem LayeredOBDD.ofTransition_isOrdered {N : ℕ} {State : Type*}
    [Fintype State] [DecidableEq State]
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) :
    (LayeredOBDD.ofTransition step accept start).toBranchingProgram.IsOrdered
      (fun x ↦ x.val) := by
  intro gate x low high hnode y hy
  have hnode' := ReadOnceOBDD.toBranchingProgram_node_decision _ gate x low high hnode
  have hro := (LayeredOBDD.ofTransition step accept start).readOnce gate x low high hnode'
  have hlow : (LayeredOBDD.ofTransition step accept start).support low =
      Finset.univ.filter (fun j : Fin N ↦ low.1.1 ≤ j.1) := rfl
  have hhigh : (LayeredOBDD.ofTransition step accept start).support high =
      Finset.univ.filter (fun j : Fin N ↦ high.1.1 ≤ j.1) := rfl
  change y ∈ (LayeredOBDD.ofTransition step accept start).support low ∨
    y ∈ (LayeredOBDD.ofTransition step accept start).support high at hy
  show x.val < y.val
  rcases hy with hy | hy
  · rw [hlow] at hy
    have hx := hro.1
    rw [hlow] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy hx
    omega
  · rw [hhigh] at hy
    have hx := hro.2
    rw [hhigh] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy hx
    omega

/-! ## The unambiguous OBDD for `L_n` in every order -/

section positive

variable {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
  {bitCount : ℕ} (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))

/-- Reindexing the columns and the assignment by the same bijection leaves
the subset sum unchanged. -/
theorem subsetSum_comp_equiv {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid G] (b : ι → G) (x : ι → Bool) (σ : Equiv.Perm ι) :
    subsetSum (b ∘ σ) (x ∘ σ) = subsetSum b x := by
  unfold subsetSum
  exact Equiv.sum_comp σ (fun i ↦ if x i then b i else 0)

theorem encodedTermState_comp_equiv (σ : Equiv.Perm (Fin bitCount))
    (T : ThresholdTerm n) (x : Fin bitCount → Bool) :
    encodedTermState ranks hn (a ∘ σ) T (x ∘ σ) =
      encodedTermState ranks hn a T x := by
  unfold encodedTermState
  exact subsetSum_comp_equiv (encodedTermColumns ranks hn a T) x σ

/-- The term OBDD read in the variable order `σ`: the layered OBDD for the
permuted columns, with position `i` renamed to `σ i`. -/
noncomputable def encodedTermProgram (σ : Equiv.Perm (Fin bitCount))
    (T : ThresholdTerm n) : BranchingProgram (Fin bitCount) :=
  (encodedTermOBDD ranks hn (a ∘ σ) T).toBranchingProgram.mapVar σ

theorem encodedTermProgram_computes (σ : Equiv.Perm (Fin bitCount))
    (T : ThresholdTerm n) :
    (encodedTermProgram ranks hn a σ T).Computes
      (fun x ↦ encodedTermStateAccepts ranks hn T
        (encodedTermState ranks hn a T x)) := by
  intro x
  have h := BranchingProgram.mapVar_computes _ σ
    ((encodedTermOBDD ranks hn (a ∘ σ) T).toBranchingProgram_computes
      (encodedTermOBDD_computes ranks hn (a ∘ σ) T)) x
  simp only [encodedTermState_comp_equiv] at h
  exact h

theorem encodedTermProgram_size (σ : Equiv.Perm (Fin bitCount))
    (T : ThresholdTerm n) :
    (encodedTermProgram ranks hn a σ T).size =
      (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card := by
  rw [encodedTermProgram, BranchingProgram.mapVar_size,
    ReadOnceOBDD.toBranchingProgram_size, encodedTermOBDD_size]

theorem encodedTermProgram_isOrdered (σ : Equiv.Perm (Fin bitCount))
    (T : ThresholdTerm n) :
    (encodedTermProgram ranks hn a σ T).IsOrdered (fun y ↦ (σ.symm y).val) :=
  BranchingProgram.mapVar_isOrdered _ σ _
    (LayeredOBDD.ofTransition_isOrdered _ _ _)

theorem encodedTermProgram_isUnambiguous (σ : Equiv.Perm (Fin bitCount))
    (T : ThresholdTerm n) :
    (encodedTermProgram ranks hn a σ T).IsUnambiguous :=
  BranchingProgram.mapVar_isUnambiguous _ σ
    (ReadOnceOBDD.toBranchingProgram_isUnambiguous _)

/-- The unambiguous OBDD for `L_n` in the order `σ`: guess a term, then run
its OBDD. -/
noncomputable def encodedOuterProgram (σ : Equiv.Perm (Fin bitCount)) :
    BranchingProgram (Fin bitCount) := by
  letI := Classical.decEq (ThresholdTerm n)
  exact BranchingProgram.guessUnion
    (fun T : ThresholdTerm n ↦ encodedTermProgram ranks hn a σ T)

theorem encodedOuterProgram_computes (σ : Equiv.Perm (Fin bitCount)) :
    (encodedOuterProgram ranks hn a σ).Computes (hardFunction ranks hn a) := by
  classical
  intro x
  rw [hardFunction_iff_exists_termStateAccepts]
  unfold encodedOuterProgram
  exact BranchingProgram.guessUnion_computes _ _
    (fun T ↦ encodedTermProgram_computes ranks hn a σ T) x

theorem encodedOuterProgram_isUnambiguous (σ : Equiv.Perm (Fin bitCount)) :
    (encodedOuterProgram ranks hn a σ).IsUnambiguous := by
  classical
  unfold encodedOuterProgram
  apply BranchingProgram.guessUnion_isUnambiguous
  · intro T
    exact encodedTermProgram_isUnambiguous ranks hn a σ T
  · intro T U hTU x hboth
    have hT := (encodedTermProgram_computes ranks hn a σ T x).mp hboth.1
    have hU := (encodedTermProgram_computes ranks hn a σ U x).mp hboth.2
    exact hTU (encodedTermStates_unambiguous ranks hn a x hT hU)

theorem encodedOuterProgram_isOrdered (σ : Equiv.Perm (Fin bitCount)) :
    (encodedOuterProgram ranks hn a σ).IsOrdered (fun y ↦ (σ.symm y).val) := by
  classical
  unfold encodedOuterProgram
  apply BranchingProgram.guessUnion_isOrdered
  intro T
  exact encodedTermProgram_isOrdered ranks hn a σ T

theorem encodedOuterProgram_size_le_of_width {width : ℕ}
    (σ : Equiv.Perm (Fin bitCount))
    (hwidth : ∀ T : ThresholdTerm n,
      (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤ width) :
    (encodedOuterProgram ranks hn a σ).size ≤
      1 + Fintype.card (ThresholdTerm n) * ((bitCount + 1) * 16 ^ width) := by
  classical
  unfold encodedOuterProgram
  rw [BranchingProgram.guessUnion_size]
  rw [add_comm]
  apply Nat.add_le_add_left
  calc (∑ T : ThresholdTerm n, (encodedTermProgram ranks hn a σ T).size)
      = ∑ T : ThresholdTerm n,
          (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card := by
        apply Finset.sum_congr rfl
        intro T _
        exact encodedTermProgram_size ranks hn a σ T
    _ ≤ ∑ _T : ThresholdTerm n, (bitCount + 1) * 16 ^ width := by
        apply Finset.sum_le_sum
        intro T _
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by norm_num)
        exact card_encodedTermSupport_le ranks hn T (hwidth T)
    _ = Fintype.card (ThresholdTerm n) * ((bitCount + 1) * 16 ^ width) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end positive

/-! ## The corollary -/

/-- The explicit node bound of the unambiguous OBDD, `2^{O(n)}`. -/
abbrev unambiguousOBDDBound (n : ℕ) : ℕ :=
  1 + n * 2 ^ n * ((encodedInputCount n + 1) * 16 ^ (10 * n))

theorem unambiguousOBDDBound_le_two_pow (n : ℕ) (hn : 13 ≤ n) :
    unambiguousOBDDBound n ≤ 2 ^ (45 * n) := by
  apply le_trans ?_ (positiveCircuitBound_le_two_pow n hn)
  unfold unambiguousOBDDBound positiveCircuitBound
  have ha : 1 ≤ n * 2 ^ n := Nat.mul_pos (by omega) (Nat.two_pow_pos n)
  nlinarith [Nat.zero_le ((encodedInputCount n + 1) * 16 ^ (10 * n))]

/-- The positive side for one choice of short label orders and any encoder:
an unambiguous OBDD for `L_n` in every variable order. -/
theorem exists_unambiguous_obdd_every_order {n : ℕ} (ranks : LabelOrders n)
    (hn : 0 < n)
    (hwidth : ∀ T : ThresholdTerm n,
      (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤ 10 * n)
    (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))
    (σ : Equiv.Perm (Fin (encodedInputCount n))) :
    ∃ B : BranchingProgram.{0, 0} (Fin (encodedInputCount n)),
      B.IsOrdered (fun y ↦ (σ.symm y).val) ∧
      B.IsUnambiguous ∧
      B.Computes (hardFunction ranks hn a) ∧
      B.size ≤ unambiguousOBDDBound n := by
  refine ⟨encodedOuterProgram ranks hn a σ,
    encodedOuterProgram_isOrdered ranks hn a σ,
    encodedOuterProgram_isUnambiguous ranks hn a σ,
    encodedOuterProgram_computes ranks hn a σ, ?_⟩
  calc (encodedOuterProgram ranks hn a σ).size
      ≤ 1 + Fintype.card (ThresholdTerm n) *
          ((encodedInputCount n + 1) * 16 ^ (10 * n)) :=
        encodedOuterProgram_size_le_of_width ranks hn a σ hwidth
    _ ≤ unambiguousOBDDBound n := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ (card_thresholdTerm_le n)

/-- The paper's corollary.  For every variable order `σ`
(the program reads `x_{σ 0}, x_{σ 1}, …`), `L_n` has an unambiguous OBDD in
that order with at most `unambiguousOBDDBound n` nodes, which is at most
`2^{45 n}` for `n ≥ 13`; and every DNNF for `¬L_n` has at least
`spectralNodeLower n` nodes, which is `2^{Ω(n²)}`.  The lower bound is the
main theorem's, restated next to the positive side in the paper's own
model of the positive side. -/
@[tutorial_box "cor:paper-uobdd"]
theorem unambiguous_obdd_separation (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      (∀ σ : Equiv.Perm (Fin (encodedInputCount n)),
        ∃ B : BranchingProgram.{0, 0} (Fin (encodedInputCount n)),
          B.IsOrdered (fun y ↦ (σ.symm y).val) ∧
          B.IsUnambiguous ∧
          B.Computes (hardFunction ranks hn a) ∧
          B.size ≤ unambiguousOBDDBound n) ∧
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
        spectralNodeLower n ≤ (D.size : ℝ) := by
  obtain ⟨ranks, hwidth⟩ := every_term_short hn
  obtain ⟨a, hlower⟩ := DNNF_lower_bound_nodes n hn ranks
  exact ⟨ranks, a, fun σ ↦ exists_unambiguous_obdd_every_order ranks hn hwidth a σ, hlower⟩

end DDNNFNegation
