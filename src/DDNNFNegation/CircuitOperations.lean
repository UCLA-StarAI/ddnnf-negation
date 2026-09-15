import DDNNFNegation.Circuit

/-!
# Operations on shared NNF circuits

Relabeling gates preserves the graph; relabeling variables preserves its
semantics after the corresponding substitution. Restriction fixes selected
variables to constants. `disjointOr` joins a finite family of circuits with
one new OR gate. Separate lemmas establish the semantics, class properties,
and size bounds used in the easy-side construction and padding argument.
-/

namespace DDNNFNegation

open Finset

section

namespace NNFNode

/-- Rename all child references of one local gate.  This is gate
relabeling, so it lives here rather than in the trust boundary: the
claim does not mention it. -/
def map {Var Gate Gate' : Type*} (f : Gate → Gate') :
    NNFNode Var Gate → NNFNode Var Gate'
  | top => top
  | bot => bot
  | pos x => pos x
  | neg x => neg x
  | conj left right => conj (f left) (f right)
  | disj children => disj (children.map f)

end NNFNode

variable {Var : Type*} [DecidableEq Var]

namespace NNFNode

variable {Gate Gate' : Type*}

omit [DecidableEq Var] in
/-- A child after relabeling comes from an original child, even when the label map
identifies gates. -/
theorem isChild_map_exists (node : NNFNode Var Gate) (f : Gate → Gate')
    (child : Gate') (hchild : (node.map f).IsChild child) :
    ∃ source, node.IsChild source ∧ f source = child := by
  cases node <;> simp [NNFNode.map, NNFNode.IsChild] at hchild ⊢
  · rcases hchild with rfl | rfl <;> simp
  · obtain ⟨source, hmem, rfl⟩ := hchild
    exact ⟨source, hmem, rfl⟩

omit [DecidableEq Var] in
/-- Relabeling node references transports truth by composition with the label map. -/
theorem holds_map (node : NNFNode Var Gate) (f : Gate → Gate')
    (v : Var → Bool) (child : Gate' → Prop) :
    (node.map f).Holds v child ↔ node.Holds v (fun gate ↦ child (f gate)) := by
  cases node <;> simp [NNFNode.map, NNFNode.Holds]

/-- Relabeling node references transports the union of child supports. -/
theorem support_map (node : NNFNode Var Gate)
    (f : Gate → Gate') (child : Gate' → Finset Var) :
    (node.map f).Support child = node.Support (fun gate ↦ child (f gate)) := by
  cases node <;> simp [NNFNode.map, NNFNode.Support, List.foldl_map]

omit [DecidableEq Var] in
/-- Relabeling the inputs keeps their number. -/
theorem fanIn_map (node : NNFNode Var Gate) (f : Gate → Gate') :
    (node.map f).fanIn = node.fanIn := by
  cases node <;> simp [NNFNode.map, NNFNode.fanIn]

omit [DecidableEq Var] in
/-- A transported node is a conjunction exactly when the original is, with
the children carried across. -/
theorem map_eq_conj_iff (e : Gate ≃ Gate') (node : NNFNode Var Gate)
    (left right : Gate') :
    node.map e = .conj left right ↔ node = .conj (e.symm left) (e.symm right) := by
  cases node <;> simp [NNFNode.map, Equiv.eq_symm_apply]

end NNFNode

namespace NNFCircuit

/-- Carry a circuit along an equivalence of its gate type with any other
finite type.  Nothing about the circuit changes except the names of the
gates. -/
def transportGates {Gate' : Type*} [Fintype Gate'] [DecidableEq Gate']
    (C : NNFCircuit Var) (e : C.Gate ≃ Gate') : NNFCircuit Var where
  Gate := Gate'
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := e C.output
  node := fun gate ↦ (C.node (e.symm gate)).map e
  rank := fun gate ↦ C.rank (e.symm gate)
  child_rank := by
    intro gate child hchild
    obtain ⟨source, hsource, rfl⟩ :=
      NNFNode.isChild_map_exists (C.node (e.symm gate)) e child hchild
    simpa using C.child_rank (e.symm gate) source hsource
  semantics := fun gate v ↦ C.semantics (e.symm gate) v
  semantics_eq := by
    intro gate v
    rw [NNFNode.holds_map]
    simpa using C.semantics_eq (e.symm gate) v
  support := fun gate ↦ C.support (e.symm gate)
  support_eq := by
    intro gate
    rw [NNFNode.support_map]
    simpa using C.support_eq (e.symm gate)

/-- Renumbering gates preserves their computed Boolean values. -/
@[simp]
theorem transportGates_semantics {Gate' : Type*} [Fintype Gate'] [DecidableEq Gate']
    (C : NNFCircuit Var) (e : C.Gate ≃ Gate') (gate : Gate') (v : Var → Bool) :
    (C.transportGates e).semantics gate v ↔ C.semantics (e.symm gate) v := Iff.rfl

/-- Transport preserves the computed function. -/
theorem computes_transportGates {Gate' : Type*} [Fintype Gate'] [DecidableEq Gate']
    (C : NNFCircuit Var) (e : C.Gate ≃ Gate') (f : (Var → Bool) → Prop)
    (h : C.Computes f) : (C.transportGates e).Computes f := by
  intro v
  have : (C.transportGates e).output = e C.output := rfl
  rw [Computes] at h
  simpa [this] using h v

/-- Transport preserves decomposability. -/
theorem isDecomposable_transportGates {Gate' : Type*} [Fintype Gate'] [DecidableEq Gate']
    (C : NNFCircuit Var) (e : C.Gate ≃ Gate') (h : C.IsDecomposable) :
    (C.transportGates e).IsDecomposable := by
  intro gate left right hnode
  have hnode' : C.node (e.symm gate) = .conj (e.symm left) (e.symm right) :=
    (NNFNode.map_eq_conj_iff e (C.node (e.symm gate)) left right).mp hnode
  exact h (e.symm gate) (e.symm left) (e.symm right) hnode'

/-- Transport preserves the DNNF property. -/
theorem isDNNF_transportGates {Gate' : Type*} [Fintype Gate'] [DecidableEq Gate']
    (C : NNFCircuit Var) (e : C.Gate ≃ Gate') (h : C.IsDNNF) :
    (C.transportGates e).IsDNNF :=
  isDecomposable_transportGates C e h

/-- **Every circuit is isomorphic to one whose gates live in the lowest
universe.**  The gate type is finite, so numbering the gates by
`Fin (size C)` loses nothing. -/
noncomputable def toFinGates (C : NNFCircuit Var) : NNFCircuit.{_, 0} Var :=
  C.transportGates (Fintype.equivFin C.Gate)

/-- Finite gate numbering preserves the function at the circuit output. -/
theorem computes_toFinGates (C : NNFCircuit Var) (f : (Var → Bool) → Prop)
    (h : C.Computes f) : C.toFinGates.Computes f :=
  computes_transportGates C _ f h

/-- Finite gate numbering preserves decomposability. -/
theorem isDNNF_toFinGates (C : NNFCircuit Var) (h : C.IsDNNF) :
    C.toFinGates.IsDNNF :=
  isDNNF_transportGates C _ h

end NNFCircuit

end

namespace NNFNode

/-- Relabel the variables in one local NNF node. -/
def mapVariables {Var Var' Gate : Type*} (f : Var → Var') :
    NNFNode Var Gate → NNFNode Var' Gate
  | .top => .top
  | .bot => .bot
  | .pos x => .pos (f x)
  | .neg x => .neg (f x)
  | .conj left right => .conj left right
  | .disj children => .disj children

@[simp] theorem isChild_mapVariables_iff
    {Var Var' Gate : Type*} (f : Var → Var')
    (node : NNFNode Var Gate) (child : Gate) :
    (node.mapVariables f).IsChild child ↔ node.IsChild child := by
  cases node <;> simp [mapVariables, IsChild]

@[simp] theorem holds_mapVariables_iff
    {Var Var' Gate : Type*} (f : Var → Var')
    (node : NNFNode Var Gate) (v : Var' → Bool) (child : Gate → Prop) :
    (node.mapVariables f).Holds v child ↔
      node.Holds (v ∘ f) child := by
  cases node <;> simp [mapVariables, Holds, Function.comp_apply]

/-- Replace variables from the right summand by constants. -/
def restrictRightVariables {Var Extra Gate : Type*}
    (fixed : Extra → Bool) :
    NNFNode (Var ⊕ Extra) Gate → NNFNode Var Gate
  | .top => .top
  | .bot => .bot
  | .pos (.inl x) => .pos x
  | .pos (.inr y) => if fixed y then .top else .bot
  | .neg (.inl x) => .neg x
  | .neg (.inr y) => if fixed y then .bot else .top
  | .conj left right => .conj left right
  | .disj children => .disj children

@[simp] theorem isChild_restrictRightVariables_iff
    {Var Extra Gate : Type*} (fixed : Extra → Bool)
    (node : NNFNode (Var ⊕ Extra) Gate) (child : Gate) :
    (node.restrictRightVariables fixed).IsChild child ↔
      node.IsChild child := by
  cases node with
  | top | bot | conj | disj =>
      simp [restrictRightVariables, IsChild]
  | pos x | neg x =>
      cases x with
      | inl x => simp [restrictRightVariables, IsChild]
      | inr y =>
          cases h : fixed y <;> simp [restrictRightVariables, IsChild, h]

@[simp] theorem holds_restrictRightVariables_iff
    {Var Extra Gate : Type*} (fixed : Extra → Bool)
    (node : NNFNode (Var ⊕ Extra) Gate) (v : Var → Bool)
    (child : Gate → Prop) :
    (node.restrictRightVariables fixed).Holds v child ↔
      node.Holds (Sum.elim v fixed) child := by
  cases node with
  | top | bot | conj | disj =>
      simp [restrictRightVariables, Holds]
  | pos x | neg x =>
      cases x with
      | inl x => simp [restrictRightVariables, Holds]
      | inr y =>
          cases h : fixed y <;> simp [restrictRightVariables, Holds, h]

/-- Changing variable labels does not change whether a node is a binary conjunction. -/
theorem mapVariables_eq_conj_iff
    {Var Var' Gate : Type*} (f : Var → Var')
    (node : NNFNode Var Gate) (left right : Gate) :
    node.mapVariables f = .conj left right ↔
      node = .conj left right := by
  cases node <;> simp [mapVariables]

/-- Changing variable labels does not change whether a node is a disjunction. -/
theorem mapVariables_eq_disj_iff
    {Var Var' Gate : Type*} (f : Var → Var')
    (node : NNFNode Var Gate) (children : List Gate) :
    node.mapVariables f = .disj children ↔
      node = .disj children := by
  cases node <;> simp [mapVariables]

/-- Fixing extra variables changes literals but leaves conjunction nodes intact. -/
theorem restrictRightVariables_eq_conj_iff
    {Var Extra Gate : Type*} (fixed : Extra → Bool)
    (node : NNFNode (Var ⊕ Extra) Gate) (left right : Gate) :
    node.restrictRightVariables fixed = .conj left right ↔
      node = .conj left right := by
  cases node with
  | top | bot | conj | disj =>
      simp [restrictRightVariables]
  | pos x | neg x =>
      cases x with
      | inl x => simp [restrictRightVariables]
      | inr y =>
          cases h : fixed y <;> simp [restrictRightVariables, h]

end NNFNode

namespace NNFCircuit

noncomputable section

variable {Var Var' Extra : Type*}
  [DecidableEq Var] [DecidableEq Var'] [DecidableEq Extra]

private theorem map_foldl_union
    {Gate : Type*} (e : Var ↪ Var') (support : Gate → Finset Var)
    (children : List Gate) (initial : Finset Var) :
    (children.foldl (fun result gate ↦ result ∪ support gate) initial).map e =
      children.foldl
        (fun result gate ↦ result ∪ (support gate).map e)
        (initial.map e) := by
  induction children generalizing initial with
  | nil => rfl
  | cons gate children ih =>
      simp only [List.foldl_cons]
      rw [ih, Finset.map_union]

private theorem support_mapVariables
    {Gate : Type*} (e : Var ↪ Var') (support : Gate → Finset Var)
    (node : NNFNode Var Gate) :
    (node.Support support).map e =
      (node.mapVariables e).Support (fun gate ↦ (support gate).map e) := by
  cases node <;>
    simp [NNFNode.Support, NNFNode.mapVariables, map_foldl_union,
      Finset.map_union]

/-- Relabel every literal along a variable embedding.  The gate graph and all
sharing are unchanged. -/
noncomputable def mapVariables (C : NNFCircuit Var) (e : Var ↪ Var') :
    NNFCircuit Var' where
  Gate := C.Gate
  gateFintype := C.gateFintype
  gateDecidableEq := C.gateDecidableEq
  output := C.output
  node := fun gate ↦ (C.node gate).mapVariables e
  rank := C.rank
  child_rank := by
    intro gate child hchild
    exact C.child_rank gate child
      ((NNFNode.isChild_mapVariables_iff e (C.node gate) child).mp hchild)
  semantics := fun gate v ↦ C.semantics gate (v ∘ e)
  semantics_eq := by
    intro gate v
    rw [C.semantics_eq]
    exact NNFNode.holds_mapVariables_iff e (C.node gate) v
      (fun child ↦ C.semantics child (v ∘ e)) |>.symm
  support := fun gate ↦ (C.support gate).map e
  support_eq := by
    intro gate
    rw [C.support_eq]
    exact support_mapVariables e C.support (C.node gate)

@[simp] theorem mapVariables_size (C : NNFCircuit Var) (e : Var ↪ Var') :
    (C.mapVariables e).size = C.size := rfl

/-- Injective variable relabeling computes the original function on the pulled-back
assignment. -/
theorem mapVariables_computes (C : NNFCircuit Var) (e : Var ↪ Var')
    {f : (Var → Bool) → Prop} (hf : C.Computes f) :
    (C.mapVariables e).Computes (fun v ↦ f (v ∘ e)) := by
  intro v
  exact hf (v ∘ e)

/-- An injective variable map preserves disjoint supports at conjunctions. -/
theorem mapVariables_decomposable (C : NNFCircuit Var) (e : Var ↪ Var')
    (hC : C.IsDecomposable) : (C.mapVariables e).IsDecomposable := by
  intro gate left right hnode
  have horiginal : C.node gate = .conj left right :=
    (NNFNode.mapVariables_eq_conj_iff e (C.node gate) left right).mp hnode
  simpa [mapVariables] using
    (Finset.disjoint_map e).mpr (hC gate left right horiginal)

/-- Variable relabeling preserves mutually exclusive disjuncts. -/
theorem mapVariables_deterministic (C : NNFCircuit Var) (e : Var ↪ Var')
    (hC : C.IsDeterministic) : (C.mapVariables e).IsDeterministic := by
  intro gate children hnode left hleft right hright hlr v
  have horiginal : C.node gate = .disj children :=
    (NNFNode.mapVariables_eq_disj_iff
      e (C.node gate) children).mp hnode
  exact hC gate children horiginal left hleft right hright hlr (v ∘ e)

/-- Injective variable relabeling preserves the deterministic DNNF class. -/
theorem mapVariables_isDeterministicDNNF
    (C : NNFCircuit Var) (e : Var ↪ Var')
    (hC : C.IsDeterministicDNNF) :
    (C.mapVariables e).IsDeterministicDNNF :=
  ⟨C.mapVariables_decomposable e hC.1,
    C.mapVariables_deterministic e hC.2⟩

/-! ## Restricting padding variables -/

private def leftPreimage (S : Finset (Var ⊕ Extra)) : Finset Var :=
  S.toLeft

omit [DecidableEq Var] [DecidableEq Extra] in
@[simp] private theorem leftPreimage_empty :
    leftPreimage (∅ : Finset (Var ⊕ Extra)) = ∅ := by
  ext x
  simp [leftPreimage]

omit [DecidableEq Var] [DecidableEq Extra] in
@[simp] private theorem leftPreimage_singleton_inl (x : Var) :
    leftPreimage ({Sum.inl x} : Finset (Var ⊕ Extra)) = {x} := by
  ext y
  simp [leftPreimage]

omit [DecidableEq Var] [DecidableEq Extra] in
@[simp] private theorem leftPreimage_singleton_inr (y : Extra) :
    leftPreimage ({Sum.inr y} : Finset (Var ⊕ Extra)) = ∅ := by
  ext x
  simp [leftPreimage]

@[simp] private theorem leftPreimage_union
    (S T : Finset (Var ⊕ Extra)) :
    leftPreimage (S ∪ T) = leftPreimage S ∪ leftPreimage T :=
  Finset.toLeft_union

private theorem leftPreimage_foldl_union
    {Gate : Type*} (support : Gate → Finset (Var ⊕ Extra))
    (children : List Gate) (initial : Finset (Var ⊕ Extra)) :
    leftPreimage
        (children.foldl (fun result gate ↦ result ∪ support gate) initial) =
      children.foldl
        (fun result gate ↦ result ∪ leftPreimage (support gate))
        (leftPreimage initial) := by
  induction children generalizing initial with
  | nil => rfl
  | cons gate children ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      exact Finset.toLeft_union

private theorem support_restrictRightVariables
    {Gate : Type*} (fixed : Extra → Bool)
    (support : Gate → Finset (Var ⊕ Extra))
    (node : NNFNode (Var ⊕ Extra) Gate) :
    leftPreimage (node.Support support) =
      (node.restrictRightVariables fixed).Support
        (fun gate ↦ leftPreimage (support gate)) := by
  cases node with
  | top | bot =>
      simp only [NNFNode.Support, NNFNode.restrictRightVariables,
        leftPreimage_empty]
  | conj left right =>
      simp only [NNFNode.Support, NNFNode.restrictRightVariables,
        leftPreimage_union]
  | disj children =>
      simpa [NNFNode.Support, NNFNode.restrictRightVariables,
        leftPreimage_empty] using
        leftPreimage_foldl_union support children ∅
  | pos x | neg x =>
      cases x with
      | inl x => simp only [NNFNode.Support,
          NNFNode.restrictRightVariables, leftPreimage_singleton_inl]
      | inr y =>
          cases h : fixed y <;>
            simp only [NNFNode.Support, NNFNode.restrictRightVariables,
              h, Bool.false_eq_true, ↓reduceIte, leftPreimage_singleton_inr]

/-- Fix all variables in the right summand and retain only the variables in
the left summand.  Literal gates on fixed variables become constants. -/
noncomputable def restrictRightVariables
    (C : NNFCircuit (Var ⊕ Extra)) (fixed : Extra → Bool) :
    NNFCircuit Var where
  Gate := C.Gate
  gateFintype := C.gateFintype
  gateDecidableEq := C.gateDecidableEq
  output := C.output
  node := fun gate ↦ (C.node gate).restrictRightVariables fixed
  rank := C.rank
  child_rank := by
    intro gate child hchild
    exact C.child_rank gate child
      ((NNFNode.isChild_restrictRightVariables_iff
        fixed (C.node gate) child).mp hchild)
  semantics := fun gate v ↦ C.semantics gate (Sum.elim v fixed)
  semantics_eq := by
    intro gate v
    rw [C.semantics_eq]
    exact NNFNode.holds_restrictRightVariables_iff
      fixed (C.node gate) v
      (fun child ↦ C.semantics child (Sum.elim v fixed)) |>.symm
  support := fun gate ↦ leftPreimage (C.support gate)
  support_eq := by
    intro gate
    rw [C.support_eq]
    exact support_restrictRightVariables fixed C.support (C.node gate)

/-- Fixing the extra variables computes the corresponding slice of the original function. -/
theorem restrictRightVariables_computes
    (C : NNFCircuit (Var ⊕ Extra)) (fixed : Extra → Bool)
    {f : ((Var ⊕ Extra) → Bool) → Prop} (hf : C.Computes f) :
    (C.restrictRightVariables fixed).Computes
      (fun v ↦ f (Sum.elim v fixed)) := by
  intro v
  exact hf (Sum.elim v fixed)

/-- Restriction preserves disjoint supports because it only removes variables. -/
theorem restrictRightVariables_decomposable
    (C : NNFCircuit (Var ⊕ Extra)) (fixed : Extra → Bool)
    (hC : C.IsDecomposable) :
    (C.restrictRightVariables fixed).IsDecomposable := by
  intro gate left right hnode
  have horiginal : C.node gate = .conj left right :=
    (NNFNode.restrictRightVariables_eq_conj_iff
      fixed (C.node gate) left right).mp hnode
  rw [Finset.disjoint_left]
  intro x hxleft hxright
  apply (Finset.disjoint_left.mp (hC gate left right horiginal))
  · simpa [restrictRightVariables, leftPreimage] using hxleft
  · simpa [restrictRightVariables, leftPreimage] using hxright

/-- Padding by unused variables is relabeling into the left summand. -/
noncomputable def padRightVariables (C : NNFCircuit Var) :
    NNFCircuit (Var ⊕ Extra) :=
  C.mapVariables Function.Embedding.inl

/-- Adding unused input variables preserves the deterministic DNNF class. -/
theorem padRightVariables_isDeterministicDNNF
    (C : NNFCircuit Var) (hC : C.IsDeterministicDNNF) :
    (C.padRightVariables (Extra := Extra)).IsDeterministicDNNF :=
  C.mapVariables_isDeterministicDNNF Function.Embedding.inl hC

end

end NNFCircuit

namespace NNFCircuit

variable {Var J : Type*} [DecidableEq Var] [Fintype J] [DecidableEq J]

/-- A gate belonging to one circuit in a dependent family. -/
abbrev ComponentGate (C : J → NNFCircuit Var) :=
  Σ j, (C j).Gate

/-- The extra `none` gate is the family disjunction. -/
abbrev FamilyGate (C : J → NNFCircuit Var) :=
  Option (ComponentGate C)

private noncomputable def rootChildren (C : J → NNFCircuit Var) :
    List (FamilyGate C) :=
  (Finset.univ : Finset J).toList.map
    (fun j ↦ some ⟨j, (C j).output⟩)

private noncomputable def familyNode (C : J → NNFCircuit Var) :
    FamilyGate C → NNFNode Var (FamilyGate C)
  | none => .disj (rootChildren C)
  | some ⟨j, gate⟩ => (C j).node gate |>.map (fun child ↦ some ⟨j, child⟩)

private noncomputable def familyMaxRank (C : J → NNFCircuit Var) : ℕ :=
  Finset.univ.sup (fun gate : ComponentGate C ↦
    (C gate.1).rank gate.2)

private noncomputable def familyRank (C : J → NNFCircuit Var) :
    FamilyGate C → ℕ
  | none => familyMaxRank C + 1
  | some ⟨j, gate⟩ => (C j).rank gate

private def familySemantics (C : J → NNFCircuit Var) :
    FamilyGate C → (Var → Bool) → Prop
  | none, v => ∃ j, (C j).semantics (C j).output v
  | some ⟨j, gate⟩, v => (C j).semantics gate v

private noncomputable def familySupport (C : J → NNFCircuit Var) :
    FamilyGate C → Finset Var
  | none => (rootChildren C).foldl
      (fun result child ↦ result ∪
        match child with
        | none => ∅
        | some ⟨j, gate⟩ => (C j).support gate) ∅
  | some ⟨j, gate⟩ => (C j).support gate

omit [DecidableEq Var] in
/-- A child after relabeling comes from an original child, even when the label map
identifies gates. -/
private theorem isChild_map_exists
    {Gate Gate' : Type*} (node : NNFNode Var Gate) (f : Gate → Gate')
    (child : Gate') (hchild : (node.map f).IsChild child) :
    ∃ source, node.IsChild source ∧ f source = child := by
  cases node <;> simp [NNFNode.map, NNFNode.IsChild] at hchild ⊢
  · rcases hchild with rfl | rfl <;> simp
  · obtain ⟨source, hmem, rfl⟩ := hchild
    exact ⟨source, hmem, rfl⟩

omit [DecidableEq Var] in
/-- Relabeling node references transports truth by composition with the label map. -/
private theorem holds_map
    {Gate Gate' : Type*} (node : NNFNode Var Gate) (f : Gate → Gate')
    (v : Var → Bool) (child : Gate' → Prop) :
    (node.map f).Holds v child ↔
      node.Holds v (fun gate ↦ child (f gate)) := by
  cases node <;> simp [NNFNode.map, NNFNode.Holds]

/-- Relabeling node references transports the union of child supports. -/
private theorem support_map
    {Gate Gate' : Type*} (node : NNFNode Var Gate) (f : Gate → Gate')
    (child : Gate' → Finset Var) :
    (node.map f).Support child =
      node.Support (fun gate ↦ child (f gate)) := by
  cases node <;> simp [NNFNode.map, NNFNode.Support, List.foldl_map]

omit [DecidableEq J] in
private theorem family_child_rank (C : J → NNFCircuit Var)
    (gate child : FamilyGate C)
    (hchild : (familyNode C gate).IsChild child) :
    familyRank C child < familyRank C gate := by
  cases gate with
  | none =>
      simp only [familyNode, NNFNode.IsChild] at hchild
      obtain ⟨j, hj, hchild⟩ := List.mem_map.mp hchild
      subst child
      simp only [familyRank]
      have hle : (C j).rank (C j).output ≤ familyMaxRank C := by
        unfold familyMaxRank
        exact Finset.le_sup (s := Finset.univ)
          (f := fun gate : ComponentGate C ↦ (C gate.1).rank gate.2)
          (by simp : (⟨j, (C j).output⟩ : ComponentGate C) ∈ Finset.univ)
      omega
  | some component =>
      rcases component with ⟨j, gate⟩
      simp only [familyNode] at hchild
      obtain ⟨source, hsource, rfl⟩ :=
        isChild_map_exists ((C j).node gate)
          (fun child ↦ some ⟨j, child⟩) child hchild
      exact (C j).child_rank gate source hsource

omit [DecidableEq J] in
private theorem family_semantics_eq (C : J → NNFCircuit Var)
    (gate : FamilyGate C) (v : Var → Bool) :
    familySemantics C gate v ↔
      (familyNode C gate).Holds v (fun child ↦ familySemantics C child v) := by
  cases gate with
  | none =>
      simp only [familyNode, NNFNode.Holds, familySemantics]
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨some ⟨j, (C j).output⟩, ?_, hj⟩
        apply List.mem_map.mpr
        exact ⟨j, by simp, rfl⟩
      · rintro ⟨child, hchild, hsem⟩
        obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hchild
        exact ⟨j, hsem⟩
  | some component =>
      rcases component with ⟨j, gate⟩
      simp only [familySemantics, familyNode]
      rw [holds_map]
      simpa [familySemantics] using (C j).semantics_eq gate v

omit [DecidableEq J] in
private theorem family_support_eq (C : J → NNFCircuit Var)
    (gate : FamilyGate C) :
    familySupport C gate =
      (familyNode C gate).Support (familySupport C) := by
  cases gate with
  | none =>
      simp [familyNode, NNFNode.Support, familySupport, rootChildren,
        List.foldl_map]
  | some component =>
      rcases component with ⟨j, gate⟩
      simp only [familySupport, familyNode]
      rw [support_map]
      simpa [familySupport] using (C j).support_eq gate

/-- Add one OR gate above the disjoint union of a finite family of circuits. -/
noncomputable def disjointOr (C : J → NNFCircuit Var) : NNFCircuit Var where
  Gate := FamilyGate C
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := none
  node := familyNode C
  rank := familyRank C
  child_rank := family_child_rank C
  semantics := familySemantics C
  semantics_eq := family_semantics_eq C
  support := familySupport C
  support_eq := family_support_eq C

/-- The family circuit computes the disjunction of its component functions. -/
theorem disjointOr_computes (C : J → NNFCircuit Var)
    (f : J → (Var → Bool) → Prop)
    (hcomputes : ∀ j, (C j).Computes (f j)) :
    (disjointOr C).Computes (fun v ↦ ∃ j, f j v) := by
  intro v
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (hcomputes j v).mp hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (hcomputes j v).mpr hj⟩

/-- The family OR introduces no conjunction, so component decomposability suffices. -/
theorem disjointOr_decomposable (C : J → NNFCircuit Var)
    (hdecomp : ∀ j, (C j).IsDecomposable) :
    (disjointOr C).IsDecomposable := by
  intro gate left right hnode
  cases gate with
  | none => simp [disjointOr, familyNode] at hnode
  | some component =>
      rcases component with ⟨j, gate⟩
      cases hlocal : (C j).node gate <;>
        simp [disjointOr, familyNode, NNFNode.map, hlocal] at hnode
      injection hnode with hleft hright
      subst left
      subst right
      simpa [disjointOr, familySupport] using
        hdecomp j gate _ _ hlocal

/-- Disjoint component functions make the new top OR deterministic; internal ORs inherit
component determinism. -/
theorem disjointOr_deterministic (C : J → NNFCircuit Var)
    (hdet : ∀ j, (C j).IsDeterministic)
    (hdisjoint : ∀ j k, j ≠ k → ∀ v,
      ¬((C j).semantics (C j).output v ∧
        (C k).semantics (C k).output v)) :
    (disjointOr C).IsDeterministic := by
  intro gate children hnode left hleft right hright hlr v
  cases gate with
  | none =>
      simp only [disjointOr, familyNode] at hnode
      injection hnode with hchildren
      subst children
      obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hleft
      obtain ⟨k, _hk, rfl⟩ := List.mem_map.mp hright
      have hjk : j ≠ k := by
        intro heq
        subst k
        exact hlr rfl
      simpa [disjointOr, familySemantics] using hdisjoint j k hjk v
  | some component =>
      rcases component with ⟨j, gate⟩
      cases hlocal : (C j).node gate <;>
        simp [disjointOr, familyNode, NNFNode.map, hlocal] at hnode
      injection hnode with hchildren
      subst children
      obtain ⟨leftSource, hleftSource, rfl⟩ := List.mem_map.mp hleft
      obtain ⟨rightSource, hrightSource, rfl⟩ := List.mem_map.mp hright
      have hne : leftSource ≠ rightSource := by
        intro heq
        subst rightSource
        exact hlr rfl
      simpa [disjointOr, familySemantics] using
        hdet j gate _ hlocal leftSource hleftSource
          rightSource hrightSource hne v

/-- A disjoint union of deterministic DNNFs is a deterministic DNNF. -/
theorem disjointOr_isDeterministicDNNF (C : J → NNFCircuit Var)
    (hddnnf : ∀ j, (C j).IsDeterministicDNNF)
    (hdisjoint : ∀ j k, j ≠ k → ∀ v,
      ¬((C j).semantics (C j).output v ∧
        (C k).semantics (C k).output v)) :
    (disjointOr C).IsDeterministicDNNF := by
  constructor
  · exact disjointOr_decomposable C (fun j ↦ (hddnnf j).1)
  · exact disjointOr_deterministic C (fun j ↦ (hddnnf j).2) hdisjoint

/-- The new OR contributes one edge to each component output. -/
theorem disjointOr_edgeCount (C : J → NNFCircuit Var) :
    (disjointOr C).edgeCount = Fintype.card J + ∑ j, (C j).edgeCount := by
  unfold NNFCircuit.edgeCount
  change ∑ gate : FamilyGate C, (familyNode C gate).fanIn = _
  rw [Fintype.sum_option, Fintype.sum_sigma]
  congr 1
  · simp [familyNode, rootChildren, NNFNode.fanIn]
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro gate _
    simp [familyNode, NNFNode.fanIn_map]

end NNFCircuit

end DDNNFNegation
