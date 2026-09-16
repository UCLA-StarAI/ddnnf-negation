import DDNNFNegation.Circuit

/-!
# Building a circuit from an acyclic node table

The proof-side circuit model stores semantics and support together with local
equations that pin them down.  A compiler should not have to invent those
fields.  This module derives them by recursion from a finite node table and a
rank that strictly decreases along every edge.
-/

namespace DDNNFNegation

/-- The data a compiler must provide for a finite acyclic NNF circuit. -/
structure AcyclicNNFDescription (Var Gate : Type*) where
  output : Gate
  node : Gate → NNFNode Var Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child,
    (node gate).IsChild child → rank child < rank gate

namespace AcyclicNNFDescription

variable {Var Gate : Type*} [DecidableEq Var] [Fintype Gate]
  [DecidableEq Gate]

noncomputable local instance (node : NNFNode Var Gate) (child : Gate) :
    Decidable (node.IsChild child) := Classical.propDecidable _

/-- Semantics obtained solely from the node table. -/
noncomputable def semantics (D : AcyclicNNFDescription Var Gate)
    (gate : Gate) (v : Var → Bool) : Prop :=
  (D.node gate).Holds v fun child ↦
    if _h : (D.node gate).IsChild child then D.semantics child v else False
termination_by D.rank gate
decreasing_by exact D.child_rank gate child _h

omit [DecidableEq Var] [Fintype Gate] [DecidableEq Gate] in
theorem semantics_eq (D : AcyclicNNFDescription Var Gate)
    (gate : Gate) (v : Var → Bool) :
    D.semantics gate v ↔
      (D.node gate).Holds v (fun child ↦ D.semantics child v) := by
  rw [semantics]
  apply NNFNode.holds_congr
  intro child hchild
  simp [hchild]

/-- Syntactic support obtained solely from the node table. -/
noncomputable def support (D : AcyclicNNFDescription Var Gate)
    (gate : Gate) : Finset Var :=
  (D.node gate).Support fun child ↦
    if _h : (D.node gate).IsChild child then D.support child else ∅
termination_by D.rank gate
decreasing_by exact D.child_rank gate child _h

omit [Fintype Gate] [DecidableEq Gate] in
theorem support_eq (D : AcyclicNNFDescription Var Gate) (gate : Gate) :
    D.support gate = (D.node gate).Support D.support := by
  rw [support]
  apply NNFNode.support_congr
  intro child hchild
  simp [hchild]

/-- Turn an acyclic node table into the project's proof-side circuit type. -/
noncomputable def toCircuit (D : AcyclicNNFDescription Var Gate) :
    NNFCircuit Var where
  Gate := Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := D.output
  node := D.node
  rank := D.rank
  child_rank := D.child_rank
  semantics := D.semantics
  semantics_eq := D.semantics_eq
  support := D.support
  support_eq := D.support_eq

@[simp] theorem toCircuit_nodeCount (D : AcyclicNNFDescription Var Gate) :
    D.toCircuit.nodeCount = Fintype.card Gate := rfl

end AcyclicNNFDescription

end DDNNFNegation
