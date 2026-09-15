import DDNNFNegation.Separation
import DDNNFNegation.NegationNotClosed
import TutorialBox

/-!
# Internal negation: d-D circuits and partitioned-operation graphs

`DDCircuit` extends the proof-side NNF model with negation gates;
decomposability and determinism constrain its AND and OR gates.
`POG` instead uses signed node references at products, sums, and the
output. These are the formulations of Wachter and Haenni's cd-PDAGs and
Bryant, Nawrocki, Avigad, and Heule's partitioned-operation graphs.

The hard d-DNNF becomes a small circuit for its complement by adding
one negation gate or negating the output reference. The DNNF lower bound
for that same function therefore separates these languages from DNNF.
The list-valued sums in this model allow arbitrary fan-in.
-/

namespace DDNNFNegation

open Finset

/-! ## Deterministic decomposable circuits with negation gates -/

/-- One gate of a circuit in which negation may occur anywhere. -/
inductive DDNode (Var Gate : Type*) where
  | top
  | bot
  | pos (x : Var)
  | neg (x : Var)
  | conj (left right : Gate)
  | disj (children : List Gate)
  | not (child : Gate)

namespace DDNode

variable {Var Gate : Type*}

/-- Local semantics, given the meanings of child gates. -/
def Holds (v : Var → Bool) (child : Gate → Prop) : DDNode Var Gate → Prop
  | top => True
  | bot => False
  | pos x => v x = true
  | neg x => v x = false
  | conj left right => child left ∧ child right
  | disj children => ∃ gate ∈ children, child gate
  | not gate => ¬ child gate

/-- Local support, given the supports of child gates. -/
def Support [DecidableEq Var] (child : Gate → Finset Var) :
    DDNode Var Gate → Finset Var
  | top => ∅
  | bot => ∅
  | pos x => {x}
  | neg x => {x}
  | conj left right => child left ∪ child right
  | disj children =>
      children.foldl (fun result gate ↦ result ∪ child gate) ∅
  | not gate => child gate

/-- The child relation of a local gate description. -/
def IsChild (child : Gate) : DDNode Var Gate → Prop
  | conj left right => child = left ∨ child = right
  | disj children => child ∈ children
  | not gate => child = gate
  | _ => False

end DDNode

/-- A finite shared circuit with negation gates, decomposability and
determinism being conditions on its conjunctions and disjunctions
(`DDCircuit.IsDD`). -/
structure DDCircuit (Var : Type*) [DecidableEq Var] where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  node : Gate → DDNode Var Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child,
    (node gate).IsChild child → rank child < rank gate
  semantics : Gate → (Var → Bool) → Prop
  semantics_eq : ∀ gate v,
    semantics gate v ↔ (node gate).Holds v (fun child ↦ semantics child v)
  support : Gate → Finset Var
  support_eq : ∀ gate,
    support gate = (node gate).Support support

namespace DDCircuit

variable {Var : Type*} [DecidableEq Var]

instance (C : DDCircuit Var) : Fintype C.Gate := C.gateFintype

instance (C : DDCircuit Var) : DecidableEq C.Gate := C.gateDecidableEq

/-- Number of gates, negation gates included. -/
def size (C : DDCircuit Var) : ℕ :=
  Fintype.card C.Gate

/-- Function computed at the output gate. -/
def Computes (C : DDCircuit Var) (f : (Var → Bool) → Prop) : Prop :=
  ∀ v, C.semantics C.output v ↔ f v

/-- Every conjunction combines disjoint variable sets. -/
def IsDecomposable (C : DDCircuit Var) : Prop :=
  ∀ gate left right, C.node gate = .conj left right →
    Disjoint (C.support left) (C.support right)

/-- Every disjunction has mutually exclusive children. -/
def IsDeterministic (C : DDCircuit Var) : Prop :=
  ∀ gate children, C.node gate = .disj children →
    ∀ left, left ∈ children → ∀ right, right ∈ children →
      left ≠ right → ∀ v,
        ¬(C.semantics left v ∧ C.semantics right v)

/-- A d-D circuit: decomposable conjunctions and deterministic disjunctions,
with negation allowed at any gate. -/
def IsDD (C : DDCircuit Var) : Prop :=
  C.IsDecomposable ∧ C.IsDeterministic

end DDCircuit

namespace NNFNode

variable {Var Gate Gate' : Type*}

/-- An NNF gate read as a gate of a circuit with negation, its child
references renamed along `f`. -/
def toDD (f : Gate → Gate') : NNFNode Var Gate → DDNode Var Gate'
  | top => .top
  | bot => .bot
  | pos x => .pos x
  | neg x => .neg x
  | conj left right => .conj (f left) (f right)
  | disj children => .disj (children.map f)

theorem holds_toDD (f : Gate → Gate') (node : NNFNode Var Gate)
    (v : Var → Bool) (child : Gate' → Prop) :
    (node.toDD f).Holds v child ↔ node.Holds v (fun gate ↦ child (f gate)) := by
  cases node <;> simp [toDD, DDNode.Holds, NNFNode.Holds]

theorem support_toDD [DecidableEq Var] (f : Gate → Gate')
    (node : NNFNode Var Gate) (child : Gate' → Finset Var) :
    (node.toDD f).Support child = node.Support (fun gate ↦ child (f gate)) := by
  cases node <;> simp [toDD, DDNode.Support, NNFNode.Support, List.foldl_map]

theorem isChild_toDD_exists (f : Gate → Gate') (node : NNFNode Var Gate)
    (child : Gate') (hchild : (node.toDD f).IsChild child) :
    ∃ source, node.IsChild source ∧ f source = child := by
  cases node <;> simp [toDD, DDNode.IsChild, NNFNode.IsChild] at hchild ⊢
  · rcases hchild with rfl | rfl <;> simp
  · obtain ⟨source, hmem, rfl⟩ := hchild
    exact ⟨source, hmem, rfl⟩

end NNFNode

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

private def negNode (C : NNFCircuit Var) :
    Option C.Gate → DDNode Var (Option C.Gate)
  | none => .not (some C.output)
  | some gate => (C.node gate).toDD some

private def negRank (C : NNFCircuit Var) : Option C.Gate → ℕ
  | none => C.rank C.output + 1
  | some gate => C.rank gate

private def negSemantics (C : NNFCircuit Var) :
    Option C.Gate → (Var → Bool) → Prop
  | none, v => ¬ C.semantics C.output v
  | some gate, v => C.semantics gate v

private def negSupport (C : NNFCircuit Var) : Option C.Gate → Finset Var
  | none => C.support C.output
  | some gate => C.support gate

/-- Add one output negation gate to an NNF circuit. -/
noncomputable def negateOutput (C : NNFCircuit Var) : DDCircuit Var where
  Gate := Option C.Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := none
  node := negNode C
  rank := negRank C
  child_rank := by
    intro gate child hchild
    cases gate with
    | none =>
        simp [negNode, DDNode.IsChild] at hchild
        subst hchild
        simp [negRank]
    | some gate =>
        obtain ⟨source, hsource, rfl⟩ :=
          NNFNode.isChild_toDD_exists some (C.node gate) child hchild
        simpa [negRank] using C.child_rank gate source hsource
  semantics := negSemantics C
  semantics_eq := by
    intro gate v
    cases gate with
    | none => simp [negNode, negSemantics, DDNode.Holds]
    | some gate =>
        simp only [negNode]
        rw [NNFNode.holds_toDD]
        exact C.semantics_eq gate v
  support := negSupport C
  support_eq := by
    intro gate
    cases gate with
    | none => simp [negNode, negSupport, DDNode.Support]
    | some gate =>
        simp only [negNode]
        rw [NNFNode.support_toDD]
        exact C.support_eq gate

theorem negateOutput_size (C : NNFCircuit Var) :
    C.negateOutput.size = C.size + 1 := by
  show Fintype.card (Option C.Gate) = Fintype.card C.Gate + 1
  exact Fintype.card_option

theorem negateOutput_computes (C : NNFCircuit Var) {f : (Var → Bool) → Prop}
    (h : C.Computes f) : C.negateOutput.Computes (fun v ↦ ¬ f v) := by
  intro v
  exact not_congr (h v)

theorem negateOutput_isDecomposable (C : NNFCircuit Var)
    (h : C.IsDecomposable) : C.negateOutput.IsDecomposable := by
  intro gate left right hnode
  cases gate with
  | none => simp [negateOutput, negNode] at hnode
  | some gate =>
      cases hlocal : C.node gate <;>
        simp [negateOutput, negNode, NNFNode.toDD, hlocal] at hnode
      obtain ⟨rfl, rfl⟩ := hnode
      exact h gate _ _ hlocal

theorem negateOutput_isDeterministic (C : NNFCircuit Var)
    (h : C.IsDeterministic) : C.negateOutput.IsDeterministic := by
  intro gate children hnode left hleft right hright hne v
  cases gate with
  | none => simp [negateOutput, negNode] at hnode
  | some gate =>
      cases hlocal : C.node gate <;>
        simp [negateOutput, negNode, NNFNode.toDD, hlocal] at hnode
      injection hnode with hchildren
      subst hchildren
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hleft
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hright
      have hlr : l ≠ r := fun heq ↦ hne (by rw [heq])
      exact h gate _ hlocal l hl r hr hlr v

/-- A deterministic DNNF with one `not` gate above it is a d-D circuit. -/
theorem negateOutput_isDD (C : NNFCircuit Var) (h : C.IsDeterministicDNNF) :
    C.negateOutput.IsDD :=
  ⟨C.negateOutput_isDecomposable h.1, C.negateOutput_isDeterministic h.2⟩

end NNFCircuit

/-! ## Partitioned-operation graphs -/

/-- One node of a partitioned-operation graph.  An argument `(gate, sign)`
of a product or sum is the literal of that node: the node itself when the
sign is `true`, its complement when the sign is `false`. -/
inductive POGNode (Var Gate : Type*) where
  | top
  | var (x : Var)
  | prod (args : List (Gate × Bool))
  | sum (args : List (Gate × Bool))

namespace POGNode

variable {Var Gate : Type*}

/-- The truth of a signed reference, given the truth of the nodes. -/
def Lit (child : Gate → Prop) (arg : Gate × Bool) : Prop :=
  child arg.1 ↔ arg.2 = true

/-- Local semantics, given the meanings of the referenced nodes. -/
def Holds (v : Var → Bool) (child : Gate → Prop) : POGNode Var Gate → Prop
  | top => True
  | var x => v x = true
  | prod args => ∀ arg ∈ args, Lit child arg
  | sum args => ∃ arg ∈ args, Lit child arg

/-- Local support, given the supports of the referenced nodes.  A sign does
not change which variables a node mentions. -/
def Support [DecidableEq Var] (child : Gate → Finset Var) :
    POGNode Var Gate → Finset Var
  | top => ∅
  | var x => {x}
  | prod args => args.foldl (fun result arg ↦ result ∪ child arg.1) ∅
  | sum args => args.foldl (fun result arg ↦ result ∪ child arg.1) ∅

/-- The node relation: a node referenced, with either sign, by an argument. -/
def IsChild (child : Gate) : POGNode Var Gate → Prop
  | prod args => ∃ arg ∈ args, arg.1 = child
  | sum args => ∃ arg ∈ args, arg.1 = child
  | _ => False

end POGNode

/-- A finite partitioned-operation graph.  The output is a signed reference
to a node, so the complement of a graph is the same graph with the output
sign flipped. -/
structure POG (Var : Type*) [DecidableEq Var] where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  outputSign : Bool
  node : Gate → POGNode Var Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child,
    (node gate).IsChild child → rank child < rank gate
  semantics : Gate → (Var → Bool) → Prop
  semantics_eq : ∀ gate v,
    semantics gate v ↔ (node gate).Holds v (fun child ↦ semantics child v)
  support : Gate → Finset Var
  support_eq : ∀ gate,
    support gate = (node gate).Support support

namespace POG

variable {Var : Type*} [DecidableEq Var]

instance (P : POG Var) : Fintype P.Gate := P.gateFintype

instance (P : POG Var) : DecidableEq P.Gate := P.gateDecidableEq

/-- Number of nodes. -/
def size (P : POG Var) : ℕ :=
  Fintype.card P.Gate

/-- The function of the signed output reference. -/
def Computes (P : POG Var) (f : (Var → Bool) → Prop) : Prop :=
  ∀ v, POGNode.Lit (fun gate ↦ P.semantics gate v) (P.output, P.outputSign) ↔ f v

/-- Distinct arguments of every product mention disjoint variable sets. -/
def IsDecomposable (P : POG Var) : Prop :=
  ∀ gate args, P.node gate = .prod args →
    ∀ a ∈ args, ∀ b ∈ args, a ≠ b → Disjoint (P.support a.1) (P.support b.1)

/-- Distinct arguments of every sum are never true together. -/
def IsDeterministic (P : POG Var) : Prop :=
  ∀ gate args, P.node gate = .sum args →
    ∀ a ∈ args, ∀ b ∈ args, a ≠ b → ∀ v,
      ¬(POGNode.Lit (fun child ↦ P.semantics child v) a ∧
        POGNode.Lit (fun child ↦ P.semantics child v) b)

/-- The partition conditions of a POG. -/
def IsPartitioned (P : POG Var) : Prop :=
  P.IsDecomposable ∧ P.IsDeterministic

/-- The complement: the same graph with the output sign flipped. -/
def negate (P : POG Var) : POG Var :=
  { P with outputSign := !P.outputSign }

theorem negate_size (P : POG Var) : P.negate.size = P.size := rfl

theorem negate_isPartitioned (P : POG Var) (h : P.IsPartitioned) :
    P.negate.IsPartitioned := h

theorem negate_computes (P : POG Var) {f : (Var → Bool) → Prop}
    (h : P.Computes f) : P.negate.Computes (fun v ↦ ¬ f v) := by
  intro v
  have hv := h v
  simp only [POGNode.Lit] at hv ⊢
  change (P.semantics P.output v ↔ (!P.outputSign) = true) ↔ ¬ f v
  rw [← hv]
  cases P.outputSign <;> simp

end POG

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

/-- The sign with which an NNF gate is referenced in the graph: negative
for a `bot`, a negative literal, or an empty disjunction, all of which
become the constant `⊤` or a variable node read negatively. -/
def litSign (C : NNFCircuit Var) (gate : C.Gate) : Bool :=
  match C.node gate with
  | .bot => false
  | .neg _ => false
  | .disj [] => false
  | _ => true

private def pogNode (C : NNFCircuit Var) (gate : C.Gate) : POGNode Var C.Gate :=
  match C.node gate with
  | .top => .top
  | .bot => .top
  | .pos x => .var x
  | .neg x => .var x
  | .conj left right => .prod [(left, C.litSign left), (right, C.litSign right)]
  | .disj [] => .top
  | .disj children => .sum (children.map (fun child ↦ (child, C.litSign child)))

/-- The node's truth, arranged so that the signed reference `(gate, litSign gate)`
reads the NNF gate's truth. -/
private def pogSemantics (C : NNFCircuit Var) (gate : C.Gate) (v : Var → Bool) :
    Prop :=
  C.semantics gate v ↔ C.litSign gate = true

private theorem pogLit (C : NNFCircuit Var) (gate : C.Gate) (v : Var → Bool) :
    POGNode.Lit (fun child ↦ pogSemantics C child v) (gate, C.litSign gate) ↔
      C.semantics gate v := by
  simp only [POGNode.Lit, pogSemantics]
  cases C.litSign gate <;> simp

private theorem holds_prod_pair (C : NNFCircuit Var) (left right : C.Gate)
    (v : Var → Bool) :
    (∀ arg ∈ [(left, C.litSign left), (right, C.litSign right)],
        POGNode.Lit (fun child ↦ pogSemantics C child v) arg) ↔
      (C.semantics left v ∧ C.semantics right v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, pogLit]

private theorem holds_sum_map (C : NNFCircuit Var) (children : List C.Gate)
    (v : Var → Bool) :
    (∃ arg ∈ children.map (fun child ↦ (child, C.litSign child)),
        POGNode.Lit (fun child ↦ pogSemantics C child v) arg) ↔
      ∃ gate ∈ children, C.semantics gate v := by
  constructor
  · rintro ⟨arg, harg, hs⟩
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp harg
    exact ⟨source, hsource, (pogLit C source v).mp hs⟩
  · rintro ⟨source, hsource, hs⟩
    exact ⟨(source, C.litSign source), List.mem_map.mpr ⟨source, hsource, rfl⟩,
      (pogLit C source v).mpr hs⟩

private theorem pog_child_rank (C : NNFCircuit Var) (gate child : C.Gate)
    (hchild : (pogNode C gate).IsChild child) : C.rank child < C.rank gate := by
  apply C.child_rank gate child
  cases hnode : C.node gate with
  | top => simp [pogNode, hnode, POGNode.IsChild] at hchild
  | bot => simp [pogNode, hnode, POGNode.IsChild] at hchild
  | pos x => simp [pogNode, hnode, POGNode.IsChild] at hchild
  | neg x => simp [pogNode, hnode, POGNode.IsChild] at hchild
  | conj left right =>
      simp only [pogNode, hnode, POGNode.IsChild] at hchild
      obtain ⟨arg, harg, rfl⟩ := hchild
      simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
      rcases harg with rfl | rfl <;> simp [NNFNode.IsChild]
  | disj children =>
      cases children with
      | nil => simp [pogNode, hnode, POGNode.IsChild] at hchild
      | cons head tail =>
          simp only [pogNode, hnode, POGNode.IsChild, List.mem_map] at hchild
          obtain ⟨arg, ⟨source, hsource, rfl⟩, rfl⟩ := hchild
          exact hsource

private theorem pog_semantics_eq (C : NNFCircuit Var) (gate : C.Gate)
    (v : Var → Bool) :
    pogSemantics C gate v ↔
      (pogNode C gate).Holds v (fun child ↦ pogSemantics C child v) := by
  have hsem := C.semantics_eq gate v
  cases hnode : C.node gate with
  | top =>
      rw [hnode] at hsem
      simp [pogNode, pogSemantics, litSign, hnode, POGNode.Holds, hsem,
        NNFNode.Holds]
  | bot =>
      rw [hnode] at hsem
      simp [pogNode, pogSemantics, litSign, hnode, POGNode.Holds, hsem,
        NNFNode.Holds]
  | pos x =>
      rw [hnode] at hsem
      simp [pogNode, pogSemantics, litSign, hnode, POGNode.Holds, hsem,
        NNFNode.Holds]
  | neg x =>
      rw [hnode] at hsem
      simp [pogNode, pogSemantics, litSign, hnode, POGNode.Holds, hsem,
        NNFNode.Holds]
  | conj left right =>
      rw [hnode] at hsem
      simp only [pogNode, hnode, POGNode.Holds, holds_prod_pair]
      simp [pogSemantics, litSign, hnode, hsem, NNFNode.Holds]
  | disj children =>
      rw [hnode] at hsem
      cases children with
      | nil =>
          simp [pogNode, pogSemantics, litSign, hnode, POGNode.Holds, hsem,
            NNFNode.Holds]
      | cons head tail =>
          simp only [pogNode, hnode, POGNode.Holds, holds_sum_map]
          simp [pogSemantics, litSign, hnode, hsem, NNFNode.Holds]

private theorem pog_support_eq (C : NNFCircuit Var) (gate : C.Gate) :
    C.support gate = (pogNode C gate).Support C.support := by
  have hsupp := C.support_eq gate
  cases hnode : C.node gate with
  | top =>
      rw [hnode] at hsupp
      simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support]
  | bot =>
      rw [hnode] at hsupp
      simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support]
  | pos x =>
      rw [hnode] at hsupp
      simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support]
  | neg x =>
      rw [hnode] at hsupp
      simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support]
  | conj left right =>
      rw [hnode] at hsupp
      simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support]
  | disj children =>
      rw [hnode] at hsupp
      cases children with
      | nil => simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support]
      | cons head tail =>
          simp [pogNode, hnode, POGNode.Support, hsupp, NNFNode.Support,
            List.foldl_map]

/-- An NNF circuit read as a partitioned-operation graph: the same nodes,
with `bot`, negative literals and empty disjunctions turned into negatively
signed references to `⊤` or to a variable node. -/
noncomputable def toPOG (C : NNFCircuit Var) : POG Var where
  Gate := C.Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := C.output
  outputSign := C.litSign C.output
  node := pogNode C
  rank := C.rank
  child_rank := pog_child_rank C
  semantics := pogSemantics C
  semantics_eq := pog_semantics_eq C
  support := C.support
  support_eq := pog_support_eq C

theorem toPOG_size (C : NNFCircuit Var) : C.toPOG.size = C.size := rfl

theorem toPOG_computes (C : NNFCircuit Var) {f : (Var → Bool) → Prop}
    (h : C.Computes f) : C.toPOG.Computes f := by
  intro v
  exact (pogLit C C.output v).trans (h v)

theorem toPOG_isDecomposable (C : NNFCircuit Var) (h : C.IsDecomposable) :
    C.toPOG.IsDecomposable := by
  intro gate args hnode a ha b hb hab
  change pogNode C gate = _ at hnode
  cases hlocal : C.node gate with
  | top => simp [pogNode, hlocal] at hnode
  | bot => simp [pogNode, hlocal] at hnode
  | pos x => simp [pogNode, hlocal] at hnode
  | neg x => simp [pogNode, hlocal] at hnode
  | conj left right =>
      simp only [pogNode, hlocal] at hnode
      injection hnode with hargs
      subst hargs
      have hdisj := h gate left right hlocal
      obtain rfl | rfl := List.mem_pair.mp ha <;>
        obtain rfl | rfl := List.mem_pair.mp hb
      · exact absurd rfl hab
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hab
  | disj children =>
      cases children <;> simp [pogNode, hlocal] at hnode

theorem toPOG_isDeterministic (C : NNFCircuit Var) (h : C.IsDeterministic) :
    C.toPOG.IsDeterministic := by
  intro gate args hnode a ha b hb hab v
  change pogNode C gate = _ at hnode
  cases hlocal : C.node gate with
  | top => simp [pogNode, hlocal] at hnode
  | bot => simp [pogNode, hlocal] at hnode
  | pos x => simp [pogNode, hlocal] at hnode
  | neg x => simp [pogNode, hlocal] at hnode
  | conj left right => simp [pogNode, hlocal] at hnode
  | disj children =>
      cases children with
      | nil => simp [pogNode, hlocal] at hnode
      | cons head tail =>
          simp only [pogNode, hlocal] at hnode
          injection hnode with hargs
          subst hargs
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
          have hlr : l ≠ r := fun heq ↦ hab (by rw [heq])
          have hex := h gate _ hlocal l hl r hr hlr v
          change ¬(POGNode.Lit (fun child ↦ pogSemantics C child v) (l, C.litSign l) ∧
            POGNode.Lit (fun child ↦ pogSemantics C child v) (r, C.litSign r))
          rw [pogLit, pogLit]
          exact hex

/-- A deterministic DNNF is a partitioned-operation graph. -/
theorem toPOG_isPartitioned (C : NNFCircuit Var) (h : C.IsDeterministicDNNF) :
    C.toPOG.IsPartitioned :=
  ⟨C.toPOG_isDecomposable h.1, C.toPOG_isDeterministic h.2⟩

end NNFCircuit

/-! ## The corollary -/

section

/-- The lower bound the corollary quotes: every DNNF for `¬L_n` has at least
`spectralNodeLower n` nodes, which is `2^{Ω(n²)}`. -/
theorem exists_dD_circuit_and_POG_for_complement
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      (∃ C : DDCircuit.{0, 0} (Fin (encodedInputCount n)),
        C.IsDD ∧ C.Computes (fun x ↦ ¬hardFunction ranks hn a x) ∧
        C.size ≤ positiveCircuitBound n + 2) ∧
      (∃ P : POG.{0, 0} (Fin (encodedInputCount n)),
        P.IsPartitioned ∧ P.Computes (fun x ↦ ¬hardFunction ranks hn a x) ∧
        P.size ≤ positiveCircuitBound n + 1) ∧
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
        spectralNodeLower n ≤ (D.size : ℝ) := by
  obtain ⟨ranks, a, C, hdet, hcomputes, hsize, hlower⟩ :=
    negation_separation n hn
  refine ⟨ranks, a, ⟨C.negateOutput, C.negateOutput_isDD hdet,
    C.negateOutput_computes hcomputes, ?_⟩,
    ⟨C.toPOG.negate, C.toPOG.negate_isPartitioned (C.toPOG_isPartitioned hdet),
    C.toPOG.negate_computes (C.toPOG_computes hcomputes), ?_⟩, hlower⟩
  · rw [C.negateOutput_size]
    omega
  · rw [C.toPOG.negate_size, C.toPOG_size]
    exact hsize

/-- No polynomial translation from d-D circuits, or from POGs, into DNNF:
for every degree `d` and factor `M` there is a d-D circuit `C`, and a POG
`P`, such that every DNNF for the same function has more than
`M * size ^ d` gates.  Since d-DNNFs are DNNFs, the same holds against
d-DNNF. -/
theorem no_polynomial_translation_of_internal_negation (d M : ℕ) :
    ∃ (m : ℕ) (f : (Fin m → Bool) → Prop),
      (∃ C : DDCircuit.{0, 0} (Fin m), C.IsDD ∧ C.Computes f ∧
        ∀ D : NNFCircuit.{0, 0} (Fin m), D.IsDNNF → D.Computes f →
          (M : ℝ) * (C.size : ℝ) ^ d < (D.size : ℝ)) ∧
      (∃ P : POG.{0, 0} (Fin m), P.IsPartitioned ∧ P.Computes f ∧
        ∀ D : NNFCircuit.{0, 0} (Fin m), D.IsDNNF → D.Computes f →
          (M : ℝ) * (P.size : ℝ) ^ d < (D.size : ℝ)) := by
  obtain ⟨m, g, C, hdet, hcomputes, hCsize, hMm, hlow⟩ :=
    exists_separation_at_padded_scale.{0} (d + 1) (M * 2 ^ d)
  have hC : (C.size : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hCsize
  have hM : (M : ℝ) * 2 ^ d ≤ (m : ℝ) := by exact_mod_cast hMm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hs1 : (1 : ℝ) ≤ (C.size : ℝ) := by exact_mod_cast circuit_size_pos C
  -- The common bound: `M * (2 * C.size) ^ d ≤ (2 m) ^ (d + 1)`.
  have hcommon : (M : ℝ) * (2 * (C.size : ℝ)) ^ d ≤ (2 * (m : ℝ)) ^ (d + 1) := by
    calc (M : ℝ) * (2 * (C.size : ℝ)) ^ d
        = (M : ℝ) * 2 ^ d * (C.size : ℝ) ^ d := by rw [mul_pow]; ring
      _ ≤ (m : ℝ) * (2 * (m : ℝ)) ^ d :=
          mul_le_mul hM (pow_le_pow_left₀ (by positivity) hC d)
            (by positivity) hm0
      _ ≤ (2 * (m : ℝ)) * (2 * (m : ℝ)) ^ d :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 * (m : ℝ)) ^ (d + 1) := by rw [pow_succ]; ring
  refine ⟨m, fun x ↦ ¬g x, ⟨C.negateOutput, C.negateOutput_isDD hdet,
    C.negateOutput_computes hcomputes, ?_⟩,
    ⟨C.toPOG.negate, C.toPOG.negate_isPartitioned (C.toPOG_isPartitioned hdet),
    C.toPOG.negate_computes (C.toPOG_computes hcomputes), ?_⟩⟩
  · intro D hDNNF hD
    have hsize : (C.negateOutput.size : ℝ) ≤ 2 * (C.size : ℝ) := by
      rw [C.negateOutput_size]
      push_cast
      linarith
    calc (M : ℝ) * (C.negateOutput.size : ℝ) ^ d
        ≤ (M : ℝ) * (2 * (C.size : ℝ)) ^ d :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hsize d) (by positivity)
      _ ≤ (2 * (m : ℝ)) ^ (d + 1) := hcommon
      _ < (D.size : ℝ) := hlow D hDNNF hD
  · intro D hDNNF hD
    have hsize : (C.toPOG.negate.size : ℝ) ≤ 2 * (C.size : ℝ) := by
      rw [C.toPOG.negate_size, C.toPOG_size]
      linarith
    calc (M : ℝ) * (C.toPOG.negate.size : ℝ) ^ d
        ≤ (M : ℝ) * (2 * (C.size : ℝ)) ^ d :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hsize d) (by positivity)
      _ ≤ (2 * (m : ℝ)) ^ (d + 1) := hcommon
      _ < (D.size : ℝ) := hlow D hDNNF hD

/-- Internal negation: `¬L_n` has a d-D circuit and a
POG of size `2^{O(n)}` (explicitly `positiveCircuitBound n + 2`, with
`positiveCircuitBound n ≤ 2^{45 n}` for `n ≥ 13`), every DNNF for it has
size at least `spectralNodeLower n`, which is `2^{Ω(n²)}`, and consequently
neither d-D circuits nor POGs translate into DNNF with polynomial overhead. -/
@[tutorial_box "cor:paper-internal-negation"]
theorem internal_negation_separation :
    (∀ n : ℕ, ∀ hn : 0 < n,
      ∃ ranks : LabelOrders n,
      ∃ a : Fin (encodedInputCount n) →
          ((Fin n × Fin n) → GadgetVector),
        (∃ C : DDCircuit.{0, 0} (Fin (encodedInputCount n)),
          C.IsDD ∧ C.Computes (fun x ↦ ¬hardFunction ranks hn a x) ∧
          C.size ≤ positiveCircuitBound n + 2) ∧
        (∃ P : POG.{0, 0} (Fin (encodedInputCount n)),
          P.IsPartitioned ∧ P.Computes (fun x ↦ ¬hardFunction ranks hn a x) ∧
          P.size ≤ positiveCircuitBound n + 1) ∧
        ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
          D.IsDNNF →
          D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
          spectralNodeLower n ≤ (D.size : ℝ)) ∧
    ∀ d M : ℕ,
      ∃ (m : ℕ) (f : (Fin m → Bool) → Prop),
        (∃ C : DDCircuit.{0, 0} (Fin m), C.IsDD ∧ C.Computes f ∧
          ∀ D : NNFCircuit.{0, 0} (Fin m), D.IsDNNF → D.Computes f →
            (M : ℝ) * (C.size : ℝ) ^ d < (D.size : ℝ)) ∧
        (∃ P : POG.{0, 0} (Fin m), P.IsPartitioned ∧ P.Computes f ∧
          ∀ D : NNFCircuit.{0, 0} (Fin m), D.IsDNNF → D.Computes f →
            (M : ℝ) * (P.size : ℝ) ^ d < (D.size : ℝ)) :=
  ⟨exists_dD_circuit_and_POG_for_complement,
    no_polynomial_translation_of_internal_negation⟩

end

end DDNNFNegation
