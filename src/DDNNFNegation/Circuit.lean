import Mathlib
import TutorialBox

/-!
# The proof-side NNF circuit model

A circuit has finitely many shared gates, with a rank that decreases along
input references. Conjunctions are binary and disjunctions have list-valued
inputs. The structure stores semantics and syntactic supports together with
their local equations; `semantics_unique` and `support_unique` show that
these equations determine them.

Size counts nodes. Internal edge counts are used in the rectangle-cover
argument. `CircuitTransport.lean` connects this model to the concrete
array-indexed circuits in `TrustBoundary.lean`.
-/

namespace DDNNFNegation

open Finset

/-- One gate of a negation-normal-form circuit. -/
inductive NNFNode (Var Gate : Type*) where
  | top
  | bot
  | pos (x : Var)
  | neg (x : Var)
  | conj (left right : Gate)
  | disj (children : List Gate)

namespace NNFNode

/-- Local semantics, given the meanings of child gates. -/
def Holds {Var Gate : Type*} (v : Var → Bool) (child : Gate → Prop) :
    NNFNode Var Gate → Prop
  | top => True
  | bot => False
  | pos x => v x = true
  | neg x => v x = false
  | conj left right => child left ∧ child right
  | disj children => ∃ gate ∈ children, child gate

/-- Local support, given the supports of child gates. -/
def Support {Var Gate : Type*} [DecidableEq Var]
    (child : Gate → Finset Var) : NNFNode Var Gate → Finset Var
  | top => ∅
  | bot => ∅
  | pos x => {x}
  | neg x => {x}
  | conj left right => child left ∪ child right
  | disj children =>
      children.foldl (fun result gate ↦ result ∪ child gate) ∅

/-- The child relation of a local gate description. -/
def IsChild {Var Gate : Type*} (child : Gate) : NNFNode Var Gate → Prop
  | conj left right => child = left ∨ child = right
  | disj children => child ∈ children
  | _ => False

/-- The number of inputs of a gate: the edges into it. -/
def fanIn {Var Gate : Type*} : NNFNode Var Gate → ℕ
  | conj _ _ => 2
  | disj children => children.length
  | _ => 0

end NNFNode

/-- Membership in a left fold of unions over a list. -/
theorem mem_foldl_union {α β : Type*} [DecidableEq β] (x : β)
    (l : List α) (child : α → Finset β) (acc : Finset β) :
    x ∈ l.foldl (fun result j ↦ result ∪ child j) acc ↔
      x ∈ acc ∨ ∃ j ∈ l, x ∈ child j := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

/-- A finite shared NNF circuit with explicit, locally verified semantics and
support.  The rank condition rules out directed cycles. -/
@[tutorial_box "def:tutorial-circuits"]
structure NNFCircuit (Var : Type*) [DecidableEq Var] where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  node : Gate → NNFNode Var Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child,
    (node gate).IsChild child → rank child < rank gate
  semantics : Gate → (Var → Bool) → Prop
  semantics_eq : ∀ gate v,
    semantics gate v ↔ (node gate).Holds v (fun child ↦ semantics child v)
  support : Gate → Finset Var
  support_eq : ∀ gate,
    support gate = (node gate).Support support

namespace NNFCircuit

instance {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) :
    Fintype C.Gate := C.gateFintype

instance {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) :
    DecidableEq C.Gate := C.gateDecidableEq

/-- Number of shared gates. -/
@[tutorial_box "def:tutorial-circuits"]
def size {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) : ℕ :=
  Fintype.card C.Gate

/-- Number of edges, the sum of the fan-ins of the gates. Internal
construction bounds use this measure; the tutorial counts nodes with
`size`. -/
def edgeCount {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) : ℕ :=
  ∑ gate, (C.node gate).fanIn

/-- Every disjunction has at most two inputs; a conjunction always has
exactly two. -/
def IsFanInTwo {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) : Prop :=
  ∀ gate children, C.node gate = .disj children → children.length ≤ 2

/-- A fan-in-two circuit has at most two edges per gate. -/
theorem edgeCount_le_two_mul_size {Var : Type*} [DecidableEq Var]
    (C : NNFCircuit Var) (hfan : C.IsFanInTwo) :
    C.edgeCount ≤ 2 * C.size := by
  unfold edgeCount size
  calc ∑ gate, (C.node gate).fanIn ≤ ∑ _gate : C.Gate, 2 := by
        apply Finset.sum_le_sum
        intro gate _
        cases hnode : C.node gate with
        | top => exact Nat.zero_le _
        | bot => exact Nat.zero_le _
        | pos x => exact Nat.zero_le _
        | neg x => exact Nat.zero_le _
        | conj left right => exact le_rfl
        | disj children => exact hfan gate children hnode
    _ = 2 * Fintype.card C.Gate := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- Function computed at the distinguished output gate. -/
@[tutorial_box "def:tutorial-circuits"]
def Computes {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var)
    (f : (Var → Bool) → Prop) : Prop :=
  ∀ v, C.semantics C.output v ↔ f v

/-- Every conjunction combines disjoint variable sets. -/
@[tutorial_box "def:tutorial-circuits"]
def IsDecomposable {Var : Type*} [DecidableEq Var]
    (C : NNFCircuit Var) : Prop :=
  ∀ gate left right, C.node gate = .conj left right →
    Disjoint (C.support left) (C.support right)

/-- Every disjunction has mutually exclusive children. -/
@[tutorial_box "def:tutorial-circuits"]
def IsDeterministic {Var : Type*} [DecidableEq Var]
    (C : NNFCircuit Var) : Prop :=
  ∀ gate children, C.node gate = .disj children →
    ∀ left, left ∈ children → ∀ right, right ∈ children →
      left ≠ right → ∀ v,
        ¬(C.semantics left v ∧ C.semantics right v)

/-- A DNNF in the finite shared-circuit model. -/
def IsDNNF {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) : Prop :=
  C.IsDecomposable

/-- A deterministic DNNF in the finite shared-circuit model. -/
def IsDeterministicDNNF {Var : Type*} [DecidableEq Var]
    (C : NNFCircuit Var) : Prop :=
  C.IsDecomposable ∧ C.IsDeterministic

end NNFCircuit

/-- No polynomial bounds negation in this model: for every degree `d` and
multiplier `M`, there is a d-DNNF `C` such that every DNNF for its negation
has more than `M * C.size ^ d` nodes. The adversary may use additional
variables and any finite gate type. -/
def NotClosedUnderNegationNNFCircuit.{u} : Prop :=
  ∀ d M : ℕ,
    ∃ C : NNFCircuit.{0, 0} ℕ,
      C.IsDeterministicDNNF ∧
        ∀ D : NNFCircuit.{0, u} ℕ, D.IsDNNF →
          D.Computes (fun v ↦ ¬ C.semantics C.output v) →
            M * C.size ^ d < D.size

namespace NNFNode

variable {Var Gate : Type*}

/-- Local truth depends on the child meanings only at actual children. -/
theorem holds_congr (node : NNFNode Var Gate) (v : Var → Bool)
    (c₁ c₂ : Gate → Prop)
    (h : ∀ child, node.IsChild child → (c₁ child ↔ c₂ child)) :
    node.Holds v c₁ ↔ node.Holds v c₂ := by
  cases node with
  | top => rfl
  | bot => rfl
  | pos x => rfl
  | neg x => rfl
  | conj left right =>
      simp only [Holds]
      rw [h left (Or.inl rfl), h right (Or.inr rfl)]
  | disj children =>
      simp only [Holds]
      constructor
      · rintro ⟨gate, hmem, hgate⟩
        exact ⟨gate, hmem, (h gate hmem).mp hgate⟩
      · rintro ⟨gate, hmem, hgate⟩
        exact ⟨gate, hmem, (h gate hmem).mpr hgate⟩

/-- Local support depends on the child supports only at actual children. -/
theorem support_congr [DecidableEq Var] (node : NNFNode Var Gate)
    (s₁ s₂ : Gate → Finset Var)
    (h : ∀ child, node.IsChild child → s₁ child = s₂ child) :
    node.Support s₁ = node.Support s₂ := by
  cases node with
  | top => rfl
  | bot => rfl
  | pos x => rfl
  | neg x => rfl
  | conj left right =>
      simp only [Support]
      rw [h left (Or.inl rfl), h right (Or.inr rfl)]
  | disj children =>
      simp only [Support, IsChild] at h ⊢
      -- The fold visits exactly the listed children.
      suffices hgen : ∀ (l : List Gate) (acc : Finset Var),
          (∀ child ∈ l, s₁ child = s₂ child) →
          l.foldl (fun result gate ↦ result ∪ s₁ gate) acc =
            l.foldl (fun result gate ↦ result ∪ s₂ gate) acc from
        hgen children ∅ h
      intro l
      induction l with
      | nil => intro acc _; rfl
      | cons head tail ih =>
          intro acc hmem
          simp only [List.foldl_cons]
          rw [hmem head (List.mem_cons_self ..)]
          exact ih _ (fun child hchild =>
            hmem child (List.mem_cons_of_mem _ hchild))

end NNFNode

namespace NNFCircuit

variable {Var : Type*} [DecidableEq Var]

/-- **The semantics field is determined by its equation.**  Any
`f` satisfying the same local recursion as `C.semantics` agrees with it
at every gate, by induction along the rank that `child_rank` provides. -/
theorem semantics_unique (C : NNFCircuit Var)
    (f : C.Gate → (Var → Bool) → Prop)
    (hf : ∀ gate v, f gate v ↔ (C.node gate).Holds v (fun child ↦ f child v))
    (gate : C.Gate) (v : Var → Bool) :
    f gate v ↔ C.semantics gate v := by
  have key : ∀ r : ℕ, ∀ gate : C.Gate, C.rank gate < r → ∀ v : Var → Bool,
      (f gate v ↔ C.semantics gate v) := by
    intro r
    induction r with
    | zero => intro gate hgate; omega
    | succ r ih =>
        intro gate hgate v
        rw [hf gate v, C.semantics_eq gate v]
        apply NNFNode.holds_congr
        intro child hchild
        have hlt := C.child_rank gate child hchild
        exact ih child (by omega) v
  exact key (C.rank gate + 1) gate (by omega) v

/-- **The support field is determined by its equation.**  Any `s`
satisfying the same local recursion as `C.support` agrees with it at
every gate. -/
theorem support_unique (C : NNFCircuit Var) (s : C.Gate → Finset Var)
    (hs : ∀ gate, s gate = (C.node gate).Support s) (gate : C.Gate) :
    s gate = C.support gate := by
  have key : ∀ r : ℕ, ∀ gate : C.Gate, C.rank gate < r →
      s gate = C.support gate := by
    intro r
    induction r with
    | zero => intro gate hgate; omega
    | succ r ih =>
        intro gate hgate
        rw [hs gate, C.support_eq gate]
        apply NNFNode.support_congr
        intro child hchild
        have hlt := C.child_rank gate child hchild
        exact ih child (by omega)
  exact key (C.rank gate + 1) gate (by omega)

end NNFCircuit

end DDNNFNegation
