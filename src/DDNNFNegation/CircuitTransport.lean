import DDNNFNegation.TrustBoundary
import DDNNFNegation.Circuit

/-!
# Transport between the two circuit models

`NNFCircuit.toCircuit` numbers gates in topological order, preserving
semantics, supports, node count, and the d-DNNF property. In the reverse
direction, `Circuit.toBinaryNNFCircuit` replaces arbitrary-fan-in
conjunctions by binary ones. It preserves semantics and the DNNF property
and uses `s * (s + 1)` nodes for an input of size `s`.

These are the two directions needed to carry the small witness and the
lower bound to the concrete statement in `TrustBoundary.lean`.
-/

namespace DDNNFNegation

section

variable {Var : Type}

namespace Node

variable {m : ℕ}

/-- An AND node is true exactly when every child position is true, for a
child function that ignores the packaged membership proof. -/
theorem evalLocal_and (children : Finset (Fin m)) (v : Var → Bool)
    (f : Fin m → Bool) :
    (Node.and children).evalLocal v (fun j ↦ f j.1) = true ↔
      ∀ j ∈ children, f j = true := by
  simp [evalLocal, Node.children]

/-- An OR node is true exactly when some child position is true. -/
theorem evalLocal_or (children : Finset (Fin m)) (v : Var → Bool)
    (f : Fin m → Bool) :
    (Node.or children).evalLocal v (fun j ↦ f j.1) = true ↔
      ∃ j ∈ children, f j = true := by
  simp [evalLocal, Node.children]

/-- The support of an AND node is the union of the child supports. -/
theorem supportLocal_and [DecidableEq Var] (children : Finset (Fin m))
    (f : Fin m → Finset Var) :
    (Node.and children).supportLocal (fun j ↦ f j.1) =
      children.biUnion f := by
  ext x
  simp only [supportLocal, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Subtype.exists, exists_prop]
  exact Iff.rfl

/-- The support of an OR node is the union of the child supports. -/
theorem supportLocal_or [DecidableEq Var] (children : Finset (Fin m))
    (f : Fin m → Finset Var) :
    (Node.or children).supportLocal (fun j ↦ f j.1) =
      children.biUnion f := by
  ext x
  simp only [supportLocal, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Subtype.exists, exists_prop]
  exact Iff.rfl

end Node

/-! ## From an array circuit to a shared-gate circuit -/

namespace Circuit

variable (C : Circuit Var)

/-- The defining equation for recursive circuit evaluation. -/
theorem eval_eq (v : Var → Bool) (i : Fin C.size) :
    C.eval v i = (C.node i).evalLocal v (fun j ↦ C.eval v j.1) := by
  rw [Circuit.eval]

/-- The defining equation for recursive circuit support. -/
theorem support_eq [DecidableEq Var] (i : Fin C.size) :
    C.support i = (C.node i).supportLocal (fun j ↦ C.support j.1) := by
  rw [Circuit.support]

/-- Recursive array semantics evaluates an AND as the conjunction of its child values. -/
theorem eval_and {i : Fin C.size} {children : Finset (Fin C.size)}
    (h : C.node i = .and children) (v : Var → Bool) :
    C.eval v i = true ↔ ∀ j ∈ children, C.eval v j = true := by
  rw [C.eval_eq, h, Node.evalLocal_and]

/-- Recursive array semantics evaluates an OR as the disjunction of its child values. -/
theorem eval_or {i : Fin C.size} {children : Finset (Fin C.size)}
    (h : C.node i = .or children) (v : Var → Bool) :
    C.eval v i = true ↔ ∃ j ∈ children, C.eval v j = true := by
  rw [C.eval_eq, h, Node.evalLocal_or]

/-- The support of an array AND is the union of its child supports. -/
theorem support_and [DecidableEq Var] {i : Fin C.size}
    {children : Finset (Fin C.size)} (h : C.node i = .and children) :
    C.support i = children.biUnion C.support := by
  rw [C.support_eq, h, Node.supportLocal_and]

/-- The support of an array OR is the union of its child supports. -/
theorem support_or [DecidableEq Var] {i : Fin C.size}
    {children : Finset (Fin C.size)} (h : C.node i = .or children) :
    C.support i = children.biUnion C.support := by
  rw [C.support_eq, h, Node.supportLocal_or]

/-- Gates of the binary expansion.  `(i,k)` stores the conjunction of the
children of original gate `i` whose positions are below `k`.  The final
position `k = size` is the translated original gate. -/
abbrev BinaryGate := Fin C.size × Fin (C.size + 1)

/-- The final expansion gate representing original position `i`. -/
def binaryRoot (i : Fin C.size) : C.BinaryGate :=
  (i, ⟨C.size, by omega⟩)

/-- The original child positions accumulated before prefix boundary `k`. -/
def prefixChildren (children : Finset (Fin C.size)) (k : Fin (C.size + 1)) :
    Finset (Fin C.size) :=
  Finset.univ.filter fun j ↦ j ∈ children ∧ j.val < k.val

/-- Meaning assigned to every gate of the binary expansion. -/
def binarySemantics (g : C.BinaryGate) (v : Var → Bool) : Prop :=
  match C.node g.1 with
  | .and children =>
      ∀ j ∈ C.prefixChildren children g.2, C.eval v j = true
  | _ => if g.2.val = C.size then C.eval v g.1 = true else True

/-- Variable support assigned to every gate of the binary expansion. -/
def binarySupport [DecidableEq Var] (g : C.BinaryGate) : Finset Var :=
  match C.node g.1 with
  | .and children =>
      (C.prefixChildren children g.2).biUnion C.support
  | _ => if g.2.val = C.size then C.support g.1 else ∅

/-- Local node of the binary expansion.  An unbounded conjunction is scanned
once through all possible child positions.  A position that is not a child
contributes the always-true prefix base and therefore changes no meaning.
An unbounded disjunction lists its child set in increasing order. -/
def binaryNode (g : C.BinaryGate) : NNFNode Var C.BinaryGate :=
  match C.node g.1 with
  | .and children =>
      if hk : g.2.val = 0 then .top
      else
        let j : Fin C.size := ⟨g.2.val - 1, by omega⟩
        let previous : Fin (C.size + 1) := ⟨g.2.val - 1, by omega⟩
        .conj (g.1, previous)
          (if j ∈ children then C.binaryRoot j else (g.1, ⟨0, by omega⟩))
  | .const b =>
      if g.2.val = C.size then if b then .top else .bot else .top
  | .lit x b =>
      if g.2.val = C.size then if b then .pos x else .neg x else .top
  | .or children =>
      if g.2.val = C.size
      then .disj ((children.sort (· ≤ ·)).map C.binaryRoot)
      else .top

/-- An original array child lies below its parent's root in the binary expansion. -/
theorem binaryRoot_rank_lt {i j : Fin C.size} (hji : j < i)
    (k : Fin (C.size + 1)) :
    j.val * (C.size + 1) + C.size <
      i.val * (C.size + 1) + k.val := by
  have hstep : j.val * (C.size + 1) + C.size <
      (j.val + 1) * (C.size + 1) := by
    rw [Nat.add_mul]
    omega
  have hbuckets : (j.val + 1) * (C.size + 1) ≤
      i.val * (C.size + 1) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hji)
  exact lt_of_lt_of_le hstep (le_trans hbuckets (Nat.le_add_right _ _))

/-- The binary expansion reproduces the recursive array value at every original gate. -/
theorem binarySemantics_root (i : Fin C.size) (v : Var → Bool) :
    C.binarySemantics (C.binaryRoot i) v ↔ C.eval v i = true := by
  cases hnode : C.node i with
  | const b => simp [binarySemantics, binaryRoot, hnode]
  | lit x b => simp [binarySemantics, binaryRoot, hnode]
  | or children => simp [binarySemantics, binaryRoot, hnode]
  | and children =>
      rw [C.eval_and hnode]
      simp only [binarySemantics, binaryRoot, hnode, prefixChildren,
        Finset.mem_filter, Finset.mem_univ, true_and, Fin.is_lt, and_true]

/-- The binary expansion reproduces the original support at every root position. -/
theorem binarySupport_root [DecidableEq Var] (i : Fin C.size) :
    C.binarySupport (C.binaryRoot i) = C.support i := by
  cases hnode : C.node i with
  | const b => simp [binarySupport, binaryRoot, hnode]
  | lit x b => simp [binarySupport, binaryRoot, hnode]
  | or children => simp [binarySupport, binaryRoot, hnode]
  | and children =>
      rw [C.support_and hnode]
      ext x
      simp [binarySupport, binaryRoot, hnode, prefixChildren]

/-- Binary expansion of an arbitrary-fan-in array circuit. -/
def toBinaryNNFCircuit [DecidableEq Var] : NNFCircuit Var where
  Gate := C.BinaryGate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := C.binaryRoot C.output
  node := C.binaryNode
  rank g := g.1.val * (C.size + 1) + g.2.val
  child_rank := by
    intro g child hchild
    cases hnode : C.node g.1 with
    | const b =>
        by_cases hlast : g.2.val = C.size <;>
          cases b <;> simp [binaryNode, hnode, hlast, NNFNode.IsChild] at hchild
    | lit x b =>
        by_cases hlast : g.2.val = C.size <;>
          cases b <;> simp [binaryNode, hnode, hlast, NNFNode.IsChild] at hchild
    | or children =>
        by_cases hlast : g.2.val = C.size
        · simp only [binaryNode, hnode, hlast, if_pos, NNFNode.IsChild,
            List.mem_map, Finset.mem_sort] at hchild
          obtain ⟨j, hj, rfl⟩ := hchild
          have hji := C.children_lt g.1 j (by simpa [Node.children, hnode] using hj)
          dsimp [binaryRoot]
          exact C.binaryRoot_rank_lt hji g.2
        · simp [binaryNode, hnode, hlast, NNFNode.IsChild] at hchild
    | and children =>
        by_cases hk : g.2.val = 0
        · simp [binaryNode, hnode, hk, NNFNode.IsChild] at hchild
        · simp only [binaryNode, hnode, hk, NNFNode.IsChild] at hchild
          rcases hchild with rfl | rfl
          · dsimp
            omega
          · by_cases hjmem : (⟨g.2.val - 1, by omega⟩ : Fin C.size) ∈ children
            · simp only [hjmem, if_pos]
              dsimp [binaryRoot]
              have hj := C.children_lt g.1
                ⟨g.2.val - 1, by omega⟩ (by simpa [Node.children, hnode])
              exact C.binaryRoot_rank_lt hj g.2
            · simp only [hjmem, if_false]
              dsimp
              omega
  semantics := C.binarySemantics
  semantics_eq := by
    intro g v
    cases hnode : C.node g.1 with
    | const b =>
        have heval : C.eval v g.1 = b := by
          rw [C.eval_eq, hnode]
          rfl
        by_cases hlast : g.2.val = C.size <;>
          cases b <;>
          simp [binarySemantics, binaryNode, hnode, hlast,
            NNFNode.Holds, heval]
    | lit x b =>
        have heval : C.eval v g.1 = (v x == b) := by
          rw [C.eval_eq, hnode]
          rfl
        by_cases hlast : g.2.val = C.size <;>
          cases b <;> cases v x <;>
          simp [binarySemantics, binaryNode, hnode, hlast,
            NNFNode.Holds, heval]
    | or children =>
        by_cases hlast : g.2.val = C.size
        · simp only [binarySemantics, binaryNode, hnode, hlast, if_pos,
            NNFNode.Holds]
          rw [C.eval_or hnode]
          constructor
          · rintro ⟨j, hj, htrue⟩
            exact ⟨C.binaryRoot j,
              List.mem_map.mpr ⟨j, (Finset.mem_sort _).mpr hj, rfl⟩,
              (C.binarySemantics_root j v).2 htrue⟩
          · rintro ⟨child, hchild, htrue⟩
            obtain ⟨j, hj, hroot⟩ := List.mem_map.mp hchild
            refine ⟨j, (Finset.mem_sort _).mp hj,
              (C.binarySemantics_root j v).1 ?_⟩
            rw [hroot]
            exact htrue
        · simp [binarySemantics, binaryNode, hnode, hlast, NNFNode.Holds]
    | and children =>
        by_cases hk : g.2.val = 0
        · simp [binarySemantics, binaryNode, hnode, hk,
            prefixChildren, NNFNode.Holds]
        · let j : Fin C.size := ⟨g.2.val - 1, by omega⟩
          let previous : Fin (C.size + 1) := ⟨g.2.val - 1, by omega⟩
          by_cases hjmem : j ∈ children
          · rw [show C.binaryNode g =
                .conj (g.1, previous) (C.binaryRoot j) by
              simp [binaryNode, hnode, hk, hjmem, j, previous]]
            simp only [NNFNode.Holds]
            rw [C.binarySemantics_root]
            simp only [binarySemantics, hnode]
            constructor
            · intro hall
              refine ⟨?_, hall j ?_⟩
              · intro q hq
                exact hall q (by
                  simp only [prefixChildren, Finset.mem_filter,
                    Finset.mem_univ, true_and] at hq ⊢
                  have hqval : q.val < g.2.val - 1 := by
                    simpa [previous] using hq.2
                  exact ⟨hq.1, by omega⟩)
              · simp only [prefixChildren, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                exact ⟨hjmem, by dsimp [j]; omega⟩
            · rintro ⟨hprevious, hcurrent⟩ q hq
              simp only [prefixChildren, Finset.mem_filter,
                Finset.mem_univ, true_and] at hq
              by_cases hqj : q = j
              · simpa [hqj] using hcurrent
              · exact hprevious q (by
                  simp only [prefixChildren, Finset.mem_filter,
                    Finset.mem_univ, true_and]
                  have hqvalne : q.val ≠ g.2.val - 1 := by
                    intro heq
                    apply hqj
                    apply Fin.ext
                    simpa [j] using heq
                  have hqltval : q.val < g.2.val := hq.2
                  have hbound : q.val < g.2.val - 1 := by omega
                  exact ⟨hq.1, by simpa [previous] using hbound⟩)
          · rw [show C.binaryNode g =
                .conj (g.1, previous) (g.1, ⟨0, by omega⟩) by
              simp [binaryNode, hnode, hk, hjmem, j, previous]]
            simp only [NNFNode.Holds, binarySemantics, hnode]
            constructor
            · intro hall
              refine ⟨?_, ?_⟩
              · intro q hq
                exact hall q (by
                  simp only [prefixChildren, Finset.mem_filter,
                    Finset.mem_univ, true_and] at hq ⊢
                  have hqval : q.val < g.2.val - 1 := by
                    simpa [previous] using hq.2
                  exact ⟨hq.1, by omega⟩)
              · simp [prefixChildren]
            · rintro ⟨hprevious, _⟩ q hq
              apply hprevious q
              simp only [prefixChildren, Finset.mem_filter,
                Finset.mem_univ, true_and] at hq ⊢
              refine ⟨hq.1, ?_⟩
              have hnotmem : q ≠ j := by
                intro hqj
                subst q
                exact hjmem hq.1
              have hqvalne : q.val ≠ g.2.val - 1 := by
                intro heq
                apply hnotmem
                apply Fin.ext
                simpa [j] using heq
              have hqltval : q.val < g.2.val := hq.2
              have hbound : q.val < g.2.val - 1 := by omega
              simpa [previous] using hbound
  support := C.binarySupport
  support_eq := by
    intro g
    cases hnode : C.node g.1 with
    | const b =>
        have hsupport : C.support g.1 = ∅ := by
          rw [C.support_eq, hnode]
          rfl
        by_cases hlast : g.2.val = C.size <;>
          cases b <;>
          simp [binarySupport, binaryNode, hnode, hlast,
            NNFNode.Support, hsupport]
    | lit x b =>
        have hsupport : C.support g.1 = {x} := by
          rw [C.support_eq, hnode]
          rfl
        by_cases hlast : g.2.val = C.size <;>
          cases b <;>
          simp [binarySupport, binaryNode, hnode, hlast,
            NNFNode.Support, hsupport]
    | or children =>
        by_cases hlast : g.2.val = C.size
        · have hleft : C.binarySupport g = C.support g.1 := by
            simp [binarySupport, hnode, hlast]
          rw [hleft]
          simp only [binaryNode, hnode, hlast, if_pos, NNFNode.Support]
          rw [C.support_or hnode, List.foldl_map]
          ext x
          rw [mem_foldl_union]
          simp [Finset.mem_sort, C.binarySupport_root]
        · simp [binarySupport, binaryNode, hnode, hlast, NNFNode.Support]
    | and children =>
        by_cases hk : g.2.val = 0
        · simp [binarySupport, binaryNode, hnode, hk,
            prefixChildren, NNFNode.Support]
        · let j : Fin C.size := ⟨g.2.val - 1, by omega⟩
          let previous : Fin (C.size + 1) := ⟨g.2.val - 1, by omega⟩
          by_cases hjmem : j ∈ children
          · rw [show C.binaryNode g =
                .conj (g.1, previous) (C.binaryRoot j) by
              simp [binaryNode, hnode, hk, hjmem, j, previous]]
            simp only [NNFNode.Support]
            rw [C.binarySupport_root]
            simp only [binarySupport, hnode]
            ext x
            simp only [Finset.mem_union, Finset.mem_biUnion, prefixChildren,
              Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨q, ⟨hqmem, hqlt⟩, hxq⟩
              by_cases hqj : q = j
              · exact Or.inr (by simpa [hqj] using hxq)
              · have hqvalne : q.val ≠ g.2.val - 1 := by
                  intro heq
                  apply hqj
                  apply Fin.ext
                  simpa [j] using heq
                have hqltval : q.val < g.2.val := hqlt
                have hbound : q.val < g.2.val - 1 := by omega
                exact Or.inl
                  ⟨q, ⟨hqmem, by simpa [previous] using hbound⟩, hxq⟩
            · rintro (⟨q, ⟨hqmem, hqlt⟩, hxq⟩ | hxj)
              · have hqval : q.val < g.2.val - 1 := by
                  simpa [previous] using hqlt
                exact ⟨q, ⟨hqmem, by omega⟩, hxq⟩
              · exact ⟨j, ⟨hjmem, by dsimp [j]; omega⟩, hxj⟩
          · rw [show C.binaryNode g =
                .conj (g.1, previous) (g.1, ⟨0, by omega⟩) by
              simp [binaryNode, hnode, hk, hjmem, j, previous]]
            simp only [NNFNode.Support, binarySupport, hnode]
            have hzero :
                (C.prefixChildren children (⟨0, by omega⟩ : Fin (C.size + 1))).biUnion
                    C.support = ∅ := by
              ext y
              simp [prefixChildren]
            rw [hzero, Finset.union_empty]
            ext x
            simp only [Finset.mem_biUnion, prefixChildren,
              Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨q, ⟨hqmem, hqlt⟩, hxq⟩
              refine ⟨q, ⟨hqmem, ?_⟩, hxq⟩
              have hqj : q ≠ j := by
                intro heq
                subst q
                exact hjmem hqmem
              have hqvalne : q.val ≠ g.2.val - 1 := by
                intro heq
                apply hqj
                apply Fin.ext
                simpa [j] using heq
              have hqltval : q.val < g.2.val := hqlt
              have hbound : q.val < g.2.val - 1 := by omega
              simpa [previous] using hbound
            · rintro ⟨q, ⟨hqmem, hqlt⟩, hxq⟩
              have hqval : q.val < g.2.val - 1 := by
                simpa [previous] using hqlt
              exact ⟨q, ⟨hqmem, by omega⟩, hxq⟩

/-- The shared binary expansion has `size * (size + 1)` gates. -/
theorem size_toBinaryNNFCircuit [DecidableEq Var] :
    C.toBinaryNNFCircuit.size = C.size * (C.size + 1) := by
  change Fintype.card (Fin C.size × Fin (C.size + 1)) = _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- Array decomposability implies decomposability of the shared binary expansion. -/
theorem isDNNF_toBinaryNNFCircuit [DecidableEq Var]
    (hC : C.IsDNNF) : C.toBinaryNNFCircuit.IsDNNF := by
  intro gate left right hgate
  cases hnode : C.node gate.1 with
  | const b =>
      by_cases hlast : gate.2.val = C.size <;>
        cases b <;> simp [toBinaryNNFCircuit, binaryNode, hnode, hlast] at hgate
  | lit x b =>
      by_cases hlast : gate.2.val = C.size <;>
        cases b <;> simp [toBinaryNNFCircuit, binaryNode, hnode, hlast] at hgate
  | or children =>
      by_cases hlast : gate.2.val = C.size <;>
        simp [toBinaryNNFCircuit, binaryNode, hnode, hlast] at hgate
  | and children =>
      simp only [toBinaryNNFCircuit, binaryNode, hnode] at hgate
      split at hgate
      · simp at hgate
      · let j : Fin C.size := ⟨gate.2.val - 1, by omega⟩
        split at hgate
        · obtain ⟨rfl, rfl⟩ := NNFNode.conj.inj hgate
          change Disjoint
            (C.binarySupport (gate.1, ⟨gate.2.val - 1, by omega⟩))
            (C.binarySupport (C.binaryRoot j))
          rw [C.binarySupport_root]
          rw [Finset.disjoint_left]
          intro x hxprefix hxj
          simp only [binarySupport, hnode, Finset.mem_biUnion,
            prefixChildren, Finset.mem_filter, Finset.mem_univ,
            true_and] at hxprefix
          obtain ⟨q, ⟨hqmem, hqlt⟩, hxq⟩ := hxprefix
          have hqne : q ≠ j := by
            intro heq
            subst q
            dsimp [j] at hqlt
            omega
          exact (Finset.disjoint_left.mp
            (hC gate.1 children hnode q hqmem j (by assumption) hqne)) hxq hxj
        · obtain ⟨rfl, rfl⟩ := NNFNode.conj.inj hgate
          change Disjoint
            (C.binarySupport (gate.1, ⟨gate.2.val - 1, by omega⟩))
            (C.binarySupport (gate.1, ⟨0, by omega⟩))
          simp [binarySupport, hnode, prefixChildren]

end Circuit

/-! ## From a shared-gate circuit to an array circuit -/

namespace NNFNode

variable {Gate : Type} {m : ℕ}

/-- Write a shared-gate node into an array-circuit gate, naming each child
by its position `e child`. -/
def toNode (e : Gate → Fin m) : NNFNode Var Gate → Node Var m
  | top => .const true
  | bot => .const false
  | pos x => .lit x true
  | neg x => .lit x false
  | conj left right => .and {e left, e right}
  | disj children => .or (children.map e).toFinset

/-- Renumbered child-set membership corresponds to an original child reference. -/
theorem mem_children_toNode (n : NNFNode Var Gate) (e : Gate → Fin m)
    (j : Fin m) :
    j ∈ (n.toNode e).children ↔ ∃ g, n.IsChild g ∧ e g = j := by
  cases n with
  | top => simp [toNode, Node.children, NNFNode.IsChild]
  | bot => simp [toNode, Node.children, NNFNode.IsChild]
  | pos x => simp [toNode, Node.children, NNFNode.IsChild]
  | neg x => simp [toNode, Node.children, NNFNode.IsChild]
  | conj left right =>
    show j ∈ ({e left, e right} : Finset (Fin m)) ↔
      ∃ g, (g = left ∨ g = right) ∧ e g = j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨left, Or.inl rfl, rfl⟩
      · exact ⟨right, Or.inr rfl, rfl⟩
    · rintro ⟨g, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  | disj children =>
    simp [toNode, Node.children, NNFNode.IsChild, List.mem_toFinset,
      List.mem_map]

/-- Translating a proof-side node to an array node preserves its local Boolean operation. -/
theorem eval_toNode (n : NNFNode Var Gate) (e : Gate → Fin m)
    (v : Var → Bool) (child : Fin m → Bool) :
    (n.toNode e).evalLocal v (fun j ↦ child j.1) = true ↔
      n.Holds v (fun g ↦ child (e g) = true) := by
  cases n with
  | conj left right =>
    simp only [toNode, Node.evalLocal_and, NNFNode.Holds, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  | disj children =>
    simp only [toNode, Node.evalLocal_or, NNFNode.Holds, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro ⟨j, ⟨g, hg, rfl⟩, hj⟩
      exact ⟨g, hg, hj⟩
    · rintro ⟨g, hg, hj⟩
      exact ⟨e g, ⟨g, hg, rfl⟩, hj⟩
  | _ => simp [toNode, Node.evalLocal, NNFNode.Holds]

/-- Translating a proof-side node preserves the union of child supports. -/
theorem support_toNode [DecidableEq Var] (n : NNFNode Var Gate)
    (e : Gate → Fin m) (child : Fin m → Finset Var) :
    (n.toNode e).supportLocal (fun j ↦ child j.1) =
      n.Support (fun g ↦ child (e g)) := by
  cases n with
  | conj left right =>
    simp only [toNode, Node.supportLocal_and, NNFNode.Support,
      Finset.biUnion_insert, Finset.singleton_biUnion]
  | disj children =>
    simp only [toNode, Node.supportLocal_or, NNFNode.Support]
    ext x
    rw [mem_foldl_union]
    simp only [Finset.mem_biUnion, List.mem_toFinset, List.mem_map,
      Finset.notMem_empty, false_or]
    constructor
    · rintro ⟨j, ⟨g, hg, rfl⟩, hj⟩
      exact ⟨g, hg, hj⟩
    · rintro ⟨g, hg, hj⟩
      exact ⟨e g, ⟨g, hg, rfl⟩, hj⟩
  | _ => simp [toNode, Node.supportLocal, NNFNode.Support]

/-- Only proof-side conjunctions translate to array AND nodes. -/
theorem toNode_eq_and_iff (e : Gate ≃ Fin m) (n : NNFNode Var Gate)
    (children : Finset (Fin m)) :
    n.toNode e = .and children ↔
      ∃ left right, n = .conj left right ∧ children = {e left, e right} := by
  cases n <;> simp [toNode, eq_comm]

/-- Only proof-side disjunctions translate to array OR nodes. -/
theorem toNode_eq_or_iff (e : Gate ≃ Fin m) (n : NNFNode Var Gate)
    (children : Finset (Fin m)) :
    n.toNode e = .or children ↔
      ∃ l, n = .disj l ∧ children = (l.map e).toFinset := by
  cases n <;> simp [toNode, eq_comm]

end NNFNode

namespace NNFCircuit

variable [DecidableEq Var] (C : NNFCircuit.{0, 0} Var)

/-- Sort key for the gates: rank first, an arbitrary fixed enumeration
second, to break ties. -/
noncomputable def gateKey (g : C.Gate) : ℕ ×ₗ Fin (Fintype.card C.Gate) :=
  toLex (C.rank g, Fintype.equivFin C.Gate g)

/-- The finite enumeration breaks rank ties, giving each gate a distinct sorting key. -/
theorem gateKey_injective : Function.Injective C.gateKey := by
  intro a b h
  have h2 := congrArg (fun p ↦ (ofLex p).2) h
  exact (Fintype.equivFin C.Gate).injective h2

/-- A strict rank decrease implies a strict decrease of the sorting key. -/
theorem gateKey_lt_of_rank_lt {a b : C.Gate} (h : C.rank a < C.rank b) :
    C.gateKey a < C.gateKey b :=
  Prod.Lex.left _ _ h

/-- The gates ordered by their sort key.  A local instance, used only to
list the gates in order. -/
@[instance_reducible] noncomputable def gateOrder : LinearOrder C.Gate :=
  LinearOrder.lift' C.gateKey C.gateKey_injective

attribute [local instance] gateOrder

/-- The induced gate order compares the rank-and-enumeration keys. -/
theorem gateOrder_lt_iff (a b : C.Gate) : a < b ↔ C.gateKey a < C.gateKey b :=
  Iff.rfl

/-- The gates listed in order of increasing rank. -/
noncomputable def gateEnum : C.Gate ≃ Fin C.size :=
  (Fintype.orderIsoFinOfCardEq C.Gate rfl).symm.toEquiv

/-- Sorting by rank places every child before its parent, as the array boundary requires. -/
theorem gateEnum_lt_of_rank_lt {a b : C.Gate} (h : C.rank a < C.rank b) :
    C.gateEnum a < C.gateEnum b :=
  (Fintype.orderIsoFinOfCardEq C.Gate rfl).symm.lt_iff_lt.mpr
    ((C.gateOrder_lt_iff a b).mpr (C.gateKey_lt_of_rank_lt h))

/-- Write a shared-gate circuit into an array, in order of increasing
rank.  Reducible, so that `Fin C.toCircuit.size` and `Fin C.size` are
the same type for rewriting. -/
noncomputable abbrev toCircuit : Circuit Var where
  size := C.size
  node i := (C.node (C.gateEnum.symm i)).toNode C.gateEnum
  children_lt := by
    intro i j hj
    obtain ⟨g, hg, rfl⟩ := (NNFNode.mem_children_toNode _ _ _).mp hj
    have := C.gateEnum_lt_of_rank_lt (C.child_rank _ _ hg)
    simpa using this
  output := C.gateEnum C.output

/-- The array entry at a renumbered gate is its translated proof-side node. -/
theorem node_toCircuit (i : Fin C.size) :
    C.toCircuit.node i = (C.node (C.gateEnum.symm i)).toNode C.gateEnum := rfl

/-- The translated output is the array position of the original output gate. -/
theorem output_toCircuit : C.toCircuit.output = C.gateEnum C.output := rfl

/-- The array circuit's recursive semantics agrees with the proof-side stored semantics. -/
theorem eval_toCircuit (v : Var → Bool) (g : C.Gate) :
    C.toCircuit.eval v (C.gateEnum g) = true ↔ C.semantics g v := by
  refine semantics_unique C (fun g v ↦ C.toCircuit.eval v (C.gateEnum g) = true)
    ?_ g v
  intro g v
  rw [Circuit.eval_eq, node_toCircuit, Equiv.symm_apply_apply,
    NNFNode.eval_toNode]

/-- Array supports agree with proof-side supports at the corresponding gate positions. -/
theorem support_toCircuit (g : C.Gate) :
    C.toCircuit.support (C.gateEnum g) = C.support g := by
  refine support_unique C (fun g ↦ C.toCircuit.support (C.gateEnum g)) ?_ g
  intro g
  rw [Circuit.support_eq, node_toCircuit, Equiv.symm_apply_apply,
    NNFNode.support_toNode]

/-- The support correspondence in the reverse indexing form used by the class-preservation
proof. -/
theorem support_toCircuit' (i : Fin C.size) :
    C.toCircuit.support i = C.support (C.gateEnum.symm i) := by
  have := C.support_toCircuit (C.gateEnum.symm i)
  rwa [Equiv.apply_symm_apply] at this

/-- The final transport preserves both decomposability and determinism at the concrete array
boundary. -/
theorem isDeterministicDNNF_toCircuit (h : C.IsDeterministicDNNF) :
    C.toCircuit.IsDeterministicDNNF := by
  refine ⟨?_, ?_⟩
  · intro i children hi left hleft right hright hne
    rw [node_toCircuit, NNFNode.toNode_eq_and_iff] at hi
    obtain ⟨a, b, hnode, rfl⟩ := hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hleft hright
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · exact absurd rfl hne
    · rw [support_toCircuit', support_toCircuit']
      simpa using h.1 _ _ _ hnode
    · rw [support_toCircuit', support_toCircuit']
      simpa using (h.1 _ _ _ hnode).symm
    · exact absurd rfl hne
  · intro i children hi left hleft right hright hne v
    rw [node_toCircuit, NNFNode.toNode_eq_or_iff] at hi
    obtain ⟨l, hnode, rfl⟩ := hi
    rw [List.mem_toFinset, List.mem_map] at hleft hright
    obtain ⟨a, ha, rfl⟩ := hleft
    obtain ⟨b, hb, rfl⟩ := hright
    have hdet := h.2 _ _ hnode a ha b hb (fun heq ↦ hne (by rw [heq])) v
    have hdet' : ¬ (C.toCircuit.eval v (C.gateEnum a) = true ∧
        C.toCircuit.eval v (C.gateEnum b) = true) := by
      rw [eval_toCircuit, eval_toCircuit]
      exact hdet
    rw [Bool.and_eq_false_iff]
    rcases not_and_or.mp hdet' with hl | hr
    · exact Or.inl (Bool.eq_false_iff.mpr hl)
    · exact Or.inr (Bool.eq_false_iff.mpr hr)

end NNFCircuit

end

end DDNNFNegation
