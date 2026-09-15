import Mathlib

/-!
# The trust boundary: what a circuit is, and the claim

This file is the whole of what a reader must check.  A circuit is an
array of nodes; a node names its children by their positions in the
array, and holds them as a set; truth and variable support are defined
by recursion on the position.  Everything else in the development is a
proof of the claim stated at the end of this file, and Lean's kernel
checks those proofs.
-/

namespace DDNNFNegation

/-- One node of a circuit over the variables `Var`, inside a circuit of
`m` nodes.  A child is named by its position in the circuit's array, and
the children of a node form a finite set of positions. -/
inductive Node (Var : Type) (m : ℕ)
  | const (b : Bool)
  | lit (x : Var) (b : Bool)
  | and (children : Finset (Fin m))
  | or (children : Finset (Fin m))

namespace Node

variable {Var : Type} {m : ℕ}

/-- The set of positions of the children of a node. -/
def children : Node Var m → Finset (Fin m)
  | const _ => ∅
  | lit _ _ => ∅
  | and children => children
  | or children => children

/-- A position together with proof that it is a child of `n`. -/
abbrev ChildPosition (n : Node Var m) := {j // j ∈ n.children}

/-- Truth value of one node under the assignment `v`.  For a child position
`j`, the lookup requires proof that `j` is a child of this node.  A literal
`lit x b` is true when variable `x` has the value `b`; an AND node is true
when every child is, an OR node when some child is. -/
def evalLocal (n : Node Var m) (v : Var → Bool)
    (child : ChildPosition n → Bool) : Bool :=
  match n with
  | const b => b
  | lit x b => v x == b
  | and _ => decide (∀ j, child j = true)
  | or _ => decide (∃ j, child j = true)

/-- Variables mentioned by one node: the union over all child positions.
For a child position `j`, the lookup requires proof that `j` is a child of
this node. -/
def supportLocal [DecidableEq Var] (n : Node Var m)
    (child : ChildPosition n → Finset Var) : Finset Var :=
  match n with
  | const _ => ∅
  | lit x _ => {x}
  | and _
  | or _ => Finset.univ.biUnion child

end Node

/-- A circuit is an array of `size` nodes in topological order: every
child of the node at position `i` sits at a position below `i`.  One
position is the output.  A node named as a child from several positions
is shared. -/
structure Circuit (Var : Type) where
  size : ℕ
  node : Fin size → Node Var size
  children_lt : ∀ i, ∀ j ∈ (node i).children, j < i
  output : Fin size

namespace Circuit

variable {Var : Type}

/-- Truth value of the node at position `i` under the assignment `v`, by
recursion on `i`.  The proof that `j` is a child lets `children_lt` certify
that each recursive call goes to a smaller position. -/
def eval (C : Circuit Var) (v : Var → Bool) (i : Fin C.size) : Bool :=
  (C.node i).evalLocal v fun j ↦ C.eval v j.1
termination_by i.val
decreasing_by
  exact C.children_lt i j.1 j.2

/-- Variables mentioned at or below position `i`, by the same recursion. -/
def support [DecidableEq Var] (C : Circuit Var) (i : Fin C.size) :
    Finset Var :=
  (C.node i).supportLocal fun j ↦ C.support j.1
termination_by i.val
decreasing_by
  exact C.children_lt i j.1 j.2

/-- `C` computes the Boolean function `f`: at every assignment `v`, the
output node has the value `f v`. -/
def Computes (C : Circuit Var) (f : (Var → Bool) → Bool) : Prop :=
  ∀ v, C.eval v C.output = f v

/-- Decomposable: distinct children of every conjunction mention disjoint
sets of variables. -/
def IsDecomposable [DecidableEq Var] (C : Circuit Var) : Prop :=
  ∀ i children, C.node i = .and children →
    ∀ left ∈ children, ∀ right ∈ children, left ≠ right →
      Disjoint (C.support left) (C.support right)

/-- Deterministic: two distinct children of a disjunction are never true
at the same time. -/
def IsDeterministic (C : Circuit Var) : Prop :=
  ∀ i children, C.node i = .or children →
    ∀ left ∈ children, ∀ right ∈ children, left ≠ right →
      ∀ v, (C.eval v left && C.eval v right) = false

def IsDNNF [DecidableEq Var] (C : Circuit Var) : Prop :=
  C.IsDecomposable

def IsDeterministicDNNF [DecidableEq Var] (C : Circuit Var) : Prop :=
  C.IsDecomposable ∧ C.IsDeterministic

end Circuit

/-- The claim.  For every exponent `d` and factor `M` there is a
deterministic DNNF `C` over the variables `ℕ` such that every DNNF `D`
computing the negation of `C` has more than `M * C.size ^ d` nodes. -/
def NotClosedUnderNegation : Prop :=
  ∀ d M : ℕ,
    ∃ C : Circuit ℕ, C.IsDeterministicDNNF ∧
      ∀ D : Circuit ℕ, D.IsDNNF →
        D.Computes (fun v ↦ !C.eval v C.output) →
          M * C.size ^ d < D.size

end DDNNFNegation
