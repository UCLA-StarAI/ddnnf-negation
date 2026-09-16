import DDNNFNegation.Prune
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Arithmetic circuits and Boolean support

The circuit model allows variables, real constants, addition, and
multiplication. `IsMonotone` requires nonnegative constants. For circuits
on paired assignment variables whose products use disjoint positions,
replacing arithmetic operations by Boolean operations gives a DNNF for
positivity, with the same number of nodes. Separate lemmas establish
semantics, decomposability, and size.
-/

namespace DDNNFNegation

open MvPolynomial

/-- One gate of an arithmetic circuit: a real constant, an indeterminate, a
sum, or a product. -/
inductive ArithNode (V Gate : Type*) where
  | const (c : ℝ)
  | var (x : V)
  | add (left right : Gate)
  | mul (left right : Gate)

namespace ArithNode

variable {V Gate : Type*}

/-- The polynomial at a gate, given the polynomials of its children. -/
noncomputable def eval (child : Gate → MvPolynomial V ℝ) :
    ArithNode V Gate → MvPolynomial V ℝ
  | const c => C c
  | var x => X x
  | add left right => child left + child right
  | mul left right => child left * child right

/-- The indeterminates occurring below a gate, given those of its children. -/
def Vars [DecidableEq V] (child : Gate → Finset V) :
    ArithNode V Gate → Finset V
  | const _ => ∅
  | var x => {x}
  | add left right => child left ∪ child right
  | mul left right => child left ∪ child right

/-- The child relation of a node. -/
def IsChild (child : Gate) : ArithNode V Gate → Prop
  | add left right => child = left ∨ child = right
  | mul left right => child = left ∨ child = right
  | _ => False

/-- Number of incoming edges. -/
def fanIn : ArithNode V Gate → ℕ
  | .add _ _ | .mul _ _ => 2
  | _ => 0

/-- Rename the children. -/
def map {Gate' : Type*} (f : Gate → Gate') : ArithNode V Gate → ArithNode V Gate'
  | .const c => .const c
  | .var x => .var x
  | .add l r => .add (f l) (f r)
  | .mul l r => .mul (f l) (f r)

end ArithNode

/-- A finite shared arithmetic circuit over the indeterminates `V`, with real
coefficients.  `poly` is the polynomial computed at every gate and `vars` the
set of indeterminates occurring below it; both are pinned down by their local
equations. -/
structure ArithCircuit (V : Type*) [DecidableEq V] where
  Gate : Type*
  gateFintype : Fintype Gate
  gateDecidableEq : DecidableEq Gate
  output : Gate
  node : Gate → ArithNode V Gate
  rank : Gate → ℕ
  child_rank : ∀ gate child,
    (node gate).IsChild child → rank child < rank gate
  poly : Gate → MvPolynomial V ℝ
  poly_eq : ∀ gate, poly gate = (node gate).eval poly
  vars : Gate → Finset V
  vars_eq : ∀ gate, vars gate = (node gate).Vars vars

namespace ArithCircuit

variable {V : Type*} [DecidableEq V]

instance (C : ArithCircuit V) : Fintype C.Gate := C.gateFintype

instance (C : ArithCircuit V) : DecidableEq C.Gate := C.gateDecidableEq

/-- Number of gates. -/
def nodeCount (C : ArithCircuit V) : ℕ :=
  Fintype.card C.Gate

/-- Circuit size counts incoming edges and one output wire. -/
def size (C : ArithCircuit V) : ℕ := (∑ g, (C.node g).fanIn) + 1

/-- Binary arithmetic gates contribute at most two edges each. -/
theorem size_le (C : ArithCircuit V) : C.size ≤ 2 * C.nodeCount + 1 := by
  unfold size nodeCount
  have h : (∑ g, (C.node g).fanIn) ≤ ∑ _g : C.Gate, 2 := by
    apply Finset.sum_le_sum
    intro g _
    cases C.node g <;> simp [ArithNode.fanIn]
  simpa [mul_comm] using Nat.add_le_add_right h 1

/-- The polynomial computed at the output gate. -/
def Computes (C : ArithCircuit V) (p : MvPolynomial V ℝ) : Prop :=
  C.poly C.output = p

/-- Every constant is nonnegative: variables, nonnegative constants, addition
and multiplication. -/
def IsMonotone (C : ArithCircuit V) : Prop :=
  ∀ gate c, C.node gate = .const c → 0 ≤ c

/-- Syntactic multilinearity: the two factors of every product use disjoint
sets of indeterminates. -/
def IsSyntacticallyMultilinear (C : ArithCircuit V) : Prop :=
  ∀ gate left right, C.node gate = .mul left right →
    Disjoint (C.vars left) (C.vars right)

/-- Strong induction along the child relation. -/
theorem induction_rank (C : ArithCircuit V) {P : C.Gate → Prop}
    (h : ∀ gate, (∀ child, (C.node gate).IsChild child → P child) → P gate) :
    ∀ gate, P gate := by
  intro gate
  induction' hr : C.rank gate using Nat.strong_induction_on with r ih generalizing gate
  exact h gate fun child hchild ↦ ih _ (hr ▸ C.child_rank gate child hchild) child rfl

/-- Every gate of a monotone circuit has nonnegative coefficients. -/
theorem coeff_nonneg (C : ArithCircuit V) (hmono : C.IsMonotone) :
    ∀ gate m, 0 ≤ coeff m (C.poly gate) := by
  refine C.induction_rank (P := fun gate ↦ ∀ m, 0 ≤ coeff m (C.poly gate)) ?_
  intro gate ih m
  rw [C.poly_eq]
  cases hnode : C.node gate with
  | const c =>
      simp only [ArithNode.eval, coeff_C]
      split_ifs
      · exact hmono gate c hnode
      · exact le_rfl
  | var x =>
      simp only [ArithNode.eval, coeff_X]
      split_ifs <;> norm_num
  | add left right =>
      simp only [ArithNode.eval, coeff_add]
      exact add_nonneg (ih left (by rw [hnode]; exact Or.inl rfl) m)
        (ih right (by rw [hnode]; exact Or.inr rfl) m)
  | mul left right =>
      simp only [ArithNode.eval, coeff_mul]
      exact Finset.sum_nonneg fun x _ ↦
        mul_nonneg (ih left (by rw [hnode]; exact Or.inl rfl) x.1)
          (ih right (by rw [hnode]; exact Or.inr rfl) x.2)

/-- Every gate of a monotone circuit is nonnegative at a nonnegative point. -/
theorem eval_nonneg (C : ArithCircuit V) (hmono : C.IsMonotone)
    (pt : V → ℝ) (hpt : ∀ x, 0 ≤ pt x) :
    ∀ gate, 0 ≤ MvPolynomial.eval pt (C.poly gate) := by
  refine C.induction_rank (P := fun gate ↦ 0 ≤ MvPolynomial.eval pt (C.poly gate)) ?_
  intro gate ih
  rw [C.poly_eq]
  cases hnode : C.node gate with
  | const c =>
      simp only [ArithNode.eval, eval_C]
      exact hmono gate c hnode
  | var x =>
      simp only [ArithNode.eval, eval_X]
      exact hpt x
  | add left right =>
      simp only [ArithNode.eval, map_add]
      exact add_nonneg (ih left (by rw [hnode]; exact Or.inl rfl))
        (ih right (by rw [hnode]; exact Or.inr rfl))
  | mul left right =>
      simp only [ArithNode.eval, map_mul]
      exact mul_nonneg (ih left (by rw [hnode]; exact Or.inl rfl))
        (ih right (by rw [hnode]; exact Or.inr rfl))

end ArithCircuit

/-! ## The paired encoding -/

section paired

variable {N : ℕ}

/-- The monomial `m_a = ∏_i X_{i, a i}` of a Boolean assignment: the
indicator `X_i` where `a i` is true and `X̄_i` where it is false. -/
noncomputable def assignmentMonomial (a : Fin N → Bool) :
    MvPolynomial (Fin N × Bool) ℝ :=
  ∏ i, X (i, a i)

/-- The exponent vector of `assignmentMonomial a`. -/
noncomputable def assignmentExponent (a : Fin N → Bool) : (Fin N × Bool) →₀ ℕ :=
  ∑ i, Finsupp.single (i, a i) 1

theorem assignmentMonomial_eq_monomial (a : Fin N → Bool) :
    assignmentMonomial a = monomial (assignmentExponent a) 1 := by
  rw [assignmentExponent, monomial_sum_one]
  rfl

theorem assignmentExponent_apply (a : Fin N → Bool) (i : Fin N) (b : Bool) :
    assignmentExponent a (i, b) = if a i = b then 1 else 0 := by
  unfold assignmentExponent
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single i]
  · by_cases h : a i = b <;> simp [h]
  · intro j _ hj
    simp [hj]
  · simp

theorem assignmentExponent_injective :
    Function.Injective (assignmentExponent (N := N)) := by
  intro a b hab
  funext i
  have h := congrArg (fun m ↦ m (i, a i)) hab
  simp only [assignmentExponent_apply, if_true] at h
  by_contra hne
  rw [if_neg (Ne.symm hne)] at h
  exact one_ne_zero h

/-- The point `X_i = a_i`, `X̄_i = 1 - a_i` of a Boolean assignment. -/
def boolPoint (a : Fin N → Bool) : Fin N × Bool → ℝ :=
  fun v ↦ if a v.1 = v.2 then 1 else 0

theorem boolPoint_nonneg (a : Fin N → Bool) (v : Fin N × Bool) :
    0 ≤ boolPoint a v := by
  unfold boolPoint
  split_ifs <;> norm_num

/-- `m_a` is `1` at the point of `a` and `0` at every other Boolean point. -/
theorem eval_boolPoint_assignmentMonomial (x a : Fin N → Bool) :
    MvPolynomial.eval (boolPoint x) (assignmentMonomial a) =
      if a = x then 1 else 0 := by
  unfold assignmentMonomial
  rw [map_prod]
  simp only [eval_X, boolPoint]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, eq_iff_iff]
  constructor
  · intro h
    funext i
    exact (h i).symm
  · intro h i
    rw [h]

/-- The positions touched by a set of paired indeterminates. -/
def positions (s : Finset (Fin N × Bool)) : Finset (Fin N) :=
  s.image Prod.fst

theorem positions_union (s t : Finset (Fin N × Bool)) :
    positions (s ∪ t) = positions s ∪ positions t :=
  Finset.image_union _ _

theorem positions_empty : positions (∅ : Finset (Fin N × Bool)) = ∅ :=
  Finset.image_empty _

theorem positions_singleton (v : Fin N × Bool) : positions {v} = {v.1} :=
  Finset.image_singleton _ _

namespace ArithCircuit

variable (C : ArithCircuit (Fin N × Bool))

/-- The two factors of every product touch disjoint sets of positions: the
disjointness required of a syntactically set-multilinear circuit, and of the
nonnegative sum/product circuits in the lower bound. -/
def IsPairDisjoint : Prop :=
  ∀ gate left right, C.node gate = .mul left right →
    Disjoint (positions (C.vars left)) (positions (C.vars right))

/-- Syntactically set-multilinear: every sum combines equal position sets and
every product combines disjoint ones. -/
def IsSetMultilinear : Prop :=
  C.IsPairDisjoint ∧
    ∀ gate left right, C.node gate = .add left right →
      positions (C.vars left) = positions (C.vars right)

/-- A right-linear tree in the variable order `order`: every product
multiplies a single indeterminate by a circuit on positions later in the
order. -/
def IsRightLinear (order : Fin N → ℕ) : Prop :=
  ∀ gate left right, C.node gate = .mul left right →
    ∃ i b, C.node left = .var (i, b) ∧
      ∀ j ∈ positions (C.vars right), order i < order j

/-- The value of the output at the point `X_i = a_i, X̄_i = 1 - a_i`. -/
noncomputable def boolValue (a : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (boolPoint a) (C.poly C.output)

/-! ### The support translation -/

/-- The Boolean node of an arithmetic node: a positive constant is true and a
zero constant false, the indicators are the two literals of their position, a
sum is an OR and a product an AND. -/
noncomputable def translateNode {Gate : Type*} :
    ArithNode (Fin N × Bool) Gate → NNFNode (Fin N) Gate
  | .const c => if 0 < c then .top else .bot
  | .var (i, b) => if b then .pos i else .neg i
  | .add left right => .disj [left, right]
  | .mul left right => .conj left right

theorem translateNode_isChild {Gate : Type*}
    (node : ArithNode (Fin N × Bool) Gate) (child : Gate)
    (h : (translateNode node).IsChild child) : node.IsChild child := by
  cases node with
  | const c =>
      simp only [translateNode] at h
      split_ifs at h <;> simp [NNFNode.IsChild] at h
  | var x =>
      obtain ⟨i, b⟩ := x
      simp only [translateNode] at h
      cases b <;> simp [NNFNode.IsChild] at h
  | add left right =>
      simp only [translateNode, NNFNode.IsChild, List.mem_cons,
        List.not_mem_nil, or_false] at h
      exact h
  | mul left right =>
      exact h

theorem pos_add_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 < p + q ↔ 0 < p ∨ 0 < q := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    linarith [hc.1, hc.2]
  · rintro (h | h) <;> linarith

theorem pos_mul_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (_hq : 0 ≤ q) :
    0 < p * q ↔ 0 < p ∧ 0 < q := by
  constructor
  · intro h
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h' | h'
    · exact h'
    · exact absurd h'.1 (not_lt.mpr hp)
  · rintro ⟨h1, h2⟩
    exact mul_pos h1 h2

/-- The DNNF read off a monotone circuit with disjoint positions at
products: the same gates, a gate true at a Boolean point exactly when its
polynomial is positive there. -/
noncomputable def toDNNF (hmono : C.IsMonotone) : NNFCircuit (Fin N) where
  Gate := C.Gate
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := C.output
  node := fun gate ↦ translateNode (C.node gate)
  rank := C.rank
  child_rank := fun gate child h ↦
    C.child_rank gate child (translateNode_isChild _ _ h)
  semantics := fun gate x ↦ 0 < MvPolynomial.eval (boolPoint x) (C.poly gate)
  semantics_eq := by
    intro gate x
    have hnn := C.eval_nonneg hmono (boolPoint x) (boolPoint_nonneg x)
    rw [C.poly_eq]
    cases hnode : C.node gate with
    | const c =>
        simp only [ArithNode.eval, eval_C, translateNode]
        split_ifs with h <;> simp [NNFNode.Holds, h]
    | var v =>
        obtain ⟨i, b⟩ := v
        simp only [ArithNode.eval, eval_X, translateNode, boolPoint]
        cases b <;> cases hx : x i <;> simp [NNFNode.Holds, hx]
    | add left right =>
        simp only [ArithNode.eval, map_add, translateNode, NNFNode.Holds,
          List.mem_cons, List.not_mem_nil, or_false,
          exists_eq_or_imp, exists_eq_left]
        exact pos_add_iff_of_nonneg (hnn left) (hnn right)
    | mul left right =>
        simp only [ArithNode.eval, map_mul, translateNode, NNFNode.Holds]
        exact pos_mul_iff_of_nonneg (hnn left) (hnn right)
  support := fun gate ↦ positions (C.vars gate)
  support_eq := by
    intro gate
    rw [C.vars_eq]
    cases hnode : C.node gate with
    | const c =>
        simp only [ArithNode.Vars, translateNode, positions_empty]
        split_ifs <;> rfl
    | var v =>
        obtain ⟨i, b⟩ := v
        simp only [ArithNode.Vars, translateNode, positions_singleton]
        cases b <;> rfl
    | add left right =>
        simp only [ArithNode.Vars, translateNode, NNFNode.Support, List.foldl,
          positions_union, Finset.empty_union]
    | mul left right =>
        simp only [ArithNode.Vars, translateNode, NNFNode.Support,
          positions_union]

@[simp] theorem toDNNF_nodeCount (hmono : C.IsMonotone) :
    (C.toDNNF hmono).nodeCount = C.nodeCount := rfl

theorem toDNNF_isDNNF (hmono : C.IsMonotone) (hdisj : C.IsPairDisjoint) :
    (C.toDNNF hmono).IsDNNF := by
  intro gate left right h
  change translateNode (C.node gate) = .conj left right at h
  cases hnode : C.node gate with
  | const c =>
      rw [hnode] at h
      simp only [translateNode] at h
      split_ifs at h
  | var v =>
      obtain ⟨i, b⟩ := v
      rw [hnode] at h
      cases b <;> simp [translateNode] at h
  | add l r =>
      rw [hnode] at h
      cases h
  | mul l r =>
      rw [hnode] at h
      cases h
      exact hdisj gate left right hnode

/-- The translation computes the support of the output on the Boolean
points. -/
theorem toDNNF_computes (hmono : C.IsMonotone) (f : (Fin N → Bool) → Prop)
    (h : ∀ x, 0 < C.boolValue x ↔ f x) :
    (C.toDNNF hmono).Computes f :=
  h

end ArithCircuit

end paired

end DDNNFNegation
