import DDNNFNegation.Encoder
import DDNNFNegation.OuterDNF
import DDNNFNegation.OBDD
import DDNNFNegation.CircuitOperations
import DDNNFNegation.Prune
import TutorialBox

/-!
# A small d-DNNF for the encoded function

For any encoder, each outer term can be evaluated by a layered decision
diagram whose states record partial sums. The width bound on eligible
terms bounds these diagrams. Translating them to d-DNNFs and joining
them by one deterministic OR gives a small circuit for the same encoded
function used in the lower-bound argument.
-/

namespace DDNNFNegation

open Finset

noncomputable section

/-- Coordinates inspected by one signed outer term. -/
def encodedTermSupport {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n) : Finset (Fin n × Fin n) :=
  (termSigned ranks hn T).positive ∪
    (termSigned ranks hn T).negative

/-- The number of inspected coordinates is at most the number of signed literals. -/
theorem card_encodedTermSupport_le {n w : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T : ThresholdTerm n)
    (hwidth : (termSigned ranks hn T).positive.card +
      (termSigned ranks hn T).negative.card ≤ w) :
    (encodedTermSupport ranks hn T).card ≤ w := by
  exact (Finset.card_union_le _ _).trans hwidth

/-- Restrict every encoder column to the coordinates inspected by `T`. -/
def encodedTermColumns
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {iota : Type*} [Fintype iota]
    (a : iota → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    iota → (encodedTermSupport ranks hn T → GadgetVector) :=
  fun i u ↦ a i u

/-- State reached after reading a complete Boolean assignment.  The same
subset-sum update gives the state at every intermediate OBDD layer. -/
def encodedTermState
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {iota : Type*} [Fintype iota]
    (a : iota → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) (x : iota → Bool) :
    encodedTermSupport ranks hn T → GadgetVector :=
  subsetSum (encodedTermColumns ranks hn a T) x

/-- Reading one coordinate of the stored state gives the corresponding restricted encoder
sum. -/
theorem encodedTermState_apply
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {iota : Type*} [Fintype iota]
    (a : iota → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) (x : iota → Bool)
    (u : encodedTermSupport ranks hn T) :
  encodedTermState ranks hn a T x u = subsetSum a x u := by
  unfold encodedTermState DDNNFNegation.subsetSum
  simp only [Fintype.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x i = true
  · simp [hxi, encodedTermColumns]
  · simp [hxi]

/-- The exact number of states used by one term machine. -/
theorem card_encodedTermState
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n) :
    Fintype.card (encodedTermSupport ranks hn T → GadgetVector) =
      16 ^ (encodedTermSupport ranks hn T).card := by
  rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, gadget_card]

/-- A state supplies gadget values on the signed support.  Values outside
the support are irrelevant and are set to false. -/
def encodedTermStateValuation
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n)
    (s : encodedTermSupport ranks hn T → GadgetVector) :
    (Fin n × Fin n) → Prop :=
  fun u ↦ if hu : u ∈ encodedTermSupport ranks hn T then
    quadForm (s ⟨u, hu⟩) = 1
  else False

/-- Acceptance predicate of the finite-state machine for one outer term. -/
def encodedTermStateAccepts
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n)
    (s : encodedTermSupport ranks hn T → GadgetVector) : Prop :=
  (termSigned ranks hn T).Satisfied
    (encodedTermStateValuation ranks hn T s)

/-- The restricted final state accepts exactly when the original signed term
is satisfied by the full encoded partial-sum vector. -/
theorem encodedTermStateAccepts_iff
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {iota : Type*} [Fintype iota]
    (a : iota → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) (x : iota → Bool) :
    encodedTermStateAccepts ranks hn T (encodedTermState ranks hn a T x) ↔
      (termSigned ranks hn T).Satisfied
        (gadgetBits (subsetSum a x)) := by
  constructor
  · rintro ⟨hpos, hneg⟩
    constructor
    · intro u hu
      have husupport : u ∈ encodedTermSupport ranks hn T :=
        Finset.mem_union_left _ hu
      simpa [encodedTermStateAccepts, encodedTermStateValuation,
        gadgetBits, husupport, encodedTermState_apply] using hpos u hu
    · intro u hu
      have husupport : u ∈ encodedTermSupport ranks hn T :=
        Finset.mem_union_right _ hu
      simpa [encodedTermStateAccepts, encodedTermStateValuation,
        gadgetBits, husupport, encodedTermState_apply] using hneg u hu
  · rintro ⟨hpos, hneg⟩
    constructor
    · intro u hu
      have husupport : u ∈ encodedTermSupport ranks hn T :=
        Finset.mem_union_left _ hu
      simpa [encodedTermStateValuation, gadgetBits, husupport,
        encodedTermState_apply] using hpos u hu
    · intro u hu
      have husupport : u ∈ encodedTermSupport ranks hn T :=
        Finset.mem_union_right _ hu
      simpa [encodedTermStateValuation, gadgetBits, husupport,
        encodedTermState_apply] using hneg u hu

/-- The encoded outer function is the disjunction of the finite-state term
machines. -/
theorem hardFunction_iff_exists_termStateAccepts
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {iota : Type*} [Fintype iota]
    (a : iota → ((Fin n × Fin n) → GadgetVector))
    (x : iota → Bool) :
    hardFunction ranks hn a x ↔
      ∃ T : ThresholdTerm n,
        encodedTermStateAccepts ranks hn T
          (encodedTermState ranks hn a T x) := by
  unfold hardFunction outerFunction outerDNF
  apply exists_congr
  intro T
  exact (encodedTermStateAccepts_iff ranks hn a T x).symm

/-- Distinct term machines have disjoint accepting assignment sets. -/
theorem encodedTermStates_unambiguous
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {iota : Type*} [Fintype iota]
    (a : iota → ((Fin n × Fin n) → GadgetVector))
    (x : iota → Bool) {T U : ThresholdTerm n}
    (hT : encodedTermStateAccepts ranks hn T
      (encodedTermState ranks hn a T x))
    (hU : encodedTermStateAccepts ranks hn U
      (encodedTermState ranks hn a U x)) :
    T = U := by
  apply thresholdTerms_unambiguous ranks hn (gadgetBits (subsetSum a x))
  · exact (encodedTermStateAccepts_iff ranks hn a T x).mp hT
  · exact (encodedTermStateAccepts_iff ranks hn a U x).mp hU

/-! ## Shared OBDD and d-DNNF syntax -/

/-- Add one input column to the stored restricted partial-sum vector exactly when the
current Boolean bit is true. -/
def encodedTermTransition
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    Fin bitCount →
      (encodedTermSupport ranks hn T → GadgetVector) → Bool →
      (encodedTermSupport ranks hn T → GadgetVector) :=
  fun i state bit ↦
    state + if bit then encodedTermColumns ranks hn a T i else 0

/-- Boolean form of the terminal acceptance predicate. -/
noncomputable def encodedTermAcceptBool
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n)
    (state : encodedTermSupport ranks hn T → GadgetVector) : Bool :=
  @ite Bool (encodedTermStateAccepts ranks hn T state)
    (Classical.propDecidable _) true false

/-- The actual shared layered OBDD for one pulled-back outer term. -/
noncomputable def encodedTermOBDD
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) : ReadOnceOBDD (Fin bitCount) :=
  LayeredOBDD.ofTransition
    (encodedTermTransition ranks hn a T)
    (encodedTermAcceptBool ranks hn T) 0

/-- The shared OBDD has exactly one node for every layer-state pair. -/
theorem encodedTermOBDD_size
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermOBDD ranks hn a T).size =
      (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card := by
  rw [encodedTermOBDD, LayeredOBDD.ofTransition_size,
    card_encodedTermState]

/-- The layered transition system reaches the previously defined restricted
subset-sum state. -/
theorem encodedTermRun_eq_state
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) (x : Fin bitCount → Bool) :
    LayeredOBDD.runFrom (encodedTermTransition ranks hn a T)
        x 0 0 =
      encodedTermState ranks hn a T x := by
  rw [show encodedTermTransition ranks hn a T =
      (fun i state bit ↦
        state + if bit then encodedTermColumns ranks hn a T i else 0) from rfl]
  rw [LayeredOBDD.runFrom_add_at_zero]
  rfl

/-- The shared OBDD recognizes exactly its pulled-back outer term. -/
theorem encodedTermOBDD_computes
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermOBDD ranks hn a T).Computes
      (fun x ↦ encodedTermStateAccepts ranks hn T
        (encodedTermState ranks hn a T x)) := by
  intro x
  change encodedTermAcceptBool ranks hn T
      (LayeredOBDD.runFrom (encodedTermTransition ranks hn a T)
        x 0 0) = true ↔ _
  rw [encodedTermRun_eq_state]
  by_cases haccept : encodedTermStateAccepts ranks hn T
      (encodedTermState ranks hn a T x)
  · simp [encodedTermAcceptBool, haccept]
  · simp [encodedTermAcceptBool, haccept]

/-- The tutorial's term OBDD: correctness and the exact layer-state count.
`encodedTermStateAccepts_iff` identifies its acceptance predicate with the
outer term after substituting the encoded gadget bits. -/
@[tutorial_box "lem:tutorial-term-obdd"]
theorem term_obdd
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermOBDD ranks hn a T).Computes
      (fun x ↦ encodedTermStateAccepts ranks hn T
        (encodedTermState ranks hn a T x)) ∧
    (encodedTermOBDD ranks hn a T).size =
      (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card :=
  ⟨encodedTermOBDD_computes ranks hn a T, encodedTermOBDD_size ranks hn a T⟩

/-- Expanding the shared term OBDD gives a deterministic DNNF for the term. -/
noncomputable def encodedTermDNNF
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) : NNFCircuit (Fin bitCount) :=
  (encodedTermOBDD ranks hn a T).toNNFCircuit

/-- The shared decision-diagram expansion preserves decomposability and determinism. -/
theorem encodedTermDNNF_isDeterministicDNNF
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermDNNF ranks hn a T).IsDeterministicDNNF :=
  (obdd_to_dDNNF (encodedTermOBDD ranks hn a T) _
    (term_obdd ranks hn a T).1).2.1

/-- The expanded term circuit recognizes exactly the pulled-back outer term. -/
theorem encodedTermDNNF_computes
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermDNNF ranks hn a T).Computes
      (fun x ↦ encodedTermStateAccepts ranks hn T
        (encodedTermState ranks hn a T x)) :=
  (obdd_to_dDNNF (encodedTermOBDD ranks hn a T) _
    (term_obdd ranks hn a T).1).1

/-- The term d-DNNF has at most ten edges per OBDD node: the tutorial's
"constant number of edges per decision node". -/
theorem encodedTermDNNF_edgeCount_le
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermDNNF ranks hn a T).edgeCount ≤
      10 * ((bitCount + 1) *
        16 ^ (encodedTermSupport ranks hn T).card) := by
  rw [encodedTermDNNF, ← (term_obdd ranks hn a T).2]
  exact (obdd_to_dDNNF (encodedTermOBDD ranks hn a T) _
    (term_obdd ranks hn a T).1).2.2

/-- The full positive circuit is the shared disjoint union of all term
circuits, with one deterministic OR gate at the top. -/
noncomputable def encodedOuterDNNF
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    NNFCircuit (Fin bitCount) := by
  letI := Classical.decEq (ThresholdTerm n)
  exact NNFCircuit.disjointOr (fun T : ThresholdTerm n ↦
    encodedTermDNNF ranks hn a T)

/-- Lemma "Small d-DNNF", the circuit shape: the positive circuit is a
d-DNNF.  Each term circuit is one, and two distinct term circuits never
accept the same input, because two distinct terms conflict. -/
theorem encodedOuterDNNF_isDeterministicDNNF
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedOuterDNNF ranks hn a).IsDeterministicDNNF := by
  classical
  unfold encodedOuterDNNF
  apply NNFCircuit.disjointOr_isDeterministicDNNF
  · intro T
    exact encodedTermDNNF_isDeterministicDNNF ranks hn a T
  · intro T U hTU x hboth
    have hT := (encodedTermDNNF_computes ranks hn a T x).mp hboth.1
    have hU := (encodedTermDNNF_computes ranks hn a U x).mp hboth.2
    exact hTU (encodedTermStates_unambiguous ranks hn a x hT hU)

/-- Lemma "Small d-DNNF", correctness: the positive circuit computes the
hard function `L_n`. -/
theorem encodedOuterDNNF_computes
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedOuterDNNF ranks hn a).Computes
      (hardFunction ranks hn a) := by
  classical
  unfold encodedOuterDNNF
  intro x
  have hfamily := NNFCircuit.disjointOr_computes
    (fun T : ThresholdTerm n ↦ encodedTermDNNF ranks hn a T)
    (fun T x ↦ encodedTermStateAccepts ranks hn T
      (encodedTermState ranks hn a T x))
    (fun T ↦ encodedTermDNNF_computes ranks hn a T)
  exact (hfamily x).trans
    (hardFunction_iff_exists_termStateAccepts ranks hn a x).symm

/-- Lemma "Small d-DNNF", the size bound.  The edge count of the positive
circuit is counted internally as follows: one edge
per term into the top OR, and at most ten edges per node of each term
OBDD of at most `(bitCount + 1) 16^width` nodes. -/
theorem encodedOuterDNNF_edgeCount_le_of_width
    {n bitCount width : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (hwidth : ∀ T : ThresholdTerm n,
      (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤ width) :
    (encodedOuterDNNF ranks hn a).edgeCount ≤
      Fintype.card (ThresholdTerm n) *
        (1 + 10 * ((bitCount + 1) * 16 ^ width)) := by
  classical
  unfold encodedOuterDNNF
  rw [NNFCircuit.disjointOr_edgeCount]
  calc
    Fintype.card (ThresholdTerm n) +
        ∑ T : ThresholdTerm n, (encodedTermDNNF ranks hn a T).edgeCount ≤
      Fintype.card (ThresholdTerm n) +
        ∑ _T : ThresholdTerm n, 10 * ((bitCount + 1) * 16 ^ width) := by
          apply Nat.add_le_add_left
          apply Finset.sum_le_sum
          intro T _
          refine (encodedTermDNNF_edgeCount_le ranks hn a T).trans ?_
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by norm_num)
            (card_encodedTermSupport_le ranks hn T (hwidth T))
    _ = Fintype.card (ThresholdTerm n) *
        (1 + 10 * ((bitCount + 1) * 16 ^ width)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring

/-- An internal edge bound for the easy side. If every eligible outer term
has at most `width` literals, the encoded function has a d-DNNF with at
most `|terms| * (1 + 10 * (bitCount + 1) * 16^width)` edges. At width
`10*n` and input count `60*n²`, this is `2^{O(n)}`. -/
theorem small_dDNNF
    {n bitCount width : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (hwidth : ∀ T : ThresholdTerm n,
      (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤ width) :
    ∃ C : NNFCircuit.{0, 0} (Fin bitCount),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks hn a) ∧
      C.edgeCount ≤ Fintype.card (ThresholdTerm n) *
        (1 + 10 * ((bitCount + 1) * 16 ^ width)) :=
  ⟨encodedOuterDNNF ranks hn a, encodedOuterDNNF_isDeterministicDNNF ranks hn a,
    encodedOuterDNNF_computes ranks hn a,
    encodedOuterDNNF_edgeCount_le_of_width ranks hn a hwidth⟩

/-- The positive construction in node count, as used in the tutorial.
Deleting unreachable nodes converts the internal edge upper bound into
a node upper bound without changing the function or determinism. -/
@[tutorial_box "lem:tutorial-positive"]
theorem small_dDNNF_nodes
    {n bitCount width : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (hwidth : ∀ T : ThresholdTerm n,
      (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤ width) :
    ∃ C : NNFCircuit.{0, 0} (Fin bitCount),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks hn a) ∧
      C.size ≤ Fintype.card (ThresholdTerm n) *
        (1 + 10 * ((bitCount + 1) * 16 ^ width)) + 1 := by
  obtain ⟨C, hdet, hcomputes, hsize⟩ := small_dDNNF ranks hn a hwidth
  exact ⟨C.prune, C.prune_isDeterministicDNNF hdet, C.prune_computes hcomputes,
    C.prune_size_le.trans
      (Nat.add_le_add_right (C.edgeCount_prune_le.trans hsize) 1)⟩

end

end DDNNFNegation
