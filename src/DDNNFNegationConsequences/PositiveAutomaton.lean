import DDNNFNegation.PositiveSide
import DDNNFNegationConsequences.LayeredAutomaton

/-!
# The positive witness as an unambiguous automaton and grammar

Each outer term already has a finite layered transition system in
`PositiveSide`.  Here it is read as a partial deterministic automaton.  A
fresh start state unions the term automata.  Outer-term unambiguity proves
that this union has at most one accepting run, and the generic right-linear
translation then gives an unambiguous grammar for the same fixed-length
language.
-/

namespace DDNNFNegation

open Finset

noncomputable section

local instance {n : ℕ} : DecidableEq (ThresholdTerm n) :=
  Classical.decEq _

/-- Layer and restricted partial-sum vector for one outer term machine. -/
abbrev EncodedTermAutomatonState
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n) :=
  LayeredOBDD.Gate bitCount
    (encodedTermSupport ranks hn T → GadgetVector)

/-- The layered OBDD transition system, viewed as an ordinary partial DFA. -/
def encodedTermAutomaton
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    FiniteWordAutomaton
      (EncodedTermAutomatonState (bitCount := bitCount) ranks hn T) Bool :=
  LayeredOBDD.toFiniteWordAutomaton
    (encodedTermTransition ranks hn a T)
    (encodedTermAcceptBool ranks hn T) 0

/-- On a complete Boolean word, the term automaton recognizes exactly the
pulled-back outer term. -/
theorem encodedTermAutomaton_accepts_iff
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) (x : Fin bitCount → Bool) :
    (encodedTermAutomaton ranks hn a T).ExistentialAccepts (List.ofFn x) ↔
      encodedTermStateAccepts ranks hn T
        (encodedTermState ranks hn a T x) := by
  rw [encodedTermAutomaton,
    LayeredOBDD.toFiniteWordAutomaton_accepts_iff,
    encodedTermRun_eq_state]
  by_cases haccepts : encodedTermStateAccepts ranks hn T
      (encodedTermState ranks hn a T x)
  · simp [encodedTermAcceptBool, haccepts]
  · simp [encodedTermAcceptBool, haccepts]

theorem encodedTermAutomaton_isUnambiguous
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (T : ThresholdTerm n) :
    (encodedTermAutomaton ranks hn a T).IsUnambiguous :=
  LayeredOBDD.toFiniteWordAutomaton_isUnambiguous
    (encodedTermTransition ranks hn a T)
    (encodedTermAcceptBool ranks hn T) 0

/-- The finite dependent family of all term automata. -/
def encodedTermAutomatonFamily
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    FiniteAutomatonFamily (ThresholdTerm n) where
  State T := EncodedTermAutomatonState ranks hn T
  stateFintype _ := inferInstance
  stateDecidableEq _ := Classical.decEq _
  automaton T := encodedTermAutomaton ranks hn a T

/-- The positive automaton chooses a term on the first letter and thereafter
follows that term's unique layered run. -/
def encodedOuterAutomaton
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) := by
  letI := Classical.decEq (ThresholdTerm n)
  exact (encodedTermAutomatonFamily ranks hn a).unionAutomaton

@[instance_reducible] noncomputable def encodedOuterAutomatonDecidableEq
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    DecidableEq (encodedTermAutomatonFamily ranks hn a).UnionState :=
  Classical.decEq _

theorem encodedTermAutomatonState_card
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : ThresholdTerm n) :
    Fintype.card
        (EncodedTermAutomatonState (bitCount := bitCount) ranks hn T) =
      (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card := by
  simp [EncodedTermAutomatonState, LayeredOBDD.Gate, LayeredOBDD.Layer,
    Fintype.card_pi]

/-- Exact state count of the union automaton. -/
theorem encodedOuterAutomaton_state_card
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState =
      1 + ∑ T : ThresholdTerm n,
        (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card := by
  change Fintype.card (Unit ⊕ Sigma fun T : ThresholdTerm n ↦
    EncodedTermAutomatonState (bitCount := bitCount) ranks hn T) = _
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma]
  simp_rw [encodedTermAutomatonState_card]

theorem encodedOuterAutomaton_state_card_le_of_width
    {n bitCount width : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (hwidth : ∀ T : ThresholdTerm n,
      (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤ width) :
    Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState ≤
      1 + Fintype.card (ThresholdTerm n) *
        ((bitCount + 1) * 16 ^ width) := by
  rw [encodedOuterAutomaton_state_card]
  apply Nat.add_le_add_left
  calc
    ∑ T : ThresholdTerm n,
        (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card ≤
      ∑ _T : ThresholdTerm n, (bitCount + 1) * 16 ^ width := by
        apply Finset.sum_le_sum
        intro T hT
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by norm_num)
          (card_encodedTermSupport_le ranks hn T (hwidth T))
    _ = Fintype.card (ThresholdTerm n) *
        ((bitCount + 1) * 16 ^ width) := by simp

private theorem word_eq_ofFn_getVector {N : ℕ} (word : List Bool)
    (hlength : word.length = N) :
    let vector : List.Vector Bool N := ⟨word, hlength⟩
    List.ofFn vector.get = word := by
  intro vector
  have hvector := congrArg List.Vector.toList
    (List.Vector.ofFn_get vector)
  calc
    List.ofFn vector.get = vector.toList := by
      simpa only [List.Vector.toList_ofFn] using hvector
    _ = word := rfl

theorem encodedTermAutomatonFamily_hasDisjointLanguages
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedTermAutomatonFamily ranks hn a).HasDisjointLanguages := by
  intro T U word hT hU
  have hlength : word.length = bitCount :=
    LayeredOBDD.toFiniteWordAutomaton_accepts_length
      (encodedTermTransition ranks hn a T)
      (encodedTermAcceptBool ranks hn T) 0 hT
  let vector : List.Vector Bool bitCount := ⟨word, hlength⟩
  let x : Fin bitCount → Bool := vector.get
  have hword : List.ofFn x = word := by
    exact word_eq_ofFn_getVector word hlength
  have hT' : encodedTermStateAccepts ranks hn T
      (encodedTermState ranks hn a T x) :=
    (encodedTermAutomaton_accepts_iff ranks hn a T x).mp (by
      rw [hword]
      exact hT)
  have hU' : encodedTermStateAccepts ranks hn U
      (encodedTermState ranks hn a U x) :=
    (encodedTermAutomaton_accepts_iff ranks hn a U x).mp (by
      rw [hword]
      exact hU)
  exact encodedTermStates_unambiguous ranks hn a x hT' hU'

theorem encodedOuterAutomaton_isUnambiguous
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedOuterAutomaton ranks hn a).IsUnambiguous := by
  classical
  unfold encodedOuterAutomaton
  apply FiniteAutomatonFamily.unionAutomaton_isUnambiguous
  · exact fun T ↦ encodedTermAutomaton_isUnambiguous ranks hn a T
  · exact encodedTermAutomatonFamily_hasDisjointLanguages ranks hn a

theorem encodedOuterAutomaton_accepts_iff
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (x : Fin bitCount → Bool) :
    (encodedOuterAutomaton ranks hn a).ExistentialAccepts (List.ofFn x) ↔
      hardFunction ranks hn a x := by
  classical
  unfold encodedOuterAutomaton
  rw [FiniteAutomatonFamily.unionAutomaton_accepts_iff]
  calc
    (∃ T, (encodedTermAutomaton ranks hn a T).ExistentialAccepts
        (List.ofFn x)) ↔
        ∃ T, encodedTermStateAccepts ranks hn T
          (encodedTermState ranks hn a T x) := by
            apply exists_congr
            intro T
            exact encodedTermAutomaton_accepts_iff ranks hn a T x
    _ ↔ hardFunction ranks hn a x :=
      (hardFunction_iff_exists_termStateAccepts ranks hn a x).symm

theorem encodedOuterAutomaton_accepts_length
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    {word : List Bool}
    (haccepts : (encodedOuterAutomaton ranks hn a).ExistentialAccepts word) :
    word.length = bitCount := by
  classical
  unfold encodedOuterAutomaton at haccepts
  rw [FiniteAutomatonFamily.unionAutomaton_accepts_iff] at haccepts
  obtain ⟨T, hT⟩ := haccepts
  exact LayeredOBDD.toFiniteWordAutomaton_accepts_length
    (encodedTermTransition ranks hn a T)
    (encodedTermAcceptBool ranks hn T) 0 hT

/-- The direct conventional right-linear grammar for the positive
fixed-length language. -/
def encodedOuterRightLinearCFG
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) := by
  classical
  exact (encodedOuterAutomaton ranks hn a).toRightLinearCFG

@[instance_reducible] noncomputable def encodedOuterRightLinearFintype
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    Fintype (encodedOuterRightLinearCFG ranks hn a).NT := by
  change Fintype (encodedTermAutomatonFamily ranks hn a).UnionState
  infer_instance

/-- Syntactic parse trees of the direct positive grammar, with the state
instances fixed explicitly. -/
noncomputable def encodedOuterRightLinearParse
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (word : List Bool) : Type := by
  classical
  exact (encodedOuterAutomaton ranks hn a).DirectRightLinearParse word

/-- The direct right-linear grammar has exactly one nonterminal for every
state of the union automaton. -/
theorem encodedOuterRightLinear_nonterminal_card
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    @Fintype.card (encodedOuterRightLinearCFG ranks hn a).NT
        (encodedOuterRightLinearFintype ranks hn a) =
      1 + ∑ T : ThresholdTerm n,
        (bitCount + 1) * 16 ^ (encodedTermSupport ranks hn T).card := by
  change Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState = _
  exact encodedOuterAutomaton_state_card ranks hn a

/-- The direct right-linear grammar has at most `S + 2 * S * S` rules,
where `S` is the number of states of the positive automaton. -/
theorem encodedOuterRightLinear_rule_card_le
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedOuterRightLinearCFG ranks hn a).rules.card ≤
      Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState +
        2 * Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState *
          Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState := by
  classical
  unfold encodedOuterRightLinearCFG
  exact (encodedOuterAutomaton ranks hn a).toRightLinearCFG_rule_card_le_state_sq

theorem encodedOuterRightLinearCFG_language_iff
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (x : Fin bitCount → Bool) :
    List.ofFn x ∈ (encodedOuterRightLinearCFG ranks hn a).language ↔
      hardFunction ranks hn a x := by
  classical
  unfold encodedOuterRightLinearCFG
  rw [FiniteWordAutomaton.mem_directRightLinear_language_iff_accepts]
  exact encodedOuterAutomaton_accepts_iff ranks hn a x

/-- On words of every length, the direct right-linear grammar and the
positive automaton recognize the same language. -/
theorem encodedOuterRightLinearCFG_language_iff_accepts
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (word : List Bool) :
    word ∈ (encodedOuterRightLinearCFG ranks hn a).language ↔
      (encodedOuterAutomaton ranks hn a).ExistentialAccepts word := by
  classical
  unfold encodedOuterRightLinearCFG
  exact (encodedOuterAutomaton ranks hn a)
    |>.mem_directRightLinear_language_iff_accepts word

private theorem boolWordsOfFixedLength_finite (bitCount : ℕ) :
    {word : List Bool | word.length = bitCount}.Finite := by
  have hr : (Set.range (@List.Vector.toList Bool bitCount)).Finite :=
    Set.finite_range _
  apply hr.subset
  intro word hlength
  exact ⟨⟨word, hlength⟩, rfl⟩

/-- The positive right-linear grammar recognizes a finite language: every
accepted word has exactly the Boolean assignment length. -/
theorem encodedOuterRightLinearCFG_language_finite
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedOuterRightLinearCFG ranks hn a).language.Finite := by
  apply (boolWordsOfFixedLength_finite bitCount).subset
  intro word hword
  exact encodedOuterAutomaton_accepts_length ranks hn a
    ((encodedOuterRightLinearCFG_language_iff_accepts
      ranks hn a word).mp hword)

theorem encodedOuterRightLinearCFG_parse_exists_iff
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (word : List Bool) :
    Nonempty (encodedOuterRightLinearParse ranks hn a word) ↔
      word ∈ (encodedOuterRightLinearCFG ranks hn a).language := by
  classical
  unfold encodedOuterRightLinearParse encodedOuterRightLinearCFG
  exact (encodedOuterAutomaton ranks hn a).directGrammar_parse_exists_iff_mem_language word

/-- Every word has at most one syntactic parse tree in the positive
right-linear grammar. -/
theorem encodedOuterRightLinearCFG_parse_subsingleton
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector))
    (word : List Bool) :
    Subsingleton (encodedOuterRightLinearParse ranks hn a word) := by
  unfold encodedOuterRightLinearParse
  exact (encodedOuterAutomaton ranks hn a).directGrammar_parse_subsingleton
    (encodedOuterAutomaton_isUnambiguous ranks hn a) word

end

end DDNNFNegation
