import DDNNFNegationConsequences.CFGLowerBound
import DDNNFNegationConsequences.PositiveAutomaton
import DDNNFNegationConsequences.WidthWitness

/-!
# The fixed-length unambiguous-grammar separation

This file packages the two directions of the bounded-language consequence
for one and the same encoded function.  Its positive length slice has a
small conventional right-linear grammar with at most one canonical parse per
word.  Here a parse tree retains the grammar production used at every node.
Every finite CFG for the opposite slice satisfies the explicit parser
lower bound inherited from the DNNF separation.
-/

namespace DDNNFNegation

open CFGBinarization
open Filter

noncomputable section

/-- Explicit state and nonterminal bound for the positive automaton and its
direct right-linear grammar. -/
abbrev candidatePositiveGrammarStateBound (n : ℕ) : ℕ :=
  1 + (n * 2 ^ n) *
    ((encodedInputCount n + 1) * 16 ^ (10 * n))

/-- A state-only upper bound on the number of rules in the direct positive
right-linear grammar. -/
abbrev candidatePositiveGrammarRuleBound (n : ℕ) : ℕ :=
  candidatePositiveGrammarStateBound n +
    2 * candidatePositiveGrammarStateBound n *
      candidatePositiveGrammarStateBound n

/-- Bound in the same source-grammar parameter used by the hard-side parser
translation. -/
abbrev candidatePositiveGrammarDescriptionBound (n : ℕ) : ℕ :=
  candidatePositiveGrammarStateBound n +
    2 * candidatePositiveGrammarRuleBound n

/-- The positive automaton state bound is at most `2^(45*n)` for `n ≥ 13`. -/
theorem candidatePositiveGrammarStateBound_le_two_pow
    (n : ℕ) (hn : 13 ≤ n) :
    candidatePositiveGrammarStateBound n ≤ 2 ^ (45 * n) := by
  apply le_trans ?_ (positiveCircuitBound_le_two_pow n hn)
  unfold candidatePositiveGrammarStateBound positiveCircuitBound
  have ha : 1 ≤ n * 2 ^ n := Nat.mul_pos (by omega) (Nat.two_pow_pos n)
  nlinarith [Nat.zero_le ((encodedInputCount n + 1) * 16 ^ (10 * n))]

/-- The rule-count bound is exponential as well.  The loose constant keeps
the calculation elementary. -/
theorem candidatePositiveGrammarRuleBound_le_two_pow
    (n : ℕ) (hn : 13 ≤ n) :
    candidatePositiveGrammarRuleBound n ≤ 2 ^ (180 * n) := by
  let P := 2 ^ (45 * n)
  have hstate : candidatePositiveGrammarStateBound n ≤ P :=
    candidatePositiveGrammarStateBound_le_two_pow n hn
  have hPpos : 1 ≤ P := Nat.one_le_two_pow
  have hPself : P ≤ P * P := by nlinarith
  calc
    candidatePositiveGrammarRuleBound n ≤ P + 2 * P * P := by
      unfold candidatePositiveGrammarRuleBound
      gcongr
    _ ≤ 4 * P * P := by nlinarith
    _ = 2 ^ (90 * n + 2) := by
      dsimp only [P]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      simp only [← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (180 * n) := by
      exact pow_le_pow_right' (by norm_num) (by omega)

theorem candidatePositiveGrammarDescriptionBound_le_two_pow
    (n : ℕ) (hn : 13 ≤ n) :
    candidatePositiveGrammarDescriptionBound n ≤ 2 ^ (181 * n) := by
  let P := 2 ^ (180 * n)
  have hstate : candidatePositiveGrammarStateBound n ≤ P :=
    (candidatePositiveGrammarStateBound_le_two_pow n hn).trans
      (pow_le_pow_right' (by norm_num) (by omega))
  have hrules : candidatePositiveGrammarRuleBound n ≤ P :=
    candidatePositiveGrammarRuleBound_le_two_pow n hn
  calc
    candidatePositiveGrammarDescriptionBound n ≤ 3 * P := by
      unfold candidatePositiveGrammarDescriptionBound
      omega
    _ ≤ 4 * P := by omega
    _ = 2 ^ (180 * n + 2) := by
      dsimp only [P]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (181 * n) := by
      exact pow_le_pow_right' (by norm_num) (by omega)

/-- Every direct right-linear rule contributes at most two right-hand-side
symbols. -/
theorem encodedOuterRightLinear_rhsSymbolCount_le
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (∑ rule : RuleRef (encodedOuterRightLinearCFG ranks hn a),
        rule.1.output.length) ≤
      2 * (encodedOuterRightLinearCFG ranks hn a).rules.card := by
  classical
  calc
    (∑ rule : RuleRef (encodedOuterRightLinearCFG ranks hn a),
        rule.1.output.length) ≤
        ∑ _rule : RuleRef (encodedOuterRightLinearCFG ranks hn a), 2 := by
      apply Finset.sum_le_sum
      intro rule hrule
      have hmem := rule.2
      change rule.1 ∈
        (encodedOuterAutomaton ranks hn a).toRightLinearCFG.rules at hmem
      rcases (encodedOuterAutomaton ranks hn a).toRightLinearCFG_rule_shape
          rule.1 hmem with hepsilon | htransition
      · rcases hepsilon with ⟨q, hfinal, hrule⟩
        rw [hrule]
        change 0 ≤ 2
        omega
      · rcases htransition with ⟨q, b, r, hstep, hrule⟩
        rw [hrule]
        change 2 ≤ 2
        omega
    _ = 2 * Fintype.card
          (RuleRef (encodedOuterRightLinearCFG ranks hn a)) := by
      simp [mul_comm]
    _ = 2 * (encodedOuterRightLinearCFG ranks hn a).rules.card := by
      rw [Fintype.card_coe]

/-- Exact finite form of the language consequence.  The positive grammar is
the direct automaton grammar with rules `q -> b r` and `q -> epsilon`.  Its
syntactic parse trees are equivalent to accepting runs, hence are unique.  A competing grammar
for the opposite length slice may be arbitrary and may accept anything at
other lengths. -/
theorem exists_candidate_rightLinearCFG_and_complement_CFG_lower_bound
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      (∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ (encodedOuterRightLinearCFG ranks
          (by omega : 0 < n) a).language ↔
          hardFunction ranks (by omega : 0 < n) a x) ∧
      (∀ word : List Bool,
        Subsingleton (encodedOuterRightLinearParse ranks
          (by omega : 0 < n) a word)) ∧
      @sourceParameter
          (encodedOuterRightLinearCFG ranks (by omega : 0 < n) a)
          (encodedOuterRightLinearFintype ranks
            (by omega : 0 < n) a) ≤
        candidatePositiveGrammarDescriptionBound n ∧
      ∀ (G : ContextFreeGrammar Bool)
          [Fintype G.NT] [DecidableEq G.NT],
        (∀ x : Fin (encodedInputCount n) → Bool,
          List.ofFn x ∈ G.language ↔
            ¬hardFunction ranks (by omega : 0 < n) a x) →
        cfgDescriptionExponentialLower n ≤
          (sourceParameter G + encodedInputCount n + 3 : ℕ) := by
  have hnpos : 0 < n := by omega
  obtain ⟨ranks, a, _C, hwidth, _hdet, _hcomputes, _hsize, hlower⟩ :=
    exists_candidate_dDNNF_width_and_complement_DNNF_lower_bound n hn
  have hstates :
      Fintype.card (encodedTermAutomatonFamily ranks hnpos a).UnionState ≤
        candidatePositiveGrammarStateBound n := by
    calc
      Fintype.card (encodedTermAutomatonFamily ranks hnpos a).UnionState ≤
          1 + Fintype.card (ThresholdTerm n) *
            ((encodedInputCount n + 1) * 16 ^ (10 * n)) :=
        encodedOuterAutomaton_state_card_le_of_width
          ranks hnpos a hwidth
      _ ≤ 1 + (n * 2 ^ n) *
            ((encodedInputCount n + 1) * 16 ^ (10 * n)) := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ (card_thresholdTerm_le n)
      _ = candidatePositiveGrammarStateBound n := rfl
  have hrules :
      (encodedOuterRightLinearCFG ranks hnpos a).rules.card ≤
        candidatePositiveGrammarRuleBound n := by
    apply (encodedOuterRightLinear_rule_card_le ranks hnpos a).trans
    apply Nat.add_le_add hstates
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hstates) hstates
  have hdescription :
      @sourceParameter (encodedOuterRightLinearCFG ranks hnpos a)
          (encodedOuterRightLinearFintype ranks hnpos a) ≤
        candidatePositiveGrammarDescriptionBound n := by
    unfold sourceParameter candidatePositiveGrammarDescriptionBound
    change Fintype.card
        (encodedTermAutomatonFamily ranks hnpos a).UnionState +
          (∑ rule : RuleRef (encodedOuterRightLinearCFG ranks hnpos a),
            rule.1.output.length) ≤ _
    apply Nat.add_le_add hstates
    exact (encodedOuterRightLinear_rhsSymbolCount_le ranks hnpos a).trans
      (Nat.mul_le_mul_left 2 hrules)
  refine ⟨ranks, a,
    encodedOuterRightLinearCFG_language_iff ranks hnpos a,
    encodedOuterRightLinearCFG_parse_subsingleton ranks hnpos a,
    hdescription, ?_⟩
  · exact
      complement_CFG_exponential_description_lower_bound_of_DNNF_lower_bound
      ranks hnpos a hlower

/-- Asymptotic family form with the polynomial word-length contribution
removed.  Eventually, every complement grammar's source parameter is at least
half of the explicit `exp(Omega(n^2))` quantity. -/
theorem eventually_exists_candidate_rightLinearCFG_and_complement_CFG_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      ∀ hn : 0 < n,
      ∃ ranks : LabelOrders n,
      ∃ a : Fin (encodedInputCount n) →
          ((Fin n × Fin n) → GadgetVector),
        (∀ x : Fin (encodedInputCount n) → Bool,
          List.ofFn x ∈ (encodedOuterRightLinearCFG ranks
            (by omega : 0 < n) a).language ↔
            hardFunction ranks (by omega : 0 < n) a x) ∧
        (∀ word : List Bool,
          Subsingleton (encodedOuterRightLinearParse ranks
            (by omega : 0 < n) a word)) ∧
        @sourceParameter
            (encodedOuterRightLinearCFG ranks (by omega : 0 < n) a)
            (encodedOuterRightLinearFintype ranks
              (by omega : 0 < n) a) ≤
          candidatePositiveGrammarDescriptionBound n ∧
        ∀ (G : ContextFreeGrammar Bool)
            [Fintype G.NT] [DecidableEq G.NT],
          (∀ x : Fin (encodedInputCount n) → Bool,
            List.ofFn x ∈ G.language ↔
              ¬hardFunction ranks (by omega : 0 < n) a x) →
          cfgDescriptionExponentialLower n / 2 ≤
            (sourceParameter G : ℝ) := by
  filter_upwards
    [eventually_two_encodedInputCount_add_three_le_cfgDescriptionLower]
      with n hdominates
  intro hn
  obtain ⟨ranks, a, hlanguage, hunambiguous, hpositiveSize, hhard⟩ :=
    exists_candidate_rightLinearCFG_and_complement_CFG_lower_bound n hn
  refine ⟨ranks, a, hlanguage, hunambiguous, hpositiveSize, ?_⟩
  intro G _ _ hlanguage
  have htotal := hhard G hlanguage
  norm_num at hdominates htotal ⊢
  nlinarith

end

end DDNNFNegation
