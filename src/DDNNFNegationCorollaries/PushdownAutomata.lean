import DDNNFNegationConsequences.PushdownSeparation
import DDNNFNegationCorollaries.GrammarComplementation
import TutorialBox

/-!
# Small unambiguous automata can require large DPDAs

Represent the small unambiguous finite automaton by its right-linear
grammar. A one-way DPDA for the same language would give a grammar for
the complement, of polynomially bounded size. The grammar lower bound
therefore forces a quasipolynomial increase in DPDA description size.
-/

namespace DDNNFNegation

open Filter CFGBinarization Pushdown

/-- The DPDA separation.  Eventually in `n`, for one choice of label
orders and encoder, the length-`N` language of `L_n`
(`N = encodedInputCount n`) has a right-linear grammar with unique parses
and description size at most `3 · candidatePositiveGrammarRuleBound n`,
which is `2^{O(n)}`; and every deterministic pushdown automaton whose
language agrees with that language on the words of length `N` has size at
least `dpdaSizeExponentialLower n`, which is `exp (Ω (n²))`.

The automaton may behave arbitrarily at every other word length, so this is
a bound against machines for the slice, not only against machines for a
language equal to it. -/
@[tutorial_box "cor:paper-dpda"]
theorem dpda_size_separation :
    ∀ᶠ n : ℕ in atTop,
      ∀ hn : 0 < n,
      ∃ ranks : LabelOrders n,
      ∃ a : Fin (encodedInputCount n) →
          ((Fin n × Fin n) → GadgetVector),
        (∀ x : Fin (encodedInputCount n) → Bool,
          List.ofFn x ∈ (encodedOuterRightLinearCFG ranks hn a).language ↔
            hardFunction ranks hn a x) ∧
        IsRightLinear (encodedOuterRightLinearCFG ranks hn a) ∧
        (∀ word : List Bool,
          Subsingleton (encodedOuterRightLinearParse ranks hn a word)) ∧
        descriptionSize (encodedOuterRightLinearCFG ranks hn a) ≤
          3 * candidatePositiveGrammarRuleBound n ∧
        ∀ M : DPDA,
          (∀ x : Fin (encodedInputCount n) → Bool,
            List.ofFn x ∈ M.language ↔ hardFunction ranks hn a x) →
          dpdaSizeExponentialLower n ≤ (M.size : ℝ) := by
  classical
  filter_upwards
    [eventually_two_encodedInputCount_add_three_le_cfgDescriptionLower]
      with n hdominates
  intro hn
  obtain ⟨ranks, a, _C, hwidth, _hdet, _hcomputes, _hsize, hlower⟩ :=
    exists_candidate_dDNNF_width_and_complement_DNNF_lower_bound n hn
  have hstates :
      Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState ≤
        candidatePositiveGrammarStateBound n := by
    calc
      Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState ≤
          1 + Fintype.card (ThresholdTerm n) *
            ((encodedInputCount n + 1) * 16 ^ (10 * n)) :=
        encodedOuterAutomaton_state_card_le_of_width ranks hn a hwidth
      _ ≤ 1 + (n * 2 ^ n) *
            ((encodedInputCount n + 1) * 16 ^ (10 * n)) := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ (card_thresholdTerm_le n)
      _ = candidatePositiveGrammarStateBound n := rfl
  have hrules :
      (encodedOuterRightLinearCFG ranks hn a).rules.card ≤
        candidatePositiveGrammarRuleBound n := by
    apply (encodedOuterRightLinear_rule_card_le ranks hn a).trans
    apply Nat.add_le_add hstates
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hstates) hstates
  have hrhs := encodedOuterRightLinear_rhsSymbolCount_le ranks hn a
  rw [Finset.sum_coe_sort (encodedOuterRightLinearCFG ranks hn a).rules
    (fun rule ↦ rule.output.length)] at hrhs
  refine ⟨ranks, a, encodedOuterRightLinearCFG_language_iff ranks hn a,
    encodedOuterRightLinearCFG_isRightLinear ranks hn a,
    encodedOuterRightLinearCFG_parse_subsingleton ranks hn a, ?_, ?_⟩
  · unfold descriptionSize
    omega
  · intro M hM
    have hHlang : ∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ M.complementCFG.language ↔ ¬hardFunction ranks hn a x := by
      intro x
      rw [DPDA.complementCFG_language]
      exact not_congr (hM x)
    have htotal :=
      complement_CFG_exponential_description_lower_bound_of_DNNF_lower_bound
        ranks hn a hlower M.complementCFG hHlang
    have hsize : sourceParameter M.complementCFG ≤ M.size ^ 9 :=
      DPDA.sourceParameter_complementCFG_le
    refine dpdaSizeExponentialLower_le_of_ninth_power n M.size ?_
    have hcast : ((sourceParameter M.complementCFG : ℕ) : ℝ) ≤ ((M.size ^ 9 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hsize
    norm_num at hdominates htotal hcast ⊢
    nlinarith

end DDNNFNegation
