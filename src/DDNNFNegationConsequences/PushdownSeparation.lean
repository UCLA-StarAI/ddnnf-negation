import DDNNFNegationConsequences.PushdownComplementGrammar

/-!
# Transferring the grammar lower bound to DPDAs

The complement grammar has source parameter bounded by the ninth power
of the DPDA description size. A small DPDA for the hard finite language
would therefore give a small grammar for its complement. Combining this
conversion with the grammar lower bound yields the DPDA separation.
-/

namespace DDNNFNegation

open Filter CFGBinarization Pushdown

/-- **Unambiguous finite automata against deterministic pushdown automata.**

For eventually every `n` the hard family has, on the one side, a right-linear
grammar that generates its positive length slice with at most one parse per
word and has size at most `candidatePositiveGrammarDescriptionBound n`, which
is `2 ^ O(n)`; and on the other side, every deterministic pushdown automaton
whose language agrees with that slice at the slice's own word length has
size at least `dpdaSizeExponentialLower n`, which is `exp (Omega (n ^ 2))`.

The automaton is allowed to behave arbitrarily at every other word length, so
this is a bound against machines for the slice, not only against machines for
a language equal to it. -/
theorem eventually_dpda_size_lower_bound :
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
        ∀ M : DPDA,
          (∀ x : Fin (encodedInputCount n) → Bool,
            List.ofFn x ∈ M.language ↔
              hardFunction ranks (by omega : 0 < n) a x) →
          dpdaSizeExponentialLower n ≤ (M.size : ℝ) := by
  filter_upwards
    [eventually_exists_candidate_rightLinearCFG_and_complement_CFG_lower_bound]
      with n hn'
  intro hn
  obtain ⟨ranks, a, hlanguage, hunambiguous, hpositiveSize, hhard⟩ := hn' hn
  refine ⟨ranks, a, hlanguage, hunambiguous, hpositiveSize, ?_⟩
  intro M hM
  have hHlang : ∀ x : Fin (encodedInputCount n) → Bool,
      List.ofFn x ∈ M.complementCFG.language ↔
        ¬hardFunction ranks (by omega : 0 < n) a x := by
    intro x
    rw [DPDA.complementCFG_language]
    exact not_congr (hM x)
  have hbound := hhard M.complementCFG hHlang
  have hsize : sourceParameter M.complementCFG ≤ M.size ^ 9 :=
    DPDA.sourceParameter_complementCFG_le
  refine dpdaSizeExponentialLower_le_of_ninth_power n M.size ?_
  calc cfgDescriptionExponentialLower n / 2
      ≤ ((sourceParameter M.complementCFG : ℕ) : ℝ) := hbound
    _ ≤ ((M.size ^ 9 : ℕ) : ℝ) := Nat.cast_le.mpr hsize

end DDNNFNegation
