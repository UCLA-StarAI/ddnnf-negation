import DDNNFNegation.Separation
import DDNNFNegationConsequences.WidthWitness
import DDNNFNegationConsequences.CFGBinarization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The fixed-length context-free grammar lower bound

This file composes the arbitrary-CFG interval compiler with the formal DNNF
separation.  A grammar agreeing with the hard complement on the relevant
length slice would produce a DNNF for that complement.  The circuit lower
bound therefore applies to the explicit polynomial parser-size bound.
-/

namespace DDNNFNegation

open CFGBinarization
open Filter Asymptotics

/-- The explicit interval parser bound is at most a ninth-degree polynomial
in its normalized grammar parameter and the word length. -/
theorem intervalParserBound_le_six_pow (N q : ℕ) :
    1 + 2 * N +
          (q * (N + 1) ^ 2) * q ^ 3 * (N + 1) ^ 3 +
          (q * (N + 1) ^ 2 + 1) * q * (N + 1) ^ 2 ≤
      6 * (q + N + 1) ^ 9 := by
  let s := q + N + 1
  have hq : q ≤ s := by dsimp [s]; omega
  have hN : N + 1 ≤ s := by dsimp [s]; omega
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hlong :
      (q * (N + 1) ^ 2) * q ^ 3 * (N + 1) ^ 3 ≤ s ^ 9 := by
    calc
      (q * (N + 1) ^ 2) * q ^ 3 * (N + 1) ^ 3 ≤
          (s * s ^ 2) * s ^ 3 * s ^ 3 := by gcongr
      _ = s ^ 9 := by ring
  have ht : q * (N + 1) ^ 2 ≤ s ^ 3 := by
    calc
      q * (N + 1) ^ 2 ≤ s * s ^ 2 := by gcongr
      _ = s ^ 3 := by ring
  have hone3 : 1 ≤ s ^ 3 := Nat.one_le_pow 3 s (by omega)
  have hshort :
      (q * (N + 1) ^ 2 + 1) * q * (N + 1) ^ 2 ≤
        2 * s ^ 6 := by
    calc
      (q * (N + 1) ^ 2 + 1) * q * (N + 1) ^ 2 =
          (q * (N + 1) ^ 2 + 1) * (q * (N + 1) ^ 2) := by ring
      _ ≤ (s ^ 3 + s ^ 3) * s ^ 3 := by gcongr
      _ = 2 * s ^ 6 := by ring
  have hs_le_pow : s ≤ s ^ 9 := by
    calc
      s = s ^ 1 := by simp
      _ ≤ s ^ 9 := pow_le_pow_right' hs (by omega)
  have hone9 : 1 ≤ s ^ 9 := hs.trans hs_le_pow
  have hN9 : N ≤ s ^ 9 := (by omega : N ≤ s).trans hs_le_pow
  have hbase : 1 + 2 * N ≤ 3 * s ^ 9 := by omega
  have h6_9 : s ^ 6 ≤ s ^ 9 :=
    pow_le_pow_right' hs (by omega)
  calc
    1 + 2 * N +
          (q * (N + 1) ^ 2) * q ^ 3 * (N + 1) ^ 3 +
          (q * (N + 1) ^ 2 + 1) * q * (N + 1) ^ 2 ≤
        3 * s ^ 9 + s ^ 9 + 2 * s ^ 6 := by omega
    _ ≤ 6 * s ^ 9 := by omega
    _ = 6 * (q + N + 1) ^ 9 := by rfl

/-- Generic transfer of the fixed-slice DNNF lower bound to an arbitrary
finite CFG.  The grammar may behave arbitrarily away from the selected word
length. -/
theorem complement_CFG_lower_bound_of_DNNF_lower_bound
    {n : ℕ} (ranks : LabelOrders n) (hnpos : 0 < n)
    (a : Fin (encodedInputCount n) →
      ((Fin n × Fin n) → GadgetVector))
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      D.IsDNNF →
      D.Computes (fun x ↦ ¬hardFunction ranks hnpos a x) →
      spectralCircuitLower n ≤
        (2 * (D.size * (D.size + 2)) + 1 : ℕ)) :
    ∀ (G : ContextFreeGrammar Bool)
        [Fintype G.NT] [DecidableEq G.NT],
      (∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ G.language ↔
          ¬hardFunction ranks hnpos a x) →
      let q := Fintype.card G.NT + 2 +
        ∑ rule : RuleRef G, rule.1.output.length
      let B :=
        1 + 2 * encodedInputCount n +
          (q * (encodedInputCount n + 1) ^ 2) * q ^ 3 *
            (encodedInputCount n + 1) ^ 3 +
          (q * (encodedInputCount n + 1) ^ 2 + 1) * q *
            (encodedInputCount n + 1) ^ 2
      spectralCircuitLower n ≤ (2 * (B * (B + 2)) + 1 : ℕ) ∧
        gateQuasipolynomialPrefactor *
            Real.exp (gateSeparationRate * (n : ℝ) ^ 2) ≤
          (B : ℝ) := by
  intro G _ _ hlanguage
  dsimp only
  let D : NNFCircuit (Fin (encodedInputCount n)) :=
    (grammar G).closureIntervalCircuit
  have hDNNF : D.IsDNNF := by
    exact intervalCircuit_isDNNF G
  have hDcomputes : D.Computes (fun x ↦
      ¬hardFunction ranks hnpos a x) := by
    intro x
    exact (intervalCircuit_computes_source_language G x).trans
      (hlanguage x)
  have hDlower := hlower D hDNNF hDcomputes
  change spectralCircuitLower n ≤
    (2 * (D.size * (D.size + 2)) + 1 : ℕ) at hDlower
  let q := Fintype.card G.NT + 2 +
    ∑ rule : RuleRef G, rule.1.output.length
  let B :=
    1 + 2 * encodedInputCount n +
      (q * (encodedInputCount n + 1) ^ 2) * q ^ 3 *
        (encodedInputCount n + 1) ^ 3 +
      (q * (encodedInputCount n + 1) ^ 2 + 1) * q *
        (encodedInputCount n + 1) ^ 2
  have hDsize : D.size ≤ B := by
    exact intervalCircuit_size_le G
  have hpoly :
      2 * (D.size * (D.size + 2)) + 1 ≤ 2 * (B * (B + 2)) + 1 := by
    nlinarith
  have hquadratic :
      spectralCircuitLower n ≤ (2 * (B * (B + 2)) + 1 : ℕ) :=
    hDlower.trans (by exact_mod_cast hpoly)
  have hBpos : 1 ≤ B := by
    dsimp only [B]
    omega
  have hsqrt := sqrt_seventh_le_nat_of_le_quadratic
    (spectralCircuitLower n) B hBpos hquadratic
  rw [sqrt_spectralCircuitLower_eq_exponential] at hsqrt
  exact ⟨hquadratic, hsqrt⟩

/-- Direct description-size consequence of the parser transfer.  The
ninth-degree polynomial is deliberately loose but removes the internal parser
size from the final inequality. -/
theorem complement_CFG_ninth_power_lower_bound_of_DNNF_lower_bound
    {n : ℕ} (ranks : LabelOrders n) (hnpos : 0 < n)
    (a : Fin (encodedInputCount n) →
      ((Fin n × Fin n) → GadgetVector))
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      D.IsDNNF →
      D.Computes (fun x ↦ ¬hardFunction ranks hnpos a x) →
      spectralCircuitLower n ≤
        (2 * (D.size * (D.size + 2)) + 1 : ℕ)) :
    ∀ (G : ContextFreeGrammar Bool)
        [Fintype G.NT] [DecidableEq G.NT],
      (∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ G.language ↔
          ¬hardFunction ranks hnpos a x) →
      let q := Fintype.card G.NT + 2 +
        ∑ rule : RuleRef G, rule.1.output.length
      gateQuasipolynomialPrefactor *
          Real.exp (gateSeparationRate * (n : ℝ) ^ 2) ≤
        (6 * (q + encodedInputCount n + 1) ^ 9 : ℕ) := by
  intro G _ _ hlanguage
  have hparser := complement_CFG_lower_bound_of_DNNF_lower_bound
    ranks hnpos a hlower G hlanguage
  dsimp only at hparser ⊢
  exact hparser.2.trans (by
    exact_mod_cast intervalParserBound_le_six_pow
      (encodedInputCount n)
      (Fintype.card G.NT + 2 +
        ∑ rule : RuleRef G, rule.1.output.length))

/-- The exact ninth root of the exponential term after absorbing the factor
six in the parser bound. -/
noncomputable def cfgDescriptionExponentialLower (n : ℕ) : ℝ :=
  Real.exp ((Real.log (gateQuasipolynomialPrefactor / 6) +
    gateSeparationRate * (n : ℝ) ^ 2) / 9)

theorem cfgDescriptionExponentialLower_pos (n : ℕ) :
    0 < cfgDescriptionExponentialLower n := by
  unfold cfgDescriptionExponentialLower
  positivity

theorem cfgDescriptionExponentialLower_factor (n : ℕ) :
    cfgDescriptionExponentialLower n =
      Real.exp (Real.log (gateQuasipolynomialPrefactor / 6) / 9) *
        Real.exp ((gateSeparationRate / 9) * (n : ℝ) ^ 2) := by
  unfold cfgDescriptionExponentialLower
  rw [← Real.exp_add]
  congr 1
  ring

theorem cfgDescriptionExponentialLower_pow_nine (n : ℕ) :
    cfgDescriptionExponentialLower n ^ 9 =
      (gateQuasipolynomialPrefactor / 6) *
        Real.exp (gateSeparationRate * (n : ℝ) ^ 2) := by
  have hc : 0 < gateQuasipolynomialPrefactor / 6 := by
    exact div_pos gateQuasipolynomialPrefactor_pos (by norm_num)
  unfold cfgDescriptionExponentialLower
  rw [← Real.exp_nat_mul]
  calc
    Real.exp ((9 : ℝ) *
        ((Real.log (gateQuasipolynomialPrefactor / 6) +
          gateSeparationRate * (n : ℝ) ^ 2) / 9)) =
        Real.exp (Real.log (gateQuasipolynomialPrefactor / 6) +
          gateSeparationRate * (n : ℝ) ^ 2) := by congr 1; ring
    _ = Real.exp (Real.log (gateQuasipolynomialPrefactor / 6)) *
          Real.exp (gateSeparationRate * (n : ℝ) ^ 2) := by
      rw [Real.exp_add]
    _ = (gateQuasipolynomialPrefactor / 6) *
          Real.exp (gateSeparationRate * (n : ℝ) ^ 2) := by
      rw [Real.exp_log hc]

theorem cfgDescriptionExponentialLower_le_of_ninth_power
    (n s : ℕ)
    (h : gateQuasipolynomialPrefactor *
          Real.exp (gateSeparationRate * (n : ℝ) ^ 2) ≤
        (6 * s ^ 9 : ℕ)) :
    cfgDescriptionExponentialLower n ≤ (s : ℝ) := by
  have hdiv :
      (gateQuasipolynomialPrefactor / 6) *
          Real.exp (gateSeparationRate * (n : ℝ) ^ 2) ≤
        (s : ℝ) ^ 9 := by
    norm_num at h ⊢
    nlinarith
  apply le_of_pow_le_pow_left₀ (n := 9) (by norm_num) (by positivity)
  rw [cfgDescriptionExponentialLower_pow_nine]
  exact hdiv

/-- The quadratic word-length term is asymptotically negligible beside the
explicit hard-side exponential. -/
theorem encodedInputCount_add_three_isLittleO_cfgDescriptionLower :
    (fun n : ℕ => ((encodedInputCount n + 3 : ℕ) : ℝ))
      =o[atTop] cfgDescriptionExponentialLower := by
  have hb : 0 < gateSeparationRate / 9 :=
    div_pos gateSeparationRate_pos (by norm_num)
  have hk : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n)
      (sub_nonneg.mpr hnR)]
  have htwo :
      (fun n : ℕ => (n : ℝ) ^ 2) =o[atTop]
        (fun n : ℕ => Real.exp ((gateSeparationRate / 9) * (n : ℝ) ^ 2)) := by
    simpa [Function.comp_def] using
      (isLittleO_pow_exp_pos_mul_atTop 1 hb).comp_tendsto hk
  have hone :
      (fun _n : ℕ => (1 : ℝ)) =o[atTop]
        (fun n : ℕ => Real.exp ((gateSeparationRate / 9) * (n : ℝ) ^ 2)) := by
    simpa [Function.comp_def] using
      (isLittleO_pow_exp_pos_mul_atTop 0 hb).comp_tendsto hk
  have hpoly :
      (fun n : ℕ => (60 : ℝ) * (n : ℝ) ^ 2 + 3) =o[atTop]
        (fun n : ℕ => Real.exp ((gateSeparationRate / 9) * (n : ℝ) ^ 2)) := by
    simpa only [mul_one] using
      (htwo.const_mul_left 60).add (hone.const_mul_left 3)
  have hK : Real.exp (Real.log (gateQuasipolynomialPrefactor / 6) / 9) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hscaled := hpoly.const_mul_right hK
  apply hscaled.congr'
  · filter_upwards with n
    simp [encodedInputCount, pow_two]
  · filter_upwards with n
    exact (cfgDescriptionExponentialLower_factor n).symm

theorem eventually_two_encodedInputCount_add_three_le_cfgDescriptionLower :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) * (encodedInputCount n + 3 : ℕ) ≤
        cfgDescriptionExponentialLower n := by
  have hsmall :=
    encodedInputCount_add_three_isLittleO_cfgDescriptionLower.bound
      (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall] with n hn
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (encodedInputCount n + 3 : ℕ)),
    Real.norm_eq_abs,
    abs_of_pos (cfgDescriptionExponentialLower_pos n)] at hn
  norm_num at hn ⊢
  linarith

/-- The grammar's normalized description size plus the selected word length
is bounded below by an explicit exponential in `n^2`. -/
theorem complement_CFG_exponential_description_lower_bound_of_DNNF_lower_bound
    {n : ℕ} (ranks : LabelOrders n) (hnpos : 0 < n)
    (a : Fin (encodedInputCount n) →
      ((Fin n × Fin n) → GadgetVector))
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      D.IsDNNF →
      D.Computes (fun x ↦ ¬hardFunction ranks hnpos a x) →
      spectralCircuitLower n ≤
        (2 * (D.size * (D.size + 2)) + 1 : ℕ)) :
    ∀ (G : ContextFreeGrammar Bool)
        [Fintype G.NT] [DecidableEq G.NT],
      (∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ G.language ↔
          ¬hardFunction ranks hnpos a x) →
      cfgDescriptionExponentialLower n ≤
        (sourceParameter G + encodedInputCount n + 3 : ℕ) := by
  intro G _ _ hlanguage
  have hninth := complement_CFG_ninth_power_lower_bound_of_DNNF_lower_bound
    ranks hnpos a hlower G hlanguage
  dsimp only at hninth
  have hroot :=
    cfgDescriptionExponentialLower_le_of_ninth_power n _ hninth
  have heq :
      (Fintype.card G.NT + 2 +
          ∑ rule : RuleRef G, rule.1.output.length) +
          encodedInputCount n + 1 =
        sourceParameter G + encodedInputCount n + 3 := by
    unfold sourceParameter
    omega
  rw [heq] at hroot
  exact hroot

/-- Once the exponential term dominates the quadratic word length, it gives
a direct lower bound on the grammar parameter itself. -/
theorem complement_CFG_sourceParameter_lower_bound_of_DNNF_lower_bound
    {n : ℕ} (ranks : LabelOrders n) (hnpos : 0 < n)
    (a : Fin (encodedInputCount n) →
      ((Fin n × Fin n) → GadgetVector))
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      D.IsDNNF →
      D.Computes (fun x ↦ ¬hardFunction ranks hnpos a x) →
      spectralCircuitLower n ≤
        (2 * (D.size * (D.size + 2)) + 1 : ℕ))
    (hdominates :
      (2 : ℝ) * (encodedInputCount n + 3 : ℕ) ≤
        cfgDescriptionExponentialLower n) :
    ∀ (G : ContextFreeGrammar Bool)
        [Fintype G.NT] [DecidableEq G.NT],
      (∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ G.language ↔
          ¬hardFunction ranks hnpos a x) →
      cfgDescriptionExponentialLower n / 2 ≤
        (sourceParameter G : ℝ) := by
  intro G _ _ hlanguage
  have htotal :=
    complement_CFG_exponential_description_lower_bound_of_DNNF_lower_bound
      ranks hnpos a hlower G hlanguage
  norm_num at hdominates htotal ⊢
  nlinarith

/-- The formal circuit separation transferred to arbitrary finite CFGs on the
hard fixed-length slice.  The grammar may behave arbitrarily at every other
word length. -/
theorem exists_candidate_dDNNF_and_complement_CFG_lower_bound
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks
        (by omega : 0 < n) a) ∧
      C.edgeCount ≤ positiveCircuitBound n ∧
      ∀ (G : ContextFreeGrammar Bool)
          [Fintype G.NT] [DecidableEq G.NT],
        (∀ x : Fin (encodedInputCount n) → Bool,
          List.ofFn x ∈ G.language ↔
            ¬hardFunction ranks (by omega : 0 < n) a x) →
        let q := Fintype.card G.NT + 2 +
          ∑ rule : RuleRef G, rule.1.output.length
        let B :=
          1 + 2 * encodedInputCount n +
            (q * (encodedInputCount n + 1) ^ 2) * q ^ 3 *
              (encodedInputCount n + 1) ^ 3 +
            (q * (encodedInputCount n + 1) ^ 2 + 1) * q *
              (encodedInputCount n + 1) ^ 2
        spectralCircuitLower n ≤ (2 * (B * (B + 2)) + 1 : ℕ) ∧
          gateQuasipolynomialPrefactor *
              Real.exp (gateSeparationRate * (n : ℝ) ^ 2) ≤
            (B : ℝ) := by
  obtain ⟨ranks, a, C, _hwidth, hdet, hcomputes, hsize, hlower⟩ :=
    exists_candidate_dDNNF_width_and_complement_DNNF_lower_bound n hn
  refine ⟨ranks, a, C, hdet, hcomputes, hsize, ?_⟩
  exact complement_CFG_lower_bound_of_DNNF_lower_bound
    ranks (by omega : 0 < n) a hlower

end DDNNFNegation
