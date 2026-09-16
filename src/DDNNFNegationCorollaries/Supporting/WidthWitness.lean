import DDNNFNegation.Separation

/-!
# Retaining the outer-term width witness

The separation construction supplies ranks and an encoder together with
small eligible terms. Retaining their width bound supports the ordered
decision-diagram, automaton, and grammar upper bounds. The same function
retains the DNNF node lower bound for its complement.
-/

namespace DDNNFNegation

open Finset

noncomputable section

/-- The cover count of the tutorial's final step: every balanced rectangle
cover of the complement has at least `1/(64 ε)` rectangles. -/
def spectralCircuitLower (n : ℕ) : ℝ :=
  1 / (64 * (2 / 3 : ℝ) ^ ((n : ℝ) ^ 2 / 30))

/-- One fixed encoded function has width-`10n` outer terms and an explicit
small deterministic DNNF, while every typed balanced rectangle cover of its
complement is exponentially large. -/
theorem exists_candidate_dDNNF_width_and_complement_cover_lower_bound
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      (∀ T : ThresholdTerm n,
        (termSigned ranks (by omega : 0 < n) T).positive.card +
          (termSigned ranks (by omega : 0 < n) T).negative.card ≤ 10 * n) ∧
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks
        (by omega : 0 < n) a) ∧
      C.edgeCount ≤ positiveCircuitBound n ∧
      ∀ (J : Type*) [Fintype J],
        ∀ _cover : BalancedRectangleCover
          (fun x ↦ ¬hardFunction ranks
            (by omega : 0 < n) a x) J,
          spectralCircuitLower n ≤ (Fintype.card J : ℝ) := by
  obtain ⟨ranks, hwidth⟩ := every_term_short hn
  obtain ⟨a, hcover⟩ :=
    exists_encoder_with_cover_lower_bound
      n hn ranks
  let C := encodedOuterDNNF ranks hn a
  refine ⟨ranks, a, C, hwidth,
    encodedOuterDNNF_isDeterministicDNNF ranks hn a,
    encodedOuterDNNF_computes ranks hn a, ?_, ?_⟩
  · calc
      C.edgeCount ≤
          Fintype.card (ThresholdTerm n) *
            (1 + 10 * ((encodedInputCount n + 1) * 16 ^ (10 * n))) :=
        encodedOuterDNNF_edgeCount_le_of_width ranks hn a hwidth
      _ ≤ positiveCircuitBound n :=
        Nat.mul_le_mul_right _ (card_thresholdTerm_le n)
  · intro J inst cover
    exact hcover J cover

/-- The circuit-level separation with the outer-term width witness retained
and the lower bound in gate counts: every DNNF for the complement with `s`
gates satisfies `1/(64 ε) ≤ 2 s (s + 2) + 1`. -/
theorem exists_candidate_dDNNF_width_and_complement_DNNF_lower_bound
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      (∀ T : ThresholdTerm n,
        (termSigned ranks (by omega : 0 < n) T).positive.card +
          (termSigned ranks (by omega : 0 < n) T).negative.card ≤ 10 * n) ∧
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks
        (by omega : 0 < n) a) ∧
      C.edgeCount ≤ positiveCircuitBound n ∧
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks
          (by omega : 0 < n) a x) →
        spectralCircuitLower n ≤ (2 * (D.nodeCount * (D.nodeCount + 2)) + 1 : ℕ) := by
  obtain ⟨ranks, a, C, hwidth, hdet, hcomputes, hsize, hcovers⟩ :=
    exists_candidate_dDNNF_width_and_complement_cover_lower_bound n hn
  refine ⟨ranks, a, C, hwidth, hdet, hcomputes, hsize, ?_⟩
  intro D hDNNF hDcomputes
  have hnn : 1 * 1 ≤ n * n := Nat.mul_le_mul hn hn
  have hVar : 2 ≤ Fintype.card (Fin (encodedInputCount n)) := by
    rw [Fintype.card_fin]
    show 2 ≤ 60 * (n * n)
    omega
  obtain ⟨r, cover, hr⟩ :=
    D.dedup.rectangle_cover hVar
      (D.dedup_isDNNF hDNNF) (D.dedup_computes hDcomputes)
  have hcover := hcovers (Fin r) cover
  rw [Fintype.card_fin] at hcover
  have hr' : r ≤ 2 * (D.nodeCount * (D.nodeCount + 2)) + 1 :=
    hr.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 D.edgeCount_dedup_le) 1)
  exact hcover.trans (by exact_mod_cast hr')

/-- The gate-count cover inequality gives an explicit square-root circuit
lower bound: `2 s (s + 2) + 1 ≤ 7 s²` for `1 ≤ s`. -/
theorem sqrt_seventh_le_nat_of_le_quadratic
    (L : ℝ) (s : ℕ) (hs : 1 ≤ s)
    (hbound : L ≤ (2 * (s * (s + 2)) + 1 : ℕ)) :
    Real.sqrt (L / 7) ≤ (s : ℝ) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hpoly : ((2 * (s * (s + 2)) + 1 : ℕ) : ℝ) ≤
        7 * (s : ℝ) ^ 2 := by
      norm_cast
      nlinarith
    have hLsq : L ≤ 7 * (s : ℝ) ^ 2 := hbound.trans hpoly
    linarith

/-- The exponential rate of the gate-count lower bound: half of the rate
`-log(2/3)/30` of the cover count, from the square root. -/
noncomputable def gateSeparationRate : ℝ :=
  -Real.log (2 / 3 : ℝ) / 60

/-- The leading constant of the gate-count lower bound. -/
noncomputable def gateQuasipolynomialPrefactor : ℝ :=
  Real.sqrt ((1 : ℝ) / 448)

theorem gateSeparationRate_pos : 0 < gateSeparationRate := by
  unfold gateSeparationRate
  have hlog : Real.log (2 / 3 : ℝ) < 0 :=
    Real.log_neg (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
  exact div_pos (neg_pos.mpr hlog) (by norm_num)

theorem gateQuasipolynomialPrefactor_pos :
    0 < gateQuasipolynomialPrefactor := by
  unfold gateQuasipolynomialPrefactor
  positivity

/-- Exact exponential form of the square-root gate-count lower bound. -/
theorem sqrt_spectralCircuitLower_eq_exponential (n : ℕ) :
    Real.sqrt (spectralCircuitLower n / 7) =
      gateQuasipolynomialPrefactor *
        Real.exp (gateSeparationRate * (n : ℝ) ^ 2) := by
  have hsqrtExp (x : ℝ) :
      Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    have hexp : Real.exp x = (Real.exp (x / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hexp, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hinside :
      spectralCircuitLower n / 7 =
        ((1 : ℝ) / 448) *
          Real.exp ((-Real.log (2 / 3 : ℝ) / 30) *
            (n : ℝ) ^ 2) := by
    unfold spectralCircuitLower
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    rw [show Real.exp
          (Real.log (2 / 3 : ℝ) * ((n : ℝ) ^ 2 / 30)) =
        (Real.exp
          ((-Real.log (2 / 3 : ℝ) / 30) * (n : ℝ) ^ 2))⁻¹ by
      rw [← Real.exp_neg]
      congr 1
      ring]
    field_simp
    ring
  rw [hinside, Real.sqrt_mul (by positivity), hsqrtExp]
  unfold gateQuasipolynomialPrefactor gateSeparationRate
  congr 1
  congr 1
  ring

end

end DDNNFNegation
