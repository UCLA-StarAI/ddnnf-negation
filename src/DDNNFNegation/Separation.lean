import DDNNFNegation.GateElimination
import DDNNFNegation.PositiveSide
import DDNNFNegation.FinalCover
import DDNNFNegation.RankOrders
import DDNNFNegation.OBDD
import DDNNFNegation.CircuitOperations
import TutorialBox

/-!
# The explicit separation and padding the hard function

At construction parameter `n`, the hard function has `60 * n^2` inputs,
a d-DNNF of size `2^{O(n)}`, and a DNNF lower bound of `2^{Ω(n^2)}` for
its negation. Internal edge estimates are converted to the node-count
statement `negation_separation`.

Padding with unused variables to length `2^(46*n)` gives
`nonclosure_under_negation`: polynomial size before negation and a
quasipolynomial lower bound afterwards, measured in the padded input
length.
-/

namespace DDNNFNegation

open Finset

noncomputable section

/-- The edge count of the positive circuit: at most `n 2^n` term
OBDDs of at most `(N + 1) 16^{10 n}` nodes each, at most ten edges per
node, and one edge per term into the top OR. -/
abbrev positiveCircuitBound (n : ℕ) : ℕ :=
  (n * 2 ^ n) * (1 + 10 * ((encodedInputCount n + 1) * 16 ^ (10 * n)))

/-- The unpadded separation in edge count. One choice of label orders and
encoder gives a d-DNNF with at most `positiveCircuitBound n` edges, while
every DNNF for its complement has at least `1/(128 * ε) - 1/2` edges. -/
theorem negation_separation_edges
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks
        (by omega : 0 < n) a) ∧
      C.edgeCount ≤ positiveCircuitBound n ∧
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks
          (by omega : 0 < n) a x) →
        spectralEdgeLower n ≤ (D.edgeCount : ℝ) := by
  obtain ⟨ranks, hwidth⟩ := every_term_short hn
  obtain ⟨a, hlower⟩ := DNNF_lower_bound n hn ranks
  obtain ⟨C, hdet, hcomputes, hsize⟩ := small_dDNNF ranks hn a hwidth
  exact ⟨ranks, a, C, hdet, hcomputes,
    hsize.trans (Nat.mul_le_mul_right _ (card_thresholdTerm_le n)), hlower⟩

/-- A variable type with `core` active positions and enough unused positions
to reach `total`. -/
abbrev PaddedVar (core total : ℕ) :=
  Fin core ⊕ Fin (total - core)

/-- When the total length exceeds the active length, the padding type has exactly the
requested total cardinality. -/
theorem card_paddedVar {core total : ℕ} (hcore : core ≤ total) :
    Fintype.card (PaddedVar core total) = total := by
  simp [PaddedVar]
  omega

/-- The output gate witnesses that every circuit has at least one gate. -/
theorem circuit_size_pos
    {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) :
    1 ≤ C.size := by
  have hpos : 0 < Fintype.card C.Gate :=
    Fintype.card_pos_iff.mpr ⟨C.output⟩
  change 1 ≤ Fintype.card C.Gate
  omega

/-- The encoded function extended by unused variables. -/
def paddedEncodedOuterFunction
    {n core total : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin core → ((Fin n × Fin n) → GadgetVector))
    (v : PaddedVar core total → Bool) : Prop :=
  hardFunction ranks hn a (v ∘ Sum.inl)

/-- Padding by unused variables preserves the positive circuit's edge
count. Fixing those variables to false in a circuit for the complement
recovers the unpadded lower bound. -/
theorem exists_candidate_padded_dDNNF_and_complement_DNNF_lower_bound
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks
        (by omega : 0 < n) a) ∧
      C.edgeCount ≤ positiveCircuitBound n ∧
      ∀ (total : ℕ), encodedInputCount n ≤ total →
        let Cpad : NNFCircuit.{0, 0}
            (PaddedVar (encodedInputCount n) total) :=
          C.padRightVariables
        Fintype.card (PaddedVar (encodedInputCount n) total) = total ∧
        Cpad.IsDeterministicDNNF ∧
        Cpad.Computes (paddedEncodedOuterFunction ranks
          (by omega : 0 < n) a) ∧
        Cpad.edgeCount ≤ positiveCircuitBound n ∧
        ∀ D : NNFCircuit.{0, 0}
            (PaddedVar (encodedInputCount n) total),
          D.IsDNNF →
          D.Computes (fun x ↦ ¬paddedEncodedOuterFunction ranks
            (by omega : 0 < n) a x) →
          spectralEdgeLower n ≤ (D.edgeCount : ℝ) := by
  obtain ⟨ranks, a, C, hdet, hcomputes, hsize, hlower⟩ :=
    negation_separation_edges n hn
  refine ⟨ranks, a, C, hdet, hcomputes, hsize, ?_⟩
  intro total htotal
  dsimp only
  refine ⟨card_paddedVar htotal,
    C.padRightVariables_isDeterministicDNNF hdet, ?_, ?_, ?_⟩
  · intro v
    exact hcomputes (v ∘ Sum.inl)
  · rw [NNFCircuit.edgeCount_padRightVariables]
    exact hsize
  · intro D hDNNF hDcomputes
    let fixed : Fin (total - encodedInputCount n) → Bool := fun _ ↦ false
    let Drest : NNFCircuit.{0, 0} (Fin (encodedInputCount n)) :=
      D.restrictRightVariables fixed
    have hrestDNNF : Drest.IsDNNF :=
      D.restrictRightVariables_decomposable fixed hDNNF
    have hrestComputes : Drest.Computes (fun x ↦
        ¬hardFunction ranks
          (by omega : 0 < n) a x) := by
      have hrest := D.restrictRightVariables_computes fixed hDcomputes
      intro x
      simpa [Drest, paddedEncodedOuterFunction, Function.comp_def] using
        hrest x
    have h := hlower Drest hrestDNNF hrestComputes
    have hedges : Drest.edgeCount = D.edgeCount :=
      NNFCircuit.edgeCount_restrictRightVariables D fixed
    rwa [hedges] at h

/-- The padded input length `2^(46*n)`, large enough to bound the positive circuit size. -/
abbrev exponentialPaddedLength (n : ℕ) : ℕ :=
  2 ^ (46 * n)

/-- The natural-exponential rate in the reciprocal spectral term `exp(separationRate * n²)`. -/
noncomputable def separationRate : ℝ :=
  -Real.log (2 / 3 : ℝ) / 30

/-- The rate after changing variables to padded length: `separationRate / (46 * log 2)^2`. -/
noncomputable def quasipolynomialRate : ℝ :=
  separationRate / ((46 : ℝ) * Real.log 2) ^ 2

/-- The prefactor `1/256`, reserving half the reciprocal spectral bound to absorb its subtractive constant. -/
noncomputable def quasipolynomialPrefactor : ℝ :=
  1 / 256

/-- The exponential rate in the complement lower bound is positive. -/
theorem separationRate_pos : 0 < separationRate := by
  unfold separationRate
  have hlog : Real.log (2 / 3 : ℝ) < 0 :=
    Real.log_neg (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
  exact div_pos (neg_pos.mpr hlog) (by norm_num)

/-- The rate after changing from the construction parameter to padded input length is
positive. -/
theorem quasipolynomialRate_pos : 0 < quasipolynomialRate := by
  unfold quasipolynomialRate
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact div_pos separationRate_pos (sq_pos_of_pos (mul_pos (by norm_num) hlog))

/-- The fixed multiplicative constant in the padded lower bound is positive. -/
theorem quasipolynomialPrefactor_pos :
    0 < quasipolynomialPrefactor := by
  unfold quasipolynomialPrefactor
  norm_num

/-- The polynomial factor in the unpadded Boolean input count is swallowed
by a very crude power of two. -/
theorem encodedInputCount_add_one_le_two_pow (n : ℕ) :
    encodedInputCount n + 1 ≤ 2 ^ (2 * n + 9) := by
  calc
    encodedInputCount n + 1 ≤
        2 ^ 9 * (2 * n ^ 2 + 1) := by
          simp only [encodedInputCount]
          nlinarith
    _ ≤ 2 ^ 9 * 2 ^ (2 * n) := by
          exact Nat.mul_le_mul_left _
            (Nat.two_mul_sq_add_one_le_two_pow_two_mul n)
    _ = 2 ^ (2 * n + 9) := by
          rw [pow_add]
          ac_rfl

/-- The explicit positive construction has at most `2^(45*n)` edges.  The
constant is intentionally loose so the proof uses only elementary power
estimates. -/
theorem positiveCircuitBound_le_two_pow (n : ℕ) (hn : 13 ≤ n) :
    positiveCircuitBound n ≤ 2 ^ (45 * n) := by
  have hnPow : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have hbits := encodedInputCount_add_one_le_two_pow n
  have height : 16 ^ (10 * n) = 2 ^ (40 * n) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    congr 1
    omega
  set X := (encodedInputCount n + 1) * 16 ^ (10 * n) with hX
  have hXpos : 1 ≤ X := by
    rw [hX]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hXle : X ≤ 2 ^ (2 * n + 9) * 2 ^ (40 * n) := by
    rw [hX, height]
    exact Nat.mul_le_mul_right _ hbits
  have hinner : 1 + 10 * X ≤ 2 ^ 4 * (2 ^ (2 * n + 9) * 2 ^ (40 * n)) := by
    calc 1 + 10 * X ≤ 2 ^ 4 * X := by omega
      _ ≤ 2 ^ 4 * (2 ^ (2 * n + 9) * 2 ^ (40 * n)) :=
        Nat.mul_le_mul_left _ hXle
  calc
    positiveCircuitBound n = (n * 2 ^ n) * (1 + 10 * X) := rfl
    _ ≤ (2 ^ n * 2 ^ n) * (2 ^ 4 * (2 ^ (2 * n + 9) * 2 ^ (40 * n))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hnPow) hinner
    _ = 2 ^ (44 * n + 13) := by
      simp only [← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (45 * n) := by
      exact pow_le_pow_right' (by norm_num) (by omega)

/-- There is enough room for all active variables at the chosen padded length. -/
theorem encodedInputCount_le_exponentialPaddedLength
    (n : ℕ) (hn : 13 ≤ n) :
    encodedInputCount n ≤ exponentialPaddedLength n := by
  calc
    encodedInputCount n ≤ encodedInputCount n + 1 := Nat.le_succ _
    _ ≤ 2 ^ (2 * n + 9) := encodedInputCount_add_one_le_two_pow n
    _ ≤ 2 ^ (46 * n) := pow_le_pow_right' (by norm_num) (by omega)

/-- The explicit positive circuit fits within the chosen padded input length. -/
theorem positiveCircuitBound_le_exponentialPaddedLength
    (n : ℕ) (hn : 13 ≤ n) :
    positiveCircuitBound n ≤ exponentialPaddedLength n := by
  exact (positiveCircuitBound_le_two_pow n hn).trans
    (pow_le_pow_right' (by norm_num) (by omega))

/-- Write the reciprocal spectral term as `1/(128 * ε) = (1/128) * exp(separationRate * n²)`. -/
theorem inv_spectral_eq_exp (n : ℕ) :
    1 / (128 * spectralEpsilon n) =
      (1 / 128) * Real.exp (separationRate * (n : ℝ) ^ 2) := by
  unfold spectralEpsilon
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  unfold separationRate
  rw [show Real.exp
        (Real.log (2 / 3 : ℝ) * ((n : ℝ) ^ 2 / 30)) =
      (Real.exp
        ((-Real.log (2 / 3 : ℝ) / 30) * (n : ℝ) ^ 2))⁻¹ by
    rw [← Real.exp_neg]
    congr 1
    ring]
  field_simp

/-- `log (3/2) ≥ 1/3`, so the rate is at least `1/90`. -/
theorem separationRate_ge : 1 / 90 ≤ separationRate := by
  unfold separationRate
  have h : (1 : ℝ) - (3 / 2)⁻¹ ≤ Real.log (3 / 2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h2 : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2) := by
    rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  rw [h2]
  norm_num at h ⊢
  linarith

/-- For `n ≥ 25`, half the exponential term absorbs the constant `1/2`, using `exp x ≥ x^6/720`. -/
theorem exp_separationRate_absorbs (n : ℕ) (hn : 25 ≤ n) :
    (128 : ℝ) ≤ Real.exp (separationRate * (n : ℝ) ^ 2) := by
  have hn' : (25 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := (n : ℝ) ^ 2 / 90 with hx
  have hx0 : 0 ≤ x := by positivity
  have hexp : x ^ 6 / (Nat.factorial 6 : ℝ) ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hx0 6
  have hfact : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfact] at hexp
  have hmono : Real.exp x ≤ Real.exp (separationRate * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have := separationRate_ge
    rw [hx]
    nlinarith [sq_nonneg (n : ℝ)]
  have hpoly : (128 : ℝ) ≤ x ^ 6 / 720 := by
    have hx6 : x ^ 6 / 720 = (n : ℝ) ^ 12 / (90 ^ 6 * 720) := by
      rw [hx]
      ring
    rw [hx6, le_div_iff₀ (by norm_num)]
    calc (128 : ℝ) * (90 ^ 6 * 720) ≤ (25 : ℝ) ^ 12 := by norm_num
      _ ≤ (n : ℝ) ^ 12 := pow_le_pow_left₀ (by norm_num) hn' 12
  linarith

/-- For `n ≥ 25`, the explicit padded lower bound is at most the internal spectral edge bound. -/
theorem quasipolynomial_le_spectralEdgeLower (n : ℕ) (hn : 25 ≤ n) :
    quasipolynomialPrefactor * Real.exp (separationRate * (n : ℝ) ^ 2) ≤
      spectralEdgeLower n := by
  unfold spectralEdgeLower quasipolynomialPrefactor
  rw [inv_spectral_eq_exp]
  have := exp_separationRate_absorbs n hn
  linarith

/-- At `R = 2^(46*n)`, the exponential lower-bound factor is literally a
power `R^(κ log R)`, with the fixed positive `κ` above. -/
theorem exponential_eq_paddedLength_rpow_log (n : ℕ) :
    Real.exp (separationRate * (n : ℝ) ^ 2) =
      (exponentialPaddedLength n : ℝ) ^
        (quasipolynomialRate *
          Real.log (exponentialPaddedLength n : ℝ)) := by
  have hRpos : 0 < (exponentialPaddedLength n : ℝ) := by positivity
  rw [Real.rpow_def_of_pos hRpos]
  have hcast :
      (exponentialPaddedLength n : ℝ) = (2 : ℝ) ^ (46 * n) := by
    norm_cast
  rw [hcast, Real.log_pow]
  unfold quasipolynomialRate
  congr 1
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  push_cast
  ring

/-- The padded separation in explicit edge-count form.  At
the padded length `R = 2^{46 n}`
the positive d-DNNF has at most `R` edges, and every DNNF for its complement
has at least `c · R^(κ log R)` edges for the fixed positive constants
`c = 1/256` and `κ`. -/
theorem separation_after_padding
    (n : ℕ) (hn : 25 ≤ n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ Cpad : NNFCircuit.{0, 0}
        (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
      Fintype.card
          (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)) =
        exponentialPaddedLength n ∧
      Cpad.IsDeterministicDNNF ∧
      Cpad.Computes (paddedEncodedOuterFunction ranks
        (by omega : 0 < n) a) ∧
      Cpad.edgeCount ≤ exponentialPaddedLength n ∧
      ∀ D : NNFCircuit.{0, 0}
          (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬paddedEncodedOuterFunction ranks
          (by omega : 0 < n) a x) →
        quasipolynomialPrefactor *
            (exponentialPaddedLength n : ℝ) ^
              (quasipolynomialRate *
                Real.log (exponentialPaddedLength n : ℝ)) ≤
          (D.edgeCount : ℝ) := by
  obtain ⟨ranks, a, C, _hdet, _hcomputes, _hsize, hpadded⟩ :=
    exists_candidate_padded_dDNNF_and_complement_DNNF_lower_bound n (by omega)
  have hn13 : 13 ≤ n := by omega
  have hcore := encodedInputCount_le_exponentialPaddedLength n hn13
  have h := hpadded (exponentialPaddedLength n) hcore
  dsimp only at h
  rcases h with ⟨hcard, hdet, hcomputes, hsize, hlower⟩
  let Cpad : NNFCircuit.{0, 0}
      (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)) :=
    C.padRightVariables
  refine ⟨ranks, a, Cpad, hcard, hdet, hcomputes,
    hsize.trans (positiveCircuitBound_le_exponentialPaddedLength n hn13), ?_⟩
  intro D hDNNF hDcomputes
  have hD := hlower D hDNNF hDcomputes
  rw [← exponential_eq_paddedLength_rpow_log]
  exact (quasipolynomial_le_spectralEdgeLower n hn).trans hD

/-- The padded separation with adversarial gate types in any universe.
Renumber the gates by `Fin D.size` to apply `separation_after_padding`. -/
theorem separation_after_padding_of_any_gates.{u}
    (n : ℕ) (hn : 25 ≤ n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ Cpad : NNFCircuit.{0, 0}
        (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
      Fintype.card
          (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)) =
        exponentialPaddedLength n ∧
      Cpad.IsDeterministicDNNF ∧
      Cpad.Computes (paddedEncodedOuterFunction ranks
        (by omega : 0 < n) a) ∧
      Cpad.edgeCount ≤ exponentialPaddedLength n ∧
      ∀ D : NNFCircuit.{0, u}
          (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬paddedEncodedOuterFunction ranks
          (by omega : 0 < n) a x) →
        quasipolynomialPrefactor *
            (exponentialPaddedLength n : ℝ) ^
              (quasipolynomialRate *
                Real.log (exponentialPaddedLength n : ℝ)) ≤
          (D.edgeCount : ℝ) := by
  obtain ⟨ranks, a, Cpad, hcard, hdet, hcomputes, hsize, hlower⟩ :=
    separation_after_padding n hn
  refine ⟨ranks, a, Cpad, hcard, hdet, hcomputes, hsize, ?_⟩
  intro D hDNNF hDcomputes
  have h := hlower D.toFinGates
    (NNFCircuit.isDNNF_toFinGates D hDNNF)
    (NNFCircuit.computes_toFinGates D _ hDcomputes)
  rwa [NNFCircuit.edgeCount_toFinGates] at h

/-- The unpadded separation measured in nodes, with a small d-DNNF and a lower bound for every DNNF for its negation. -/
@[tutorial_box "thm:tutorial-main"]
theorem negation_separation
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks hn a) ∧
      C.size ≤ positiveCircuitBound n + 1 ∧
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
        spectralNodeLower n ≤ (D.size : ℝ) := by
  obtain ⟨ranks, hwidth⟩ := every_term_short hn
  obtain ⟨a, hlower⟩ := DNNF_lower_bound_nodes n hn ranks
  obtain ⟨C, hdet, hcomputes, hsize⟩ := small_dDNNF_nodes ranks hn a hwidth
  refine ⟨ranks, a, C, hdet, hcomputes, ?_, hlower⟩
  exact hsize.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (card_thresholdTerm_le n)) 1)

/-- The padding corollary in node count. The positive circuit fits within
the padded length; taking a square root of the internal quasipolynomial
lower bound preserves its asymptotic form. -/
@[tutorial_box "cor:tutorial-padding"]
theorem nonclosure_under_negation
    (n : ℕ) (hn : 25 ≤ n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ Cpad : NNFCircuit.{0, 0}
        (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
      Fintype.card
          (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)) =
        exponentialPaddedLength n ∧
      Cpad.IsDeterministicDNNF ∧
      Cpad.Computes (paddedEncodedOuterFunction ranks (by omega : 0 < n) a) ∧
      Cpad.size ≤ exponentialPaddedLength n ∧
      ∀ D : NNFCircuit.{0, 0}
          (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬paddedEncodedOuterFunction ranks
          (by omega : 0 < n) a x) →
        Real.sqrt (quasipolynomialPrefactor *
            (exponentialPaddedLength n : ℝ) ^
              (quasipolynomialRate *
                Real.log (exponentialPaddedLength n : ℝ)) / 3) ≤
          (D.size : ℝ) := by
  obtain ⟨ranks, a, C, _hdet, _hcomputes, _hsize, hpadded⟩ :=
    exists_candidate_padded_dDNNF_and_complement_DNNF_lower_bound n (by omega)
  have hn13 : 13 ≤ n := by omega
  have hcore := encodedInputCount_le_exponentialPaddedLength n hn13
  have h := hpadded (exponentialPaddedLength n) hcore
  dsimp only at h
  rcases h with ⟨hcard, hdet, hcomputes, hsize, hlower⟩
  let Cpad : NNFCircuit.{0, 0}
      (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)) :=
    C.padRightVariables
  refine ⟨ranks, a, Cpad.prune, hcard,
    Cpad.prune_isDeterministicDNNF hdet, Cpad.prune_computes hcomputes, ?_, ?_⟩
  · calc
      Cpad.prune.size ≤ Cpad.prune.edgeCount + 1 := Cpad.prune_size_le
      _ ≤ positiveCircuitBound n + 1 :=
        Nat.add_le_add_right (Cpad.edgeCount_prune_le.trans hsize) 1
      _ ≤ 2 ^ (45 * n) + 1 :=
        Nat.add_le_add_right (positiveCircuitBound_le_two_pow n hn13) 1
      _ ≤ 2 ^ (45 * n + 1) := by
        have hpos : 0 < (2 : ℕ) ^ (45 * n) := by positivity
        rw [pow_succ]
        omega
      _ ≤ exponentialPaddedLength n :=
        pow_le_pow_right' (by norm_num) (by omega)
  · intro D hDNNF hDcomputes
    have hD : quasipolynomialPrefactor *
        (exponentialPaddedLength n : ℝ) ^
          (quasipolynomialRate * Real.log (exponentialPaddedLength n : ℝ)) ≤
        (D.dedup.edgeCount : ℝ) := by
      rw [← exponential_eq_paddedLength_rpow_log]
      exact (quasipolynomial_le_spectralEdgeLower n hn).trans
        (hlower D.dedup (D.dedup_isDNNF hDNNF) (D.dedup_computes hDcomputes))
    have hs := circuit_size_pos D
    have he := D.edgeCount_dedup_le
    have heNat : D.dedup.edgeCount ≤ 3 * D.size ^ 2 := by nlinarith
    have heR : (D.dedup.edgeCount : ℝ) ≤ 3 * (D.size : ℝ) ^ 2 := by
      exact_mod_cast heNat
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · linarith

end

end DDNNFNegation
