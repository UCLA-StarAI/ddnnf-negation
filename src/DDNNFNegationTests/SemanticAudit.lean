import DDNNFNegation.Separation

/-!
# Semantic checks for the separation

These checks relate the encoded Boolean function, matrix zeros, partial
sums, fibers, circuit construction, and padding bound. They use the
production definitions and theorems, so changes that break these
correspondences also break the checks.
-/

namespace DDNNFNegation.SemanticAudit
open Finset

noncomputable section

/-! ## Function and sign conventions -/

/-- The encoded Boolean function is literally `F_n` at the subset sum:
the outer DNF applied to the bits `Q` reads off the subset sum. -/
theorem audit_encodedFunction_is_exact_pullback
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {ι : Type*} [Fintype ι]
    (a : ι → ((Fin n × Fin n) → GadgetVector)) (x : ι → Bool) :
    hardFunction ranks hn a x ↔
      outerDNF ranks hn (gadgetBits (subsetSum a x)) :=
  Iff.rfl

/-- Property (b) of the matrix `K`, with the sign convention pinned: the
entry at row `u` and column `v` is positive only if `F_n(u + v) = 1`. -/
theorem audit_outerMatrix_supported_on_one_inputs
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (u v : (Fin n × Fin n) → GadgetVector) (hpos : 0 < outerMatrix n u v) :
    outerFunction ranks hn (u + v) :=
  outerMatrix_pos_imp_outerFunction ranks hn u v hpos

/-! ## Boolean assignments and rectangles -/

/-- Splitting an assignment at an arbitrary set of Boolean positions
preserves the subset sum exactly, at the sixteen-letter grid alphabet. -/
theorem audit_arbitraryBitPartition_adds_partialSums
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ((Fin n × Fin n) → GadgetVector)) (S : Finset ι) (x : ι → Bool) :
    subsetSum a x =
      partialSubsetSum a S (fun i => x i) + partialSubsetSum a Sᶜ (fun i => x i) :=
  subsetSum_partition a S x

/-- Intersecting an ordinary Boolean rectangle with the zero fiber is not an
approximation: it has exactly the cardinality of the set of zero pairs used
by the group argument. -/
theorem audit_zeroFiber_rectangle_cardinality_is_exact
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ((Fin n × Fin n) → GadgetVector)) (R : BooleanRectangle ι) :
    (R.assignments ∩ zeroFiber a).card =
      (rectangleZeroPairs (partialSubsetSum a R.cut) (partialSubsetSum a R.cutᶜ)
        R.left R.right).card :=
  card_inter_zeroFiber_eq a R

/-- On a zero rectangle, `F_n` vanishes at the sum of any two common partial sums, supplying the zero-square hypothesis. -/
theorem audit_zeroRectangle_gives_commonPartialSums_hypothesis
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    {X Y : Type*}
    (L : X → ((Fin n × Fin n) → GadgetVector))
    (R : Y → ((Fin n × Fin n) → GadgetVector))
    (A : Finset X) (C : Finset Y)
    (hzero : ∀ x ∈ A, ∀ y ∈ C,
      ¬outerFunction ranks hn (L x + R y)) :
    ∀ σ ∈ commonPartialSums L R A C, ∀ τ ∈ commonPartialSums L R A C,
      ¬outerFunction ranks hn (σ + τ) :=
  commonPartialSums_sums_zero L R A C ranks hn hzero

/-! ## Encoder bookkeeping

The paper states the index bound as `[G : G_S] ≤ 8` and proves it
by `𝔽₂`-linear algebra, through `[G : G_S] = 2^{4n² - dim G_S}`.  The audit
below pins the index to the dimension count, so the machine-checked
statement is the prose statement. -/

/-- The index bound in its prose form: the quotient by the subgroup the
columns of `S` generate has at most eight elements exactly when the span of
those columns has codimension at most three. -/
theorem audit_index_bound_is_codimension_count
    {ι G : Type*} [Fintype G] [AddCommGroup G] [Module (ZMod 2) G]
    (a : ι → G) (S : Finset ι) :
    Nat.card (G ⧸ partialImage a S) ≤ 8 ↔
      Module.finrank (ZMod 2) G ≤ Module.finrank (ZMod 2) (columnSpan a S) + 3 := by
  rw [index_eq_two_pow, show (8 : ℕ) = 2 ^ 3 by norm_num,
    Nat.pow_le_pow_iff_right (by norm_num)]
  have := Submodule.finrank_le (R := ZMod 2) (M := G) (columnSpan a S)
  omega

/-- The tutorial's fiber count behind exact uniformity, at the grid
alphabet: the fiber of the partial-sum map over any point of `G_S`, times
`|G_S|`, is exactly `2^{|S|}`. -/
theorem audit_fiber_count
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ((Fin n × Fin n) → GadgetVector)) (S : Finset ι)
    {z : (Fin n × Fin n) → GadgetVector} (hz : z ∈ partialImage a S) :
    (finiteMapFiber (partialSubsetSum a S) z).card * Nat.card (partialImage a S) =
      2 ^ S.card :=
  equal_fiber_sizes gridVector_add_self a S hz

/-! ## Circuit interfaces -/

/-- The positive circuit computes the very same encoded function that the
lower-bound theorem complements. -/
theorem audit_positiveCircuit_computes_same_function
    {n bitCount : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    (encodedOuterDNNF ranks hn a).Computes
      (hardFunction ranks hn a) :=
  encodedOuterDNNF_computes ranks hn a

/-! ## Padding and restriction -/

/-- For `n ≥ 25`, the quasipolynomial expression at padded length `2^(46*n)` is at most the internal spectral edge bound. -/
theorem audit_spectral_lower_is_explicitly_quasipolynomial (n : ℕ)
    (hn : 25 ≤ n) :
    quasipolynomialPrefactor *
        (exponentialPaddedLength n : ℝ) ^
          (quasipolynomialRate *
            Real.log (exponentialPaddedLength n : ℝ)) ≤
      spectralEdgeLower n := by
  rw [← exponential_eq_paddedLength_rpow_log]
  exact quasipolynomial_le_spectralEdgeLower n hn

/-- Both constants in the explicit quasipolynomial lower bound are fixed and
strictly positive. -/
theorem audit_quasipolynomial_constants_positive :
    0 < quasipolynomialPrefactor ∧ 0 < quasipolynomialRate :=
  ⟨quasipolynomialPrefactor_pos, quasipolynomialRate_pos⟩

/-! ## Closed endpoint -/

/-- The endpoint fixes the ranks, encoder, and positive d-DNNF before it
quantifies over every DNNF for the complement of that same function. -/
theorem audit_closed_finite_candidate_endpoint
    (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (60 * (n * n)) →
        ((Fin n × Fin n) → GadgetVector),
    ∃ C : NNFCircuit.{0, 0} (Fin (60 * (n * n))),
      C.IsDeterministicDNNF ∧
      C.Computes (hardFunction ranks
        (by omega : 0 < n) a) ∧
      C.edgeCount ≤
        (n * 2 ^ n) * (1 + 10 * ((60 * (n * n) + 1) * 16 ^ (10 * n))) ∧
      ∀ D : NNFCircuit.{0, 0} (Fin (60 * (n * n))),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks
          (by omega : 0 < n) a x) →
        1 / (128 * (2 / 3 : ℝ) ^ ((n : ℝ) ^ 2 / 30)) - 1 / 2 ≤
          (D.edgeCount : ℝ) :=
  negation_separation_edges n hn

end

end DDNNFNegation.SemanticAudit
