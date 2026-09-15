import DDNNFNegationCorollaries.UnambiguousOBDD
import DDNNFNegationConsequences.ArithmeticLayered
import DDNNFNegationConsequences.ArithmeticSupport

/-!
# Assignment polynomials

Paired assignment polynomials, their monotone circuits, and the support
translation used by the missing-monomial and probabilistic circuit corollaries.
-/

namespace DDNNFNegation

open Finset MvPolynomial
open Classical

/-! ## Paired variables and evaluation -/

section polynomials

variable {N : ℕ}

/-- `T_N = ∏_i (X_i + X̄_i)`. -/
noncomputable def fullPolynomial (N : ℕ) : MvPolynomial (Fin N × Bool) ℝ :=
  ∏ i : Fin N, (X (i, true) + X (i, false))

theorem fullPolynomial_eq_sum (N : ℕ) :
    fullPolynomial N = ∑ x : Fin N → Bool, assignmentMonomial x := by
  unfold fullPolynomial assignmentMonomial
  have h : ∀ i : Fin N, (X (i, true) + X (i, false) : MvPolynomial (Fin N × Bool) ℝ) =
      ∑ b : Bool, X (i, b) := by
    intro i
    rw [Fintype.sum_bool]
  simp_rw [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The point `X_i = x_i`, `X̄_i = 1 - x_i` of the paired indeterminates. -/
noncomputable def cubePoint (x : Fin N → ℝ) : Fin N × Bool → ℝ :=
  fun v ↦ if v.2 then x v.1 else 1 - x v.1

/-- At a Boolean point the cube point is the Boolean indicator point. -/
theorem cubePoint_bool (a : Fin N → Bool) :
    cubePoint (fun i ↦ if a i then (1 : ℝ) else 0) = boolPoint a := by
  funext ⟨i, b⟩
  simp only [cubePoint, boolPoint]
  cases b <;> cases hb : a i <;> simp

theorem eval_cubePoint_fullPolynomial (x : Fin N → ℝ) :
    eval (cubePoint x) (fullPolynomial N) = 1 := by
  unfold fullPolynomial
  rw [eval_prod]
  apply Finset.prod_eq_one
  intro i _
  simp only [eval_add, eval_X, cubePoint, ↓reduceIte, Bool.false_eq_true]
  ring

theorem eval_cubePoint_assignmentMonomial_nonneg (x : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (a : Fin N → Bool) :
    0 ≤ eval (cubePoint x) (assignmentMonomial a) := by
  unfold assignmentMonomial
  rw [eval_prod]
  apply Finset.prod_nonneg
  intro i _
  rw [eval_X]
  simp only [cubePoint]
  split_ifs
  · exact (hx i).1
  · linarith [(hx i).2]

theorem eval_boolPoint_sum (S : Finset (Fin N → Bool)) (x : Fin N → Bool) :
    eval (boolPoint x) (∑ y ∈ S, assignmentMonomial y) = if x ∈ S then 1 else 0 := by
  rw [eval_sum]
  simp_rw [eval_boolPoint_assignmentMonomial]
  exact Finset.sum_ite_eq' S x (fun _ ↦ (1 : ℝ))

/-! ### Positive reweightings -/

theorem mem_support_weightedSum {S : Finset (Fin N → Bool)} {c : (Fin N → Bool) → ℝ}
    {m : (Fin N × Bool) →₀ ℕ}
    (hm : m ∈ (∑ x ∈ S, C (c x) * assignmentMonomial x).support) :
    ∃ x ∈ S, m = assignmentExponent x := by
  by_contra hne
  push Not at hne
  rw [mem_support_iff, coeff_sum] at hm
  apply hm
  apply Finset.sum_eq_zero
  intro x hx
  rw [coeff_C_mul, assignmentMonomial_eq_monomial, coeff_monomial,
    if_neg (fun h ↦ hne x hx h.symm), mul_zero]

/-- Every monomial of a reweighted sum of assignment monomials has one
indicator per position. -/
theorem weightedSum_pair_degree {S : Finset (Fin N → Bool)} {c : (Fin N → Bool) → ℝ}
    (m : (Fin N × Bool) →₀ ℕ)
    (hm : m ∈ (∑ x ∈ S, C (c x) * assignmentMonomial x).support) (i : Fin N) :
    m (i, true) + m (i, false) ≤ 1 := by
  obtain ⟨x, _, rfl⟩ := mem_support_weightedSum hm
  rw [assignmentExponent_apply, assignmentExponent_apply]
  cases x i <;> simp

theorem eval_boolPoint_weightedSum (S : Finset (Fin N → Bool)) (c : (Fin N → Bool) → ℝ)
    (x : Fin N → Bool) :
    eval (boolPoint x) (∑ y ∈ S, C (c y) * assignmentMonomial y) =
      if x ∈ S then c x else 0 := by
  rw [eval_sum]
  simp_rw [eval_mul, eval_C, eval_boolPoint_assignmentMonomial, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' S x c

/-! ### The two lower-bound transfers -/

/-- A DNNF node lower bound for `¬L` is a gate lower bound for every
monotone circuit computing a positive reweighting of `∑_{¬L a} m_a`. -/
theorem reweighted_lower_bound_of_dnnf (L : (Fin N → Bool) → Prop) (bound : ℝ)
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin N), D.IsDNNF →
      D.Computes (fun x ↦ ¬L x) → bound ≤ (D.size : ℝ))
    (A : ArithCircuit.{0, 0} (Fin N × Bool)) (hmono : A.IsMonotone)
    (c : (Fin N → Bool) → ℝ) (hc : ∀ x, 0 < c x)
    (hA : A.Computes (∑ x ∈ univ.filter (fun x ↦ ¬L x), C (c x) * assignmentMonomial x)) :
    bound ≤ (A.size : ℝ) := by
  have hA' : A.poly A.output = _ := hA
  have hout : ∀ m ∈ (A.poly A.output).support, ∀ i, m (i, true) + m (i, false) ≤ 1 := by
    intro m hm i
    rw [hA'] at hm
    exact weightedSum_pair_degree m hm i
  have hval : ∀ x, 0 < A.boolValue x ↔ ¬L x := by
    intro x
    unfold ArithCircuit.boolValue
    rw [hA', eval_boolPoint_weightedSum]
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with h
    · exact ⟨fun h0 ↦ absurd h0 (lt_irrefl (0 : ℝ)), fun h' ↦ absurd h h'⟩
    · exact ⟨fun _ ↦ h, fun _ ↦ hc x⟩
  have h := hlower A.prunedDNNF A.prunedDNNF_isDNNF (A.prunedDNNF_computes hmono hout _ hval)
  rwa [ArithCircuit.prunedDNNF_size] at h

/-- A DNNF node lower bound for `¬L` is a gate lower bound for every
monotone circuit with disjoint position sets at its products whose
support on the Boolean points is `¬L`. -/
theorem support_lower_bound_of_dnnf (L : (Fin N → Bool) → Prop) (bound : ℝ)
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin N), D.IsDNNF →
      D.Computes (fun x ↦ ¬L x) → bound ≤ (D.size : ℝ))
    (A : ArithCircuit.{0, 0} (Fin N × Bool)) (hmono : A.IsMonotone)
    (hdisj : A.IsPairDisjoint) (hval : ∀ x, 0 < A.boolValue x ↔ ¬L x) :
    bound ≤ (A.size : ℝ) := by
  have h := hlower (A.toDNNF hmono) (A.toDNNF_isDNNF hmono hdisj)
    (A.toDNNF_computes hmono _ hval)
  rwa [ArithCircuit.toDNNF_size] at h

/-! ### The circuit for `T_N` -/

variable (σ : Equiv.Perm (Fin N))

/-- The one-state layered circuit: `∏_k (X_{σ k} + X̄_{σ k})` along the
order `σ`. -/
noncomputable def fullCircuit : ArithCircuit (Fin N × Bool) :=
  LayeredArith.circuit σ (fun _ _ _ ↦ ()) (fun _ ↦ true) ()

theorem fullCircuit_poly_output :
    (fullCircuit σ).poly (fullCircuit σ).output = fullPolynomial N := by
  unfold fullCircuit
  rw [LayeredArith.circuit_poly_output, LayeredArith.layerPoly_zero, fullPolynomial_eq_sum]
  simp

theorem fullCircuit_size : (fullCircuit σ).size = 5 * N + 1 := by
  unfold fullCircuit
  rw [LayeredArith.circuit_size, Fintype.card_unit]
  ring

theorem fullCircuit_isMonotone : (fullCircuit σ).IsMonotone :=
  LayeredArith.circuit_isMonotone _ _ _ _

theorem fullCircuit_isSetMultilinear : (fullCircuit σ).IsSetMultilinear :=
  LayeredArith.circuit_isSetMultilinear _ _ _ _

theorem fullCircuit_isRightLinear : (fullCircuit σ).IsRightLinear (fun y ↦ (σ.symm y).val) :=
  LayeredArith.circuit_isRightLinear _ _ _ _

end polynomials

/-! ## The encoded hard function -/

section encoded

variable {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
  (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))

/-- `P_n = ∑_{L_n x} m_x`. -/
noncomputable def hardPolynomial : MvPolynomial (Fin (encodedInputCount n) × Bool) ℝ :=
  ∑ x ∈ univ.filter (fun x ↦ hardFunction ranks hn a x), assignmentMonomial x

/-- `Q_n = ∑_{¬L_n x} m_x`. -/
noncomputable def complementPolynomial : MvPolynomial (Fin (encodedInputCount n) × Bool) ℝ :=
  ∑ x ∈ univ.filter (fun x ↦ ¬hardFunction ranks hn a x), assignmentMonomial x

/-- `Q_n = T_n - P_n`. -/
theorem complementPolynomial_eq :
    complementPolynomial ranks hn a =
      fullPolynomial (encodedInputCount n) - hardPolynomial ranks hn a := by
  rw [fullPolynomial_eq_sum, eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Substituting `X̄_i = 1 - X_i` in the assignment polynomial gives `hardCubeFunction`. -/
noncomputable def hardCubeFunction (x : Fin (encodedInputCount n) → ℝ) : ℝ :=
  eval (cubePoint x) (hardPolynomial ranks hn a)

theorem one_sub_hardCubeFunction (x : Fin (encodedInputCount n) → ℝ) :
    1 - hardCubeFunction ranks hn a x = eval (cubePoint x) (complementPolynomial ranks hn a) := by
  rw [complementPolynomial_eq, map_sub, eval_cubePoint_fullPolynomial]
  rfl

theorem hardCubeFunction_nonneg (x : Fin (encodedInputCount n) → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : 0 ≤ hardCubeFunction ranks hn a x := by
  unfold hardCubeFunction hardPolynomial
  rw [eval_sum]
  exact Finset.sum_nonneg fun y _ ↦ eval_cubePoint_assignmentMonomial_nonneg x hx y

theorem hardCubeFunction_le_one (x : Fin (encodedInputCount n) → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : hardCubeFunction ranks hn a x ≤ 1 := by
  have h : 0 ≤ 1 - hardCubeFunction ranks hn a x := by
    rw [one_sub_hardCubeFunction]
    unfold complementPolynomial
    rw [eval_sum]
    exact Finset.sum_nonneg fun y _ ↦ eval_cubePoint_assignmentMonomial_nonneg x hx y
  linarith

/-- At Boolean points, `hardCubeFunction` is the indicator of `L_n`. -/
theorem hardCubeFunction_bool (x : Fin (encodedInputCount n) → Bool) :
    hardCubeFunction ranks hn a (fun i ↦ if x i then 1 else 0) =
      if hardFunction ranks hn a x then 1 else 0 := by
  unfold hardCubeFunction hardPolynomial
  rw [cubePoint_bool, eval_boolPoint_sum]
  simp only [mem_filter, mem_univ, true_and]

/-- Any arithmetic circuit agreeing with `1 - hardCubeFunction` throughout
`[0, 1]^N` is positive on precisely the Boolean assignments outside `L_n`. -/
theorem boolValue_pos_iff_of_cube (A : ArithCircuit (Fin (encodedInputCount n) × Bool))
    (hA : ∀ x : Fin (encodedInputCount n) → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      eval (cubePoint x) (A.poly A.output) = 1 - hardCubeFunction ranks hn a x)
    (x : Fin (encodedInputCount n) → Bool) :
    0 < A.boolValue x ↔ ¬hardFunction ranks hn a x := by
  have hx := hA (fun i ↦ if x i then 1 else 0) (fun i ↦ by split_ifs <;> norm_num)
  rw [hardCubeFunction_bool, cubePoint_bool] at hx
  unfold ArithCircuit.boolValue
  rw [hx]
  split_ifs with h <;> simp [h]

/-! ### The term circuits and their sum -/

variable (σ : Equiv.Perm (Fin (encodedInputCount n)))

/-- The layered polynomial circuit of the term OBDD of `T`, read in the
order `σ`. -/
noncomputable def termCircuit (T : ThresholdTerm n) :
    ArithCircuit (Fin (encodedInputCount n) × Bool) :=
  LayeredArith.circuit σ (encodedTermTransition ranks hn (a ∘ σ) T)
    (encodedTermAcceptBool ranks hn T) 0

theorem encodedTermAcceptBool_eq_true (T : ThresholdTerm n)
    (s : encodedTermSupport ranks hn T → GadgetVector) :
    encodedTermAcceptBool ranks hn T s = true ↔ encodedTermStateAccepts ranks hn T s := by
  by_cases h : encodedTermStateAccepts ranks hn T s <;> simp [encodedTermAcceptBool, h]

theorem termCircuit_poly_output (T : ThresholdTerm n) :
    (termCircuit ranks hn a σ T).poly (termCircuit ranks hn a σ T).output =
      ∑ x ∈ univ.filter (fun x ↦ encodedTermStateAccepts ranks hn T
        (encodedTermState ranks hn a T x)), assignmentMonomial x := by
  unfold termCircuit
  rw [LayeredArith.circuit_poly_output, LayeredArith.layerPoly_zero]
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  apply Finset.filter_congr
  intro x _
  rw [encodedTermRun_eq_state, encodedTermState_comp_equiv, encodedTermAcceptBool_eq_true]

theorem termCircuit_size (T : ThresholdTerm n) :
    (termCircuit ranks hn a σ T).size =
      (encodedInputCount n + 1) * 16 ^ (encodedTermSupport ranks hn T).card +
        (encodedInputCount n * 16 ^ (encodedTermSupport ranks hn T).card * 2 +
          encodedInputCount n * 2) := by
  unfold termCircuit
  rw [LayeredArith.circuit_size, card_encodedTermState]

theorem termCircuit_size_le (T : ThresholdTerm n)
    (hw : (termSigned ranks hn T).positive.card +
      (termSigned ranks hn T).negative.card ≤ 10 * n) :
    (termCircuit ranks hn a σ T).size ≤
      (3 * encodedInputCount n + 1) * 16 ^ (10 * n) + 2 * encodedInputCount n := by
  rw [termCircuit_size]
  have h := card_encodedTermSupport_le ranks hn T hw
  have hpow : 16 ^ (encodedTermSupport ranks hn T).card ≤ 16 ^ (10 * n) :=
    Nat.pow_le_pow_right (by norm_num) h
  nlinarith [Nat.mul_le_mul_left (3 * encodedInputCount n + 1) hpow]

include hn in
theorem card_thresholdTerm_pos : 0 < Fintype.card (ThresholdTerm n) :=
  Fintype.card_pos_iff.mpr ⟨⟨⟨⟨0, hn⟩, univ, ⟨⟨0, hn⟩, mem_univ _⟩⟩,
    by simp only [Finset.card_univ, Fintype.card_fin]; omega⟩⟩

/-- The terms enumerated as `Fin (m + 1)`, for the chain construction. -/
noncomputable def termIndex :
    ThresholdTerm n ≃ Fin (Fintype.card (ThresholdTerm n) - 1 + 1) :=
  Fintype.equivFinOfCardEq (Nat.sub_add_cancel (card_thresholdTerm_pos hn)).symm

/-- The circuit for `P_n` in the order `σ`: the sum of the term circuits. -/
noncomputable def hardCircuit : ArithCircuit (Fin (encodedInputCount n) × Bool) :=
  ArithCircuit.chain (termIndex hn) (fun T ↦ termCircuit ranks hn a σ T)

theorem sum_ite_unique {ι M : Type*} [Fintype ι] [AddCommMonoid M] (p : ι → Prop)
    (huniq : ∀ T U, p T → p U → T = U) (c : M) :
    ∑ T, (if p T then c else 0) = if ∃ T, p T then c else 0 := by
  split_ifs with h
  · obtain ⟨T0, hT0⟩ := h
    rw [Finset.sum_eq_single T0]
    · rw [if_pos hT0]
    · intro U _ hU
      rw [if_neg (fun hpU ↦ hU (huniq U T0 hpU hT0))]
    · intro h
      exact absurd (mem_univ T0) h
  · push Not at h
    exact Finset.sum_eq_zero (fun T _ ↦ if_neg (h T))

theorem hardCircuit_poly_output :
    (hardCircuit ranks hn a σ).poly (hardCircuit ranks hn a σ).output =
      hardPolynomial ranks hn a := by
  unfold hardCircuit
  rw [ArithCircuit.chain_poly_output]
  simp_rw [termCircuit_poly_output ranks hn a σ, Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold hardPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  refine (sum_ite_unique _ (fun T U hT hU ↦ encodedTermStates_unambiguous ranks hn a x hT hU)
    _).trans ?_
  rw [hardFunction_iff_exists_termStateAccepts]
  split_ifs <;> rfl

theorem hardCircuit_isMonotone : (hardCircuit ranks hn a σ).IsMonotone :=
  ArithCircuit.chain_isMonotone _ _ (fun _ ↦ LayeredArith.circuit_isMonotone _ _ _ _)

theorem hardCircuit_isRightLinear :
    (hardCircuit ranks hn a σ).IsRightLinear (fun y ↦ (σ.symm y).val) :=
  ArithCircuit.chain_isRightLinear _ (fun _ ↦ LayeredArith.circuit_isRightLinear _ _ _ _)

theorem hardCircuit_isSetMultilinear : (hardCircuit ranks hn a σ).IsSetMultilinear :=
  ArithCircuit.chain_isSetMultilinear (fun _ ↦ LayeredArith.circuit_isSetMultilinear _ _ _ _)
    univ (fun _ ↦ LayeredArith.positions_layerVars_zero σ)

/-- The explicit gate bound of the circuit for `P_n`: at most `n 2^n` terms,
each with at most `(3 N + 1) 16^{10 n} + 2 N` gates, plus one sum gate per
term. -/
abbrev arithmeticCircuitBound (n : ℕ) : ℕ :=
  n * 2 ^ n * ((3 * encodedInputCount n + 1) * 16 ^ (10 * n) + 2 * encodedInputCount n + 1)

theorem arithmeticCircuitBound_le_positiveCircuitBound (n : ℕ) :
    arithmeticCircuitBound n ≤ positiveCircuitBound n := by
  unfold arithmeticCircuitBound positiveCircuitBound
  apply Nat.mul_le_mul_left
  have hE : 1 ≤ 16 ^ (10 * n) := Nat.one_le_pow _ _ (by norm_num)
  nlinarith [Nat.mul_le_mul_left (encodedInputCount n) hE, hE]

theorem arithmeticCircuitBound_le_two_pow (n : ℕ) (hn : 13 ≤ n) :
    arithmeticCircuitBound n ≤ 2 ^ (45 * n) :=
  (arithmeticCircuitBound_le_positiveCircuitBound n).trans (positiveCircuitBound_le_two_pow n hn)

theorem hardCircuit_size_le
    (hw : ∀ T : ThresholdTerm n, (termSigned ranks hn T).positive.card +
      (termSigned ranks hn T).negative.card ≤ 10 * n) :
    (hardCircuit ranks hn a σ).size ≤ arithmeticCircuitBound n := by
  unfold hardCircuit
  rw [ArithCircuit.chain_size]
  calc ∑ T : ThresholdTerm n, (termCircuit ranks hn a σ T).size +
        (Fintype.card (ThresholdTerm n) - 1 + 1)
      ≤ ∑ _T : ThresholdTerm n,
          ((3 * encodedInputCount n + 1) * 16 ^ (10 * n) + 2 * encodedInputCount n) +
          Fintype.card (ThresholdTerm n) :=
        Nat.add_le_add (Finset.sum_le_sum fun T _ ↦ termCircuit_size_le ranks hn a σ T (hw T))
          (le_of_eq (Nat.sub_add_cancel (card_thresholdTerm_pos hn)))
    _ = Fintype.card (ThresholdTerm n) *
          ((3 * encodedInputCount n + 1) * 16 ^ (10 * n) + 2 * encodedInputCount n + 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring
    _ ≤ arithmeticCircuitBound n :=
        Nat.mul_le_mul_right _ (card_thresholdTerm_le n)

end encoded

end DDNNFNegation
