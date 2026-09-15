import DDNNFNegationCorollaries.AssignmentPolynomials
import DDNNFNegationConsequences.ArithmeticGenerating

/-!
# Missing multilinear monomials

Substituting one for the negative-literal indeterminates gives a
small monotone circuit for the generating polynomial of the hard
function. The support translation gives the lower bound for its
missing monomials, regardless of their positive coefficients.
-/

namespace DDNNFNegation

open Finset MvPolynomial
open Classical

section unpairedPolynomials

variable {N : ℕ}

/-- The multilinear monomial `∏_{i : x i} X_i` of an assignment. -/
noncomputable def indicatorMonomial (x : Fin N → Bool) : MvPolynomial (Fin N) ℝ :=
  ∏ i, if x i then X i else 1

theorem indicatorMonomial_eq_monomial (x : Fin N → Bool) :
    indicatorMonomial x = monomial (selected x univ) 1 := by
  have h : ∀ i, (if x i then X i else (1 : MvPolynomial (Fin N) ℝ)) =
      monomial (Finsupp.single i (if x i then 1 else 0)) 1 := by
    intro i
    cases x i
    · simp [monomial_zero']
    · simp [X]
  unfold indicatorMonomial
  simp_rw [h]
  rw [← monomial_sum_one]
  have hsum : (∑ i, Finsupp.single i (if x i then 1 else 0)) = selected x univ := by
    ext j
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  rw [hsum]

/-- `∏_i (1 + X_i)`. -/
noncomputable def fullGenerating (N : ℕ) : MvPolynomial (Fin N) ℝ :=
  ∏ i, (1 + X i)

theorem fullGenerating_eq_sum (N : ℕ) :
    fullGenerating N = ∑ x : Fin N → Bool, indicatorMonomial x := by
  unfold fullGenerating indicatorMonomial
  have h : ∀ i : Fin N, (1 + X i : MvPolynomial (Fin N) ℝ) =
      ∑ b : Bool, if b then X i else 1 := by
    intro i
    rw [Fintype.sum_bool]
    simp [add_comm]
  simp_rw [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The coefficients of a sum of distinct multilinear monomials are `0` or
`1`. -/
theorem coeff_sum_indicatorMonomial (S : Finset (Fin N → Bool)) (m : Fin N →₀ ℕ) :
    coeff m (∑ x ∈ S, indicatorMonomial x) =
      if ∃ x ∈ S, m = selected x univ then 1 else 0 := by
  simp_rw [indicatorMonomial_eq_monomial]
  rw [coeff_sum]
  simp_rw [coeff_monomial]
  split_ifs with h
  · obtain ⟨x₀, hx₀, rfl⟩ := h
    rw [Finset.sum_eq_single x₀]
    · simp
    · intro x _ hx
      rw [if_neg]
      intro heq
      exact hx (selected_univ_injective heq)
    · intro h
      exact absurd hx₀ h
  · apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    intro heq
    exact h ⟨x, hx, heq.symm⟩

theorem coeff_sum_indicatorMonomial_zero_or_one (S : Finset (Fin N → Bool)) (m : Fin N →₀ ℕ) :
    coeff m (∑ x ∈ S, indicatorMonomial x) = 0 ∨
      coeff m (∑ x ∈ S, indicatorMonomial x) = 1 := by
  rw [coeff_sum_indicatorMonomial]
  split_ifs <;> simp

theorem mem_support_sum_indicatorMonomial (S : Finset (Fin N → Bool)) (m : Fin N →₀ ℕ) :
    m ∈ (∑ x ∈ S, indicatorMonomial x).support ↔ ∃ x ∈ S, m = selected x univ := by
  rw [mem_support_iff, coeff_sum_indicatorMonomial]
  split_ifs with h <;> simp [h]

/-- The monomials of a positively weighted sum of multilinear monomials. -/
theorem mem_support_weightedIndicatorSum (S : Finset (Fin N → Bool))
    (c : (Fin N → Bool) → ℝ) (hc : ∀ x ∈ S, 0 < c x) (m : Fin N →₀ ℕ) :
    m ∈ (∑ x ∈ S, C (c x) * indicatorMonomial x).support ↔ ∃ x ∈ S, m = selected x univ := by
  simp_rw [indicatorMonomial_eq_monomial, C_mul_monomial, mul_one]
  rw [mem_support_iff, coeff_sum]
  simp_rw [coeff_monomial]
  constructor
  · intro h
    by_contra hne
    apply h
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    intro heq
    exact hne ⟨x, hx, heq.symm⟩
  · rintro ⟨x₀, hx₀, rfl⟩
    rw [Finset.sum_eq_single x₀]
    · simpa using (hc x₀ hx₀).ne'
    · intro x _ hx
      rw [if_neg]
      intro heq
      exact hx (selected_univ_injective heq)
    · intro h
      exact absurd hx₀ h

/-- The lower bound transferred to monotone circuits whose output monomials
are exactly the multilinear monomials of the assignments outside `L`. -/
theorem generating_lower_bound_of_dnnf (L : (Fin N → Bool) → Prop) (bound : ℝ)
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin N), D.IsDNNF →
      D.Computes (fun x ↦ ¬L x) → bound ≤ (D.size : ℝ))
    (A : ArithCircuit.{0, 0} (Fin N)) (hmono : A.IsMonotone)
    (hsupp : ∀ m, m ∈ (A.poly A.output).support ↔ ∃ x, ¬L x ∧ m = selected x univ) :
    bound ≤ ((A.size * (2 * N + 5) + 2 * N + 2 : ℕ) : ℝ) := by
  have hout : ∀ m ∈ (A.poly A.output).support, ∀ i, m i ≤ 1 := by
    intro m hm i
    obtain ⟨x, _, rfl⟩ := (hsupp m).mp hm
    exact selected_le_one x univ i
  have h := hlower A.padDNNF A.padDNNF_isDNNF ?_
  · rwa [ArithCircuit.padDNNF_size] at h
  · intro x
    rw [A.padDNNF_computes hmono hout x]
    show selected x univ ∈ (A.poly A.output).support ↔ ¬L x
    rw [hsupp]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rwa [selected_univ_injective hxy]
    · intro h
      exact ⟨x, h, rfl⟩

/-- The same bound for a positive reweighting of `∑_{¬L x} ∏_{i : x i} X_i`. -/
theorem reweighted_generating_lower_bound_of_dnnf (L : (Fin N → Bool) → Prop) (bound : ℝ)
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin N), D.IsDNNF →
      D.Computes (fun x ↦ ¬L x) → bound ≤ (D.size : ℝ))
    (A : ArithCircuit.{0, 0} (Fin N)) (hmono : A.IsMonotone)
    (c : (Fin N → Bool) → ℝ) (hc : ∀ x, 0 < c x)
    (hA : A.Computes (∑ x ∈ univ.filter (fun x ↦ ¬L x), C (c x) * indicatorMonomial x)) :
    bound ≤ ((A.size * (2 * N + 5) + 2 * N + 2 : ℕ) : ℝ) := by
  have hA' : A.poly A.output = _ := hA
  apply generating_lower_bound_of_dnnf L bound hlower A hmono
  intro m
  rw [hA', mem_support_weightedIndicatorSum _ _ (fun x _ ↦ hc x)]
  simp [mem_filter]

/-! ### The substitution `X̄_i ↦ 1` -/

/-- The substitution `X_i ↦ X_i`, `X̄_i ↦ 1`. -/
noncomputable def barOne : Fin N × Bool → MvPolynomial (Fin N) ℝ :=
  fun v ↦ if v.2 then X v.1 else 1

theorem aeval_barOne_assignmentMonomial (x : Fin N → Bool) :
    aeval barOne (assignmentMonomial x) = indicatorMonomial x := by
  unfold assignmentMonomial indicatorMonomial
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [aeval_X]; rfl

theorem aeval_barOne_fullPolynomial (N : ℕ) :
    aeval barOne (fullPolynomial N) = fullGenerating N := by
  unfold fullPolynomial fullGenerating
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_add, aeval_X, aeval_X]
  simp [barOne, add_comm]

namespace ArithNode

variable {Gate : Type*}

/-- The node after the substitution: `X̄_i` becomes the constant `1`. -/
def substituteBar : ArithNode (Fin N × Bool) Gate → ArithNode (Fin N) Gate
  | const c => const c
  | var (i, b) => if b then var i else const 1
  | add left right => add left right
  | mul left right => mul left right

theorem substituteBar_isChild {node : ArithNode (Fin N × Bool) Gate} {c : Gate}
    (h : node.substituteBar.IsChild c) : node.IsChild c := by
  cases node with
  | const _ => exact absurd h id
  | var v =>
      obtain ⟨i, b⟩ := v
      cases b <;> simp [substituteBar, IsChild] at h
  | add _ _ => exact h
  | mul _ _ => exact h

end ArithNode

namespace ArithCircuit

variable (C : ArithCircuit (Fin N × Bool))

/-- The circuit after the substitution `X̄_i ↦ 1`: same gates, same size. -/
noncomputable def substituteBar : ArithCircuit (Fin N) where
  Gate := C.Gate
  gateFintype := C.gateFintype
  gateDecidableEq := C.gateDecidableEq
  output := C.output
  node g := (C.node g).substituteBar
  rank := C.rank
  child_rank g c h := C.child_rank g c (ArithNode.substituteBar_isChild h)
  poly g := aeval barOne (C.poly g)
  poly_eq g := by
    rw [C.poly_eq g]
    cases C.node g with
    | const c =>
        simp only [ArithNode.eval, ArithNode.substituteBar]
        rw [aeval_C, algebraMap_eq]
    | var v =>
        obtain ⟨i, b⟩ := v
        simp only [ArithNode.eval, ArithNode.substituteBar]
        rw [aeval_X]
        cases b <;> simp [barOne]
    | add left right => simp only [ArithNode.eval, ArithNode.substituteBar, map_add]
    | mul left right => simp only [ArithNode.eval, ArithNode.substituteBar, map_mul]
  vars g := positions ((C.vars g).filter fun v ↦ v.2 = true)
  vars_eq g := by
    rw [C.vars_eq g]
    cases C.node g with
    | const c => simp [ArithNode.Vars, ArithNode.substituteBar, positions]
    | var v =>
        obtain ⟨i, b⟩ := v
        simp only [ArithNode.Vars, ArithNode.substituteBar, Finset.filter_singleton]
        cases b <;> simp [positions]
    | add left right =>
        simp only [ArithNode.Vars, ArithNode.substituteBar, Finset.filter_union,
          positions_union]
    | mul left right =>
        simp only [ArithNode.Vars, ArithNode.substituteBar, Finset.filter_union,
          positions_union]

@[simp] theorem substituteBar_size : C.substituteBar.size = C.size := rfl

theorem substituteBar_computes {p : MvPolynomial (Fin N × Bool) ℝ} (h : C.Computes p) :
    C.substituteBar.Computes (aeval barOne p) := by
  have h' : C.poly C.output = p := h
  show aeval barOne (C.poly C.output) = _
  rw [h']

theorem substituteBar_isMonotone (hmono : C.IsMonotone) : C.substituteBar.IsMonotone := by
  intro g c h
  change (C.node g).substituteBar = .const c at h
  cases hnode : C.node g with
  | const c' =>
      rw [hnode] at h
      cases h
      exact hmono g c hnode
  | var v =>
      obtain ⟨i, b⟩ := v
      rw [hnode] at h
      cases b
      · simp only [ArithNode.substituteBar, Bool.false_eq_true, if_false,
          ArithNode.const.injEq] at h
        rw [← h]
        norm_num
      · simp [ArithNode.substituteBar] at h
  | add _ _ =>
      rw [hnode] at h
      cases h
  | mul _ _ =>
      rw [hnode] at h
      cases h

/-- Disjoint position sets at products become disjoint variable sets. -/
theorem substituteBar_isSyntacticallyMultilinear (hdisj : C.IsPairDisjoint) :
    C.substituteBar.IsSyntacticallyMultilinear := by
  intro g l r h
  change (C.node g).substituteBar = .mul l r at h
  cases hnode : C.node g with
  | const _ =>
      rw [hnode] at h
      cases h
  | var v =>
      obtain ⟨i, b⟩ := v
      rw [hnode] at h
      cases b <;> simp [ArithNode.substituteBar] at h
  | add _ _ =>
      rw [hnode] at h
      cases h
  | mul l' r' =>
      rw [hnode] at h
      cases h
      have := hdisj g _ _ hnode
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image (Finset.filter_subset _ _))
        (Finset.disjoint_of_subset_right (Finset.image_subset_image (Finset.filter_subset _ _))
          this)

end ArithCircuit

end unpairedPolynomials

section encodedGenerating

variable {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
  (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))

/-- `G_n = ∑_{L_n x} ∏_{i : x i} X_i`. -/
noncomputable def hardGenerating : MvPolynomial (Fin (encodedInputCount n)) ℝ :=
  ∑ x ∈ univ.filter (fun x ↦ hardFunction ranks hn a x), indicatorMonomial x

/-- `H_n = ∑_{¬L_n x} ∏_{i : x i} X_i`. -/
noncomputable def complementGenerating : MvPolynomial (Fin (encodedInputCount n)) ℝ :=
  ∑ x ∈ univ.filter (fun x ↦ ¬hardFunction ranks hn a x), indicatorMonomial x

theorem aeval_barOne_hardPolynomial :
    aeval barOne (hardPolynomial ranks hn a) = hardGenerating ranks hn a := by
  unfold hardPolynomial hardGenerating
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ ↦ aeval_barOne_assignmentMonomial x

/-- `H_n = ∏_i (1 + X_i) - G_n`. -/
theorem complementGenerating_eq :
    complementGenerating ranks hn a =
      fullGenerating (encodedInputCount n) - hardGenerating ranks hn a := by
  rw [fullGenerating_eq_sum, eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- The monomials absent from `G_n` among the multilinear ones are those of
the assignments outside `L_n`. -/
theorem multilinear_notMem_support_hardGenerating (m : Fin (encodedInputCount n) →₀ ℕ) :
    ((∀ i, m i ≤ 1) ∧ m ∉ (hardGenerating ranks hn a).support) ↔
      ∃ x, ¬hardFunction ranks hn a x ∧ m = selected x univ := by
  unfold hardGenerating
  rw [multilinear_iff_exists_selected, mem_support_sum_indicatorMonomial]
  constructor
  · rintro ⟨⟨x, rfl⟩, h⟩
    refine ⟨x, fun hx ↦ h ⟨x, by simpa using hx, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro ⟨y, hy, hxy⟩
    rw [selected_univ_injective hxy] at hx
    exact hx (by simpa using hy)

variable (σ : Equiv.Perm (Fin (encodedInputCount n)))

/-- The circuit for `G_n`: the paired circuit for `P_n` after the substitution. -/
noncomputable def hardGeneratingCircuit : ArithCircuit (Fin (encodedInputCount n)) :=
  (hardCircuit ranks hn a σ).substituteBar

theorem hardGeneratingCircuit_computes :
    (hardGeneratingCircuit ranks hn a σ).Computes (hardGenerating ranks hn a) := by
  rw [← aeval_barOne_hardPolynomial]
  exact (hardCircuit ranks hn a σ).substituteBar_computes (hardCircuit_poly_output ranks hn a σ)

theorem hardGeneratingCircuit_isMonotone : (hardGeneratingCircuit ranks hn a σ).IsMonotone :=
  (hardCircuit ranks hn a σ).substituteBar_isMonotone (hardCircuit_isMonotone ranks hn a σ)

theorem hardGeneratingCircuit_isSyntacticallyMultilinear :
    (hardGeneratingCircuit ranks hn a σ).IsSyntacticallyMultilinear :=
  (hardCircuit ranks hn a σ).substituteBar_isSyntacticallyMultilinear
    (hardCircuit_isSetMultilinear ranks hn a σ).1

theorem hardGeneratingCircuit_size_le
    (hw : ∀ T : ThresholdTerm n, (termSigned ranks hn T).positive.card +
      (termSigned ranks hn T).negative.card ≤ 10 * n) :
    (hardGeneratingCircuit ranks hn a σ).size ≤ arithmeticCircuitBound n :=
  hardCircuit_size_le ranks hn a σ hw

/-- The circuit for `∏_i (1 + X_i)`: the paired circuit for `T_n` after the
substitution. -/
noncomputable def fullGeneratingCircuit : ArithCircuit (Fin (encodedInputCount n)) :=
  (fullCircuit σ).substituteBar

theorem fullGeneratingCircuit_computes :
    (fullGeneratingCircuit σ).Computes (fullGenerating (encodedInputCount n)) := by
  rw [← aeval_barOne_fullPolynomial]
  exact (fullCircuit σ).substituteBar_computes (fullCircuit_poly_output σ)

theorem fullGeneratingCircuit_isMonotone : (fullGeneratingCircuit σ).IsMonotone :=
  (fullCircuit σ).substituteBar_isMonotone (fullCircuit_isMonotone σ)

theorem fullGeneratingCircuit_isSyntacticallyMultilinear :
    (fullGeneratingCircuit σ).IsSyntacticallyMultilinear :=
  (fullCircuit σ).substituteBar_isSyntacticallyMultilinear (fullCircuit_isSetMultilinear σ).1

theorem fullGeneratingCircuit_size :
    (fullGeneratingCircuit σ).size = 5 * encodedInputCount n + 1 :=
  fullCircuit_size σ

end encodedGenerating

/-- The polynomial of satisfying assignments has a monotone syntactically
multilinear circuit of size `2^{O(n)}`. Subtracting it from `∏_i (1 + X_i)`
computes the polynomial of missing multilinear monomials, also in size
`2^{O(n)}`. Any monotone circuit supported on those missing monomials,
regardless of their positive coefficients, has size `s` satisfying
`(2*N + 5)*s + 2*N + 2 ≥ spectralNodeLower n`. Thus `s = 2^{Ω(n²)}`. Both
polynomials themselves have coefficients in `{0, 1}`. -/
@[tutorial_box "cor:paper-generating"]
theorem missing_monomials (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector),
      (∀ m, coeff m (hardGenerating ranks hn a) = 0 ∨
        coeff m (hardGenerating ranks hn a) = 1) ∧
      (∃ P : ArithCircuit.{0, 0} (Fin (encodedInputCount n)),
        P.IsMonotone ∧ P.IsSyntacticallyMultilinear ∧
        P.Computes (hardGenerating ranks hn a) ∧
        P.size ≤ arithmeticCircuitBound n) ∧
      (∃ T : ArithCircuit.{0, 0} (Fin (encodedInputCount n)),
        T.IsMonotone ∧ T.IsSyntacticallyMultilinear ∧
        T.Computes (fullGenerating (encodedInputCount n)) ∧
        T.size ≤ 5 * encodedInputCount n + 1) ∧
      complementGenerating ranks hn a =
        fullGenerating (encodedInputCount n) - hardGenerating ranks hn a ∧
      (∀ m, coeff m (complementGenerating ranks hn a) = 0 ∨
        coeff m (complementGenerating ranks hn a) = 1) ∧
      (∀ A : ArithCircuit.{0, 0} (Fin (encodedInputCount n)), A.IsMonotone →
        (∀ m, m ∈ (A.poly A.output).support ↔
          (∀ i, m i ≤ 1) ∧ m ∉ (hardGenerating ranks hn a).support) →
        spectralNodeLower n ≤
          ((A.size * (2 * encodedInputCount n + 5) + 2 * encodedInputCount n + 2 : ℕ) : ℝ)) ∧
      (∀ A : ArithCircuit.{0, 0} (Fin (encodedInputCount n)), A.IsMonotone →
        A.Computes (complementGenerating ranks hn a) →
        spectralNodeLower n ≤
          ((A.size * (2 * encodedInputCount n + 5) + 2 * encodedInputCount n + 2 : ℕ) : ℝ)) := by
  obtain ⟨ranks, hwidth⟩ := every_term_short hn
  obtain ⟨a, hlower⟩ := DNNF_lower_bound_nodes n hn ranks
  refine ⟨ranks, a, fun m ↦ coeff_sum_indicatorMonomial_zero_or_one _ m, ?_, ?_,
    complementGenerating_eq ranks hn a, fun m ↦ coeff_sum_indicatorMonomial_zero_or_one _ m,
    ?_, ?_⟩
  · exact ⟨hardGeneratingCircuit ranks hn a (Equiv.refl _),
      hardGeneratingCircuit_isMonotone ranks hn a _,
      hardGeneratingCircuit_isSyntacticallyMultilinear ranks hn a _,
      hardGeneratingCircuit_computes ranks hn a _,
      hardGeneratingCircuit_size_le ranks hn a _ hwidth⟩
  · exact ⟨fullGeneratingCircuit (Equiv.refl _), fullGeneratingCircuit_isMonotone _,
      fullGeneratingCircuit_isSyntacticallyMultilinear _, fullGeneratingCircuit_computes _,
      (fullGeneratingCircuit_size _).le⟩
  · intro A hmono hsupp
    refine generating_lower_bound_of_dnnf _ _ hlower A hmono fun m ↦ ?_
    rw [hsupp, multilinear_notMem_support_hardGenerating]
  · intro A hmono hA
    refine generating_lower_bound_of_dnnf _ _ hlower A hmono fun m ↦ ?_
    have hA' : A.poly A.output = _ := hA
    rw [hA', complementGenerating, mem_support_sum_indicatorMonomial]
    simp [mem_filter]

end DDNNFNegation
