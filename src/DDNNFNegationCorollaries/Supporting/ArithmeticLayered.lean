import DDNNFNegationCorollaries.Supporting.ArithmeticCircuits
import DDNNFNegation.OBDD

/-!
# Layered polynomial circuits and sums of circuits

The positive side of the arithmetic corollaries.  A layered transition
system (the data behind the project's layered OBDDs, `LayeredOBDD`) becomes
a monotone arithmetic circuit over the paired indeterminates: the node of
layer `k` and state `s` is `X_{σ k} · (node of layer k+1 after reading 1) +
X̄_{σ k} · (node of layer k+1 after reading 0)`, and the terminal nodes are
the constants `1` (accept) and `0` (reject).  The variable read at layer `k`
is `σ k`, so the circuit follows any prescribed variable order.  Its output
polynomial is the sum of the monomials `m_x` over the accepted assignments
`x` (`layerPoly_zero`); the circuit is syntactically set-multilinear and
right-linear in the order `σ` (`circuit_isSetMultilinear`,
`circuit_isRightLinear`).

The second construction adds the outputs of finitely many circuits along a
chain of sums (`ArithCircuit.chain`), preserving monotonicity,
set-multilinearity when all outputs touch the same positions, and
right-linearity.
-/

namespace DDNNFNegation

open MvPolynomial Finset

namespace ArithNode

variable {V Gate Gate' : Type*}

theorem eval_map (f : Gate → Gate') (node : ArithNode V Gate)
    (child : Gate' → MvPolynomial V ℝ) :
    (node.map f).eval child = node.eval (child ∘ f) := by
  cases node <;> rfl

theorem vars_map [DecidableEq V] (f : Gate → Gate') (node : ArithNode V Gate)
    (child : Gate' → Finset V) :
    (node.map f).Vars child = node.Vars (child ∘ f) := by
  cases node <;> rfl

theorem isChild_map (f : Gate → Gate') (node : ArithNode V Gate) (child' : Gate')
    (h : (node.map f).IsChild child') :
    ∃ child, node.IsChild child ∧ f child = child' := by
  cases node with
  | const c => exact absurd h id
  | var x => exact absurd h id
  | add left right =>
      rcases h with h | h
      · exact ⟨left, Or.inl rfl, h.symm⟩
      · exact ⟨right, Or.inr rfl, h.symm⟩
  | mul left right =>
      rcases h with h | h
      · exact ⟨left, Or.inl rfl, h.symm⟩
      · exact ⟨right, Or.inr rfl, h.symm⟩

theorem map_eq_const (f : Gate → Gate') (node : ArithNode V Gate) (c : ℝ) :
    node.map f = const c ↔ node = const c := by
  cases node <;> simp [map]

theorem map_eq_var (f : Gate → Gate') (node : ArithNode V Gate) (x : V) :
    node.map f = var x ↔ node = var x := by
  cases node <;> simp [map]

theorem map_eq_add (f : Gate → Gate') (node : ArithNode V Gate) (l r : Gate') :
    node.map f = add l r ↔ ∃ left right, node = add left right ∧ f left = l ∧ f right = r := by
  cases node <;> simp [map]

theorem map_eq_mul (f : Gate → Gate') (node : ArithNode V Gate) (l r : Gate') :
    node.map f = mul l r ↔ ∃ left right, node = mul left right ∧ f left = l ∧ f right = r := by
  cases node <;> simp [map]

end ArithNode

/-! ## Reading a layered transition system as a polynomial circuit -/

namespace LayeredArith

variable {N : ℕ} (σ : Equiv.Perm (Fin N)) {State : Type*}
  (step : Fin N → State → Bool → State) (accept : State → Bool)

/-- Gates: one sum (or terminal constant) per layer and state, one product per
layer, state and bit, and one indeterminate per layer and bit. -/
abbrev Gate (N : ℕ) (State : Type*) :=
  (Fin (N + 1) × State) ⊕ ((Fin N × State × Bool) ⊕ (Fin N × Bool))

/-- The polynomial of the node at layer `k` in state `s`. -/
noncomputable def layerPoly (k : ℕ) (s : State) : MvPolynomial (Fin N × Bool) ℝ :=
  if h : k < N then
    X (σ ⟨k, h⟩, true) * layerPoly (k + 1) (step ⟨k, h⟩ s true) +
      X (σ ⟨k, h⟩, false) * layerPoly (k + 1) (step ⟨k, h⟩ s false)
  else C (if accept s then 1 else 0)
termination_by N - k
decreasing_by all_goals omega

theorem layerPoly_of_lt (k : ℕ) (s : State) (h : k < N) :
    layerPoly σ step accept k s =
      X (σ ⟨k, h⟩, true) * layerPoly σ step accept (k + 1) (step ⟨k, h⟩ s true) +
        X (σ ⟨k, h⟩, false) * layerPoly σ step accept (k + 1) (step ⟨k, h⟩ s false) := by
  rw [layerPoly]
  simp [h]

theorem layerPoly_of_le (k : ℕ) (s : State) (h : N ≤ k) :
    layerPoly σ step accept k s = C (if accept s then 1 else 0) := by
  rw [layerPoly]
  simp [not_lt.mpr h]

/-- The indeterminates read from layer `k` on. -/
def layerVars (k : ℕ) : Finset (Fin N × Bool) :=
  univ.filter fun v ↦ k ≤ (σ.symm v.1).1

/-- The local node table. -/
def node : Gate N State → ArithNode (Fin N × Bool) (Gate N State)
  | .inl (k, s) =>
      if h : k.1 < N then
        .add (.inr (.inl (⟨k.1, h⟩, s, true))) (.inr (.inl (⟨k.1, h⟩, s, false)))
      else .const (if accept s then 1 else 0)
  | .inr (.inl (k, s, b)) =>
      .mul (.inr (.inr (k, b))) (.inl (⟨k.1 + 1, Nat.succ_lt_succ k.isLt⟩, step k s b))
  | .inr (.inr (k, b)) => .var (σ k, b)

/-- Ranks decrease from the first layer to the indeterminates. -/
def rank : Gate N State → ℕ
  | .inl (k, _) => 3 * (N - k.1) + 2
  | .inr (.inl (k, _, _)) => 3 * (N - k.1) + 1
  | .inr (.inr _) => 0

theorem child_rank (gate child : Gate N State)
    (h : (node σ step accept gate).IsChild child) : rank child < rank gate := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [node, hk, ↓reduceDIte] at h
      rcases h with rfl | rfl <;> simp only [rank] <;> omega
    · simp only [node, hk, ↓reduceDIte] at h
      exact absurd h id
  · rcases h with rfl | rfl <;> simp only [rank] <;> have := k.isLt <;> omega
  · exact absurd h id

/-- The polynomial table. -/
noncomputable def poly : Gate N State → MvPolynomial (Fin N × Bool) ℝ
  | .inl (k, s) => layerPoly σ step accept k.1 s
  | .inr (.inl (k, s, b)) => X (σ k, b) * layerPoly σ step accept (k.1 + 1) (step k s b)
  | .inr (.inr (k, b)) => X (σ k, b)

theorem poly_eq (gate : Gate N State) :
    poly σ step accept gate = (node σ step accept gate).eval (poly σ step accept) := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [poly, node, hk, ↓reduceDIte, ArithNode.eval]
      exact layerPoly_of_lt σ step accept k.1 s hk
    · simp only [poly, node, hk, ↓reduceDIte, ArithNode.eval]
      exact layerPoly_of_le σ step accept k.1 s (not_lt.mp hk)
  · rfl
  · rfl

/-- The indeterminate table. -/
def vars : Gate N State → Finset (Fin N × Bool)
  | .inl (k, _) => layerVars σ k.1
  | .inr (.inl (k, _, b)) => {(σ k, b)} ∪ layerVars σ (k.1 + 1)
  | .inr (.inr (k, b)) => {(σ k, b)}

theorem mem_layerVars (k : ℕ) (v : Fin N × Bool) :
    v ∈ layerVars σ k ↔ k ≤ (σ.symm v.1).1 := by
  simp [layerVars]

theorem layerVars_of_le (k : ℕ) (h : N ≤ k) : layerVars σ k = ∅ := by
  ext v
  simp only [mem_layerVars, Finset.notMem_empty, iff_false, not_le]
  exact lt_of_lt_of_le (σ.symm v.1).isLt h

theorem layerVars_succ (k : Fin N) :
    layerVars σ k.1 = ({(σ k, true)} ∪ layerVars σ (k.1 + 1)) ∪
      ({(σ k, false)} ∪ layerVars σ (k.1 + 1)) := by
  ext ⟨i, b⟩
  have hi : i = σ k ↔ (σ.symm i).1 = k.1 := by
    rw [← Equiv.symm_apply_eq, Fin.ext_iff]
  simp only [mem_layerVars, mem_union, mem_singleton, Prod.mk.injEq, hi]
  cases b <;> simp <;> omega

theorem vars_eq (gate : Gate N State) :
    vars σ gate = (node σ step accept gate).Vars (vars σ) := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [vars, node, hk, ↓reduceDIte, ArithNode.Vars]
      exact layerVars_succ σ ⟨k.1, hk⟩
    · simp only [vars, node, hk, ↓reduceDIte, ArithNode.Vars]
      exact layerVars_of_le σ k.1 (not_lt.mp hk)
  · rfl
  · rfl

/-! ### The output polynomial -/

/-- The exponent of the indeterminates read from layer `k` on under the bit
sequence `v`: `∏_{j ≥ k} X_{σ j, v j}`. -/
noncomputable def suffixExponent (k : ℕ) (v : Fin N → Bool) : (Fin N × Bool) →₀ ℕ :=
  ∑ j ∈ univ.filter (fun j : Fin N ↦ k ≤ j.1), Finsupp.single (σ j, v j) 1

theorem suffixExponent_apply (k : ℕ) (v : Fin N → Bool) (i : Fin N) (b : Bool) :
    suffixExponent σ k v (σ i, b) = if k ≤ i.1 ∧ v i = b then 1 else 0 := by
  unfold suffixExponent
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq, σ.injective.eq_iff]
  by_cases hk : k ≤ i.1
  · rw [Finset.sum_eq_single i]
    · simp [hk]
    · intro j _ hj
      simp [hj]
    · intro hi
      simp [hk] at hi
  · rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro j hj
      have hji : j ≠ i := fun hji ↦ hk (hji ▸ (Finset.mem_filter.mp hj).2)
      simp [hji]

theorem suffixExponent_of_le (k : ℕ) (h : N ≤ k) (v : Fin N → Bool) :
    suffixExponent σ k v = 0 := by
  unfold suffixExponent
  apply Finset.sum_eq_zero
  intro j hj
  have := (Finset.mem_filter.mp hj).2
  have := j.isLt
  omega

theorem suffixExponent_succ (k : ℕ) (h : k < N) (v : Fin N → Bool) :
    suffixExponent σ k v =
      Finsupp.single (σ ⟨k, h⟩, v ⟨k, h⟩) 1 + suffixExponent σ (k + 1) v := by
  have hset : univ.filter (fun j : Fin N ↦ k ≤ j.1) =
      insert ⟨k, h⟩ (univ.filter (fun j : Fin N ↦ k + 1 ≤ j.1)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨k, h⟩ : Fin N) ∉ univ.filter (fun j : Fin N ↦ k + 1 ≤ j.1) := by
    simp
  unfold suffixExponent
  rw [hset, Finset.sum_insert hnot]

theorem suffixExponent_update (k : ℕ) (h : k < N) (v : Fin N → Bool) (b : Bool) :
    suffixExponent σ (k + 1) (Function.update v ⟨k, h⟩ b) = suffixExponent σ (k + 1) v := by
  unfold suffixExponent
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≠ ⟨k, h⟩ := by
    intro hjk
    have := (Finset.mem_filter.mp hj).2
    rw [hjk] at this
    simp at this
  rw [Function.update_of_ne hjk]

theorem suffixExponent_zero (v : Fin N → Bool) :
    suffixExponent σ 0 v = assignmentExponent (v ∘ σ.symm) := by
  unfold suffixExponent assignmentExponent
  rw [Finset.filter_true_of_mem (fun _ _ ↦ Nat.zero_le _)]
  rw [← Equiv.sum_comp σ (fun i ↦ Finsupp.single (i, (v ∘ σ.symm) i) 1)]
  simp

theorem runFrom_congr (k : ℕ) (s : State) (v w : Fin N → Bool)
    (hvw : ∀ j : Fin N, k ≤ j.1 → v j = w j) :
    LayeredOBDD.runFrom step v k s = LayeredOBDD.runFrom step w k s := by
  by_cases h : k < N
  · rw [LayeredOBDD.runFrom_of_lt step v k s h, LayeredOBDD.runFrom_of_lt step w k s h,
      hvw ⟨k, h⟩ le_rfl]
    exact runFrom_congr (k + 1) _ v w fun j hj ↦ hvw j (by omega)
  · rw [LayeredOBDD.runFrom, LayeredOBDD.runFrom]
    simp [h]
termination_by N - k
decreasing_by omega

theorem runFrom_of_le (k : ℕ) (h : N ≤ k) (v : Fin N → Bool) (s : State) :
    LayeredOBDD.runFrom step v k s = s := by
  rw [LayeredOBDD.runFrom]
  simp [not_lt.mpr h]

open Classical in
/-- The coefficients of the node polynomial at layer `k`: `1` on the
exponent of a bit sequence accepted from layer `k` on, `0` elsewhere. -/
theorem coeff_layerPoly (k : ℕ) (s : State) (m : (Fin N × Bool) →₀ ℕ) :
    coeff m (layerPoly σ step accept k s) =
      if ∃ v, m = suffixExponent σ k v ∧
          accept (LayeredOBDD.runFrom step v k s) = true then 1 else 0 := by
  by_cases h : k < N
  · have ih := fun s' m' ↦ coeff_layerPoly (k + 1) s' m'
    rw [layerPoly_of_lt σ step accept k s h, coeff_add, coeff_X_mul', coeff_X_mul']
    have key : ∀ b : Bool,
        (if (σ ⟨k, h⟩, b) ∈ m.support then
          coeff (m - Finsupp.single (σ ⟨k, h⟩, b) 1)
            (layerPoly σ step accept (k + 1) (step ⟨k, h⟩ s b)) else 0) =
        if ∃ v, v ⟨k, h⟩ = b ∧ m = suffixExponent σ k v ∧
            accept (LayeredOBDD.runFrom step v k s) = true then 1 else 0 := by
      intro b
      by_cases hmem : (σ ⟨k, h⟩, b) ∈ m.support
      · rw [if_pos hmem, ih]
        apply if_congr _ rfl rfl
        have hle : Finsupp.single (σ ⟨k, h⟩, b) 1 ≤ m := by
          rw [Finsupp.single_le_iff]
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
        constructor
        · rintro ⟨v, hv, hacc⟩
          refine ⟨Function.update v ⟨k, h⟩ b, Function.update_self _ _ _, ?_, ?_⟩
          · rw [suffixExponent_succ σ k h, Function.update_self, suffixExponent_update,
              ← hv, add_tsub_cancel_of_le hle]
          · rw [LayeredOBDD.runFrom_of_lt step _ k s h, Function.update_self,
              runFrom_congr step (k + 1) _ _ v]
            · exact hacc
            · intro j hj
              exact Function.update_of_ne (fun hjk ↦ by rw [hjk] at hj; simp at hj) _ _
        · rintro ⟨v, hvk, hm, hacc⟩
          refine ⟨v, ?_, ?_⟩
          · rw [hm, suffixExponent_succ σ k h, hvk, add_tsub_cancel_left]
          · rw [LayeredOBDD.runFrom_of_lt step v k s h, hvk] at hacc
            exact hacc
      · rw [if_neg hmem]
        symm
        rw [if_neg]
        rintro ⟨v, hvk, hm, -⟩
        apply hmem
        rw [Finsupp.mem_support_iff, hm, suffixExponent_apply]
        simp [hvk]
    rw [key true, key false]
    have excl : ∀ v w : Fin N → Bool, m = suffixExponent σ k v → m = suffixExponent σ k w →
        v ⟨k, h⟩ = w ⟨k, h⟩ := by
      intro v w hv hw
      have h1 := congrArg (fun e ↦ e (σ ⟨k, h⟩, v ⟨k, h⟩)) hv
      have h2 := congrArg (fun e ↦ e (σ ⟨k, h⟩, v ⟨k, h⟩)) hw
      simp only [suffixExponent_apply, le_refl, true_and, if_true] at h1 h2
      rw [h1] at h2
      by_contra hne
      rw [if_neg (Ne.symm hne)] at h2
      exact one_ne_zero h2
    by_cases hex : ∃ v, m = suffixExponent σ k v ∧
        accept (LayeredOBDD.runFrom step v k s) = true
    · rw [if_pos hex]
      obtain ⟨v, hm, hacc⟩ := hex
      cases hv : v ⟨k, h⟩
      · rw [if_neg, if_pos ⟨v, hv, hm, hacc⟩, zero_add]
        rintro ⟨w, hwk, hw, -⟩
        have := excl v w hm hw
        rw [hv, hwk] at this
        exact absurd this (by decide)
      · rw [if_pos ⟨v, hv, hm, hacc⟩, if_neg, add_zero]
        rintro ⟨w, hwk, hw, -⟩
        have := excl v w hm hw
        rw [hv, hwk] at this
        exact absurd this (by decide)
    · rw [if_neg hex, if_neg, if_neg, add_zero]
      · rintro ⟨w, -, hw, hacc⟩
        exact hex ⟨w, hw, hacc⟩
      · rintro ⟨w, -, hw, hacc⟩
        exact hex ⟨w, hw, hacc⟩
  · have hk : N ≤ k := not_lt.mp h
    rw [layerPoly_of_le σ step accept k s hk, coeff_C]
    simp only [suffixExponent_of_le σ k hk, runFrom_of_le step k hk, exists_const]
    by_cases hm : m = 0 <;> by_cases hacc : accept s = true <;> simp [hm, hacc, eq_comm]
termination_by N - k
decreasing_by omega

open Classical in
/-- The output polynomial: the sum of `m_x` over the assignments `x` whose
bit sequence `x ∘ σ` (the bits in reading order) is accepted. -/
theorem layerPoly_zero (start : State) :
    layerPoly σ step accept 0 start =
      ∑ x ∈ univ.filter (fun x : Fin N → Bool ↦
          accept (LayeredOBDD.runFrom step (x ∘ σ) 0 start) = true),
        assignmentMonomial x := by
  ext m
  rw [coeff_layerPoly, coeff_sum]
  simp only [assignmentMonomial_eq_monomial, coeff_monomial]
  rw [Finset.sum_boole, Finset.filter_filter]
  have hiff : (∃ v, m = suffixExponent σ 0 v ∧
      accept (LayeredOBDD.runFrom step v 0 start) = true) ↔
      ∃ x, accept (LayeredOBDD.runFrom step (x ∘ σ) 0 start) = true ∧
        assignmentExponent x = m := by
    constructor
    · rintro ⟨v, hm, hacc⟩
      refine ⟨v ∘ σ.symm, ?_, ?_⟩
      · have : (v ∘ σ.symm) ∘ σ = v := by
          funext j
          simp
        rw [this]
        exact hacc
      · rw [hm, suffixExponent_zero]
    · rintro ⟨x, hacc, hm⟩
      refine ⟨x ∘ σ, ?_, hacc⟩
      rw [suffixExponent_zero, ← hm]
      congr 1
      funext i
      simp
  by_cases hex : ∃ x, accept (LayeredOBDD.runFrom step (x ∘ σ) 0 start) = true ∧
      assignmentExponent x = m
  · rw [if_pos (hiff.mpr hex)]
    obtain ⟨x, hacc, hm⟩ := hex
    have hfilter : univ.filter (fun x : Fin N → Bool ↦
        accept (LayeredOBDD.runFrom step (x ∘ σ) 0 start) = true ∧
          assignmentExponent x = m) = {x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨-, hy⟩
        exact assignmentExponent_injective (hy.trans hm.symm)
      · rintro rfl
        exact ⟨hacc, hm⟩
    rw [hfilter, Finset.card_singleton, Nat.cast_one]
  · rw [if_neg (fun h ↦ hex (hiff.mp h))]
    rw [Finset.filter_eq_empty_iff.mpr, Finset.card_empty, Nat.cast_zero]
    intro y _ hy
    exact hex ⟨y, hy⟩

variable [Fintype State] [DecidableEq State]

/-- The layered polynomial circuit of a transition system, reading the
variable `σ k` at layer `k`, started in `start`. -/
noncomputable def circuit (start : State) : ArithCircuit (Fin N × Bool) where
  Gate := Gate N State
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := .inl (⟨0, Nat.succ_pos N⟩, start)
  node := node σ step accept
  rank := rank
  child_rank := child_rank σ step accept
  poly := poly σ step accept
  poly_eq := poly_eq σ step accept
  vars := vars σ
  vars_eq := vars_eq σ step accept

variable (start : State)

theorem circuit_nodeCount :
    (circuit σ step accept start).nodeCount =
      (N + 1) * Fintype.card State + (N * Fintype.card State * 2 + N * 2) := by
  show Fintype.card ((Fin (N + 1) × State) ⊕ ((Fin N × State × Bool) ⊕ (Fin N × Bool))) = _
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem circuit_poly_output :
    (circuit σ step accept start).poly (circuit σ step accept start).output =
      layerPoly σ step accept 0 start := rfl

omit [Fintype State] [DecidableEq State] in
theorem node_const_nonneg (gate : Gate N State) (c : ℝ)
    (h : node σ step accept gate = .const c) : 0 ≤ c := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
      split_ifs <;> norm_num
  · cases h
  · cases h

theorem circuit_isMonotone : (circuit σ step accept start).IsMonotone :=
  node_const_nonneg σ step accept

theorem positions_layerVars_zero : positions (layerVars σ 0) = univ := by
  ext i
  simp only [positions, mem_image, mem_layerVars, mem_univ, iff_true]
  exact ⟨(i, true), Nat.zero_le _, rfl⟩

omit [Fintype State] [DecidableEq State] in
theorem node_mul_disjoint (gate l r : Gate N State)
    (h : node σ step accept gate = .mul l r) :
    Disjoint (positions (vars σ l)) (positions (vars σ r)) := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
  · cases h
    simp only [vars]
    rw [positions_singleton, Finset.disjoint_singleton_left]
    simp only [positions, mem_image, mem_layerVars, not_exists, not_and]
    intro v hv hvk
    rw [hvk, Equiv.symm_apply_apply] at hv
    omega
  · cases h

omit [Fintype State] [DecidableEq State] in
theorem node_add_positions (gate l r : Gate N State)
    (h : node σ step accept gate = .add l r) :
    positions (vars σ l) = positions (vars σ r) := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
      simp only [vars]
      rw [positions_union, positions_union, positions_singleton, positions_singleton]
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
  · cases h
  · cases h

theorem circuit_isSetMultilinear : (circuit σ step accept start).IsSetMultilinear :=
  ⟨node_mul_disjoint σ step accept, node_add_positions σ step accept⟩

omit [Fintype State] [DecidableEq State] in
theorem node_mul_rightLinear (gate l r : Gate N State)
    (h : node σ step accept gate = .mul l r) :
    ∃ i b, node σ step accept l = .var (i, b) ∧
      ∀ j ∈ positions (vars σ r), (σ.symm i).val < (σ.symm j).val := by
  rcases gate with ⟨k, s⟩ | ⟨⟨k, s, b⟩ | ⟨k, b⟩⟩
  · by_cases hk : k.1 < N
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
    · simp only [node, hk, ↓reduceDIte] at h
      cases h
  · cases h
    refine ⟨σ k, b, rfl, ?_⟩
    intro j hj
    simp only [vars, positions, mem_image] at hj
    obtain ⟨v, hv, rfl⟩ := hj
    rw [mem_layerVars] at hv
    simp only [Equiv.symm_apply_apply]
    omega
  · cases h

theorem circuit_isRightLinear :
    (circuit σ step accept start).IsRightLinear (fun y ↦ (σ.symm y).val) :=
  node_mul_rightLinear σ step accept

end LayeredArith

/-! ## Summing the outputs of a family of circuits -/

namespace ArithCircuit

section chain

variable {V : Type*} [DecidableEq V] {ι : Type*} {m : ℕ}
  (e : ι ≃ Fin (m + 1)) (f : ι → ArithCircuit V)

/-- Gates of the chain: the gates of every summand, and one chain gate per
summand.  Chain gate `0` copies the output node of the first summand; chain
gate `k + 1` adds chain gate `k` and the output of summand `k + 1`. -/
abbrev ChainGate (f : ι → ArithCircuit V) (m : ℕ) := (Σ i, (f i).Gate) ⊕ Fin (m + 1)

/-- The output polynomial of the `j`-th summand. -/
noncomputable def termPoly (j : Fin (m + 1)) : MvPolynomial V ℝ :=
  (f (e.symm j)).poly (f (e.symm j)).output

/-- The output indeterminates of the `j`-th summand. -/
def termVars (j : Fin (m + 1)) : Finset V :=
  (f (e.symm j)).vars (f (e.symm j)).output

/-- The summands up to `k`. -/
def below (k : Fin (m + 1)) : Finset (Fin (m + 1)) :=
  univ.filter (· ≤ k)

theorem below_zero (k : Fin (m + 1)) (hk : k.1 = 0) : below k = {k} := by
  ext j
  simp only [below, mem_filter, mem_univ, true_and, mem_singleton, Fin.le_def, Fin.ext_iff]
  omega

theorem below_succ (k : Fin (m + 1)) (_hk : k.1 ≠ 0) :
    below k = insert k (below ⟨k.1 - 1, by omega⟩) := by
  ext j
  simp only [below, mem_filter, mem_univ, true_and, mem_insert, Fin.le_def, Fin.ext_iff]
  omega

theorem notMem_below_pred (k : Fin (m + 1)) (hk : k.1 ≠ 0) :
    k ∉ below ⟨k.1 - 1, by omega⟩ := by
  simp only [below, mem_filter, mem_univ, true_and, Fin.le_def, not_le]
  omega

theorem below_last : below (Fin.last m) = univ := by
  ext j
  simp [below, Fin.le_last]

/-- The local node table of the chain. -/
def chainNode : ChainGate f m → ArithNode V (ChainGate f m)
  | .inl ⟨i, g⟩ => ((f i).node g).map fun g' ↦ .inl ⟨i, g'⟩
  | .inr k =>
      if hk : k.1 = 0 then
        ((f (e.symm k)).node (f (e.symm k)).output).map fun g' ↦ .inl ⟨e.symm k, g'⟩
      else .add (.inr ⟨k.1 - 1, by omega⟩) (.inl ⟨e.symm k, (f (e.symm k)).output⟩)

/-- The polynomial table. -/
noncomputable def chainPoly : ChainGate f m → MvPolynomial V ℝ
  | .inl ⟨i, g⟩ => (f i).poly g
  | .inr k => ∑ j ∈ below k, termPoly e f j

theorem chain_poly_eq (gate : ChainGate f m) :
    chainPoly e f gate = (chainNode e f gate).eval (chainPoly e f) := by
  rcases gate with ⟨i, g⟩ | k
  · simp only [chainPoly, chainNode, ArithNode.eval_map]
    exact (f i).poly_eq g
  · simp only [chainPoly, chainNode]
    split_ifs with hk
    · rw [below_zero k hk, Finset.sum_singleton, ArithNode.eval_map]
      exact (f (e.symm k)).poly_eq _
    · rw [below_succ k hk, Finset.sum_insert (notMem_below_pred k hk)]
      simp only [ArithNode.eval, chainPoly]
      rw [add_comm]
      rfl

/-- The indeterminate table. -/
def chainVars : ChainGate f m → Finset V
  | .inl ⟨i, g⟩ => (f i).vars g
  | .inr k => (below k).biUnion (termVars e f)

theorem chain_vars_eq (gate : ChainGate f m) :
    chainVars e f gate = (chainNode e f gate).Vars (chainVars e f) := by
  rcases gate with ⟨i, g⟩ | k
  · simp only [chainVars, chainNode, ArithNode.vars_map]
    exact (f i).vars_eq g
  · simp only [chainVars, chainNode]
    split_ifs with hk
    · rw [below_zero k hk, Finset.singleton_biUnion, ArithNode.vars_map]
      exact (f (e.symm k)).vars_eq _
    · rw [below_succ k hk, Finset.biUnion_insert]
      simp only [ArithNode.Vars, chainVars]
      rw [union_comm]
      rfl

theorem positions_biUnion {N : ℕ} {α : Type*} (s : Finset α) (t : α → Finset (Fin N × Bool)) :
    positions (s.biUnion t) = s.biUnion fun x ↦ positions (t x) :=
  Finset.biUnion_image

variable [Fintype ι]

/-- The largest rank of a summand gate. -/
def maxRank : ℕ :=
  univ.sup fun p : Σ i, (f i).Gate ↦ (f p.1).rank p.2

theorem rank_le_maxRank (i : ι) (g : (f i).Gate) : (f i).rank g ≤ maxRank f :=
  Finset.le_sup (f := fun p : Σ i, (f i).Gate ↦ (f p.1).rank p.2) (mem_univ ⟨i, g⟩)

/-- Ranks: summand gates keep theirs, chain gates sit above them all. -/
def chainRank : ChainGate f m → ℕ
  | .inl ⟨i, g⟩ => (f i).rank g
  | .inr k => maxRank f + k.1 + 1

theorem chain_child_rank (gate child : ChainGate f m)
    (h : (chainNode e f gate).IsChild child) : chainRank f child < chainRank f gate := by
  rcases gate with ⟨i, g⟩ | k
  · obtain ⟨g', hg', rfl⟩ := ArithNode.isChild_map _ _ _ h
    exact (f i).child_rank g g' hg'
  · simp only [chainNode] at h
    split_ifs at h with hk
    · obtain ⟨g', hg', rfl⟩ := ArithNode.isChild_map _ _ _ h
      have h1 := (f (e.symm k)).child_rank _ g' hg'
      have h2 := rank_le_maxRank f (e.symm k) (f (e.symm k)).output
      simp only [chainRank]
      omega
    · rcases h with rfl | rfl
      · simp only [chainRank]
        omega
      · have h2 := rank_le_maxRank f (e.symm k) (f (e.symm k)).output
        simp only [chainRank]
        omega

variable [DecidableEq ι]

/-- The sum of the outputs of the circuits `f i`, along a chain of sums. -/
noncomputable def chain : ArithCircuit V where
  Gate := ChainGate f m
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := .inr (Fin.last m)
  node := chainNode e f
  rank := chainRank f
  child_rank := chain_child_rank e f
  poly := chainPoly e f
  poly_eq := chain_poly_eq e f
  vars := chainVars e f
  vars_eq := chain_vars_eq e f

theorem chain_nodeCount : (chain e f).nodeCount = ∑ i, (f i).nodeCount + (m + 1) := by
  show Fintype.card ((Σ i, (f i).Gate) ⊕ Fin (m + 1)) = _
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  rfl

theorem chain_poly_output :
    (chain e f).poly (chain e f).output = ∑ i, (f i).poly (f i).output := by
  change ∑ j ∈ below (Fin.last m), termPoly e f j = _
  rw [below_last]
  exact Equiv.sum_comp e.symm fun i ↦ (f i).poly (f i).output

omit [Fintype ι] [DecidableEq ι] in
theorem chainNode_const (hf : ∀ i, (f i).IsMonotone) (gate : ChainGate f m) (c : ℝ)
    (hc : chainNode e f gate = .const c) : 0 ≤ c := by
  rcases gate with ⟨i, g⟩ | k
  · exact hf i g c ((ArithNode.map_eq_const _ _ _).mp hc)
  · simp only [chainNode] at hc
    split_ifs at hc with hk
    exact hf _ _ c ((ArithNode.map_eq_const _ _ _).mp hc)

theorem chain_isMonotone (h : ∀ i, (f i).IsMonotone) : (chain e f).IsMonotone :=
  chainNode_const e f h

omit [Fintype ι] [DecidableEq ι] in
theorem chainNode_mul_rightLinear {N : ℕ} {e : ι ≃ Fin (m + 1)}
    {f : ι → ArithCircuit (Fin N × Bool)} (order : Fin N → ℕ)
    (h : ∀ i, (f i).IsRightLinear order) (gate l r : ChainGate f m)
    (hg : chainNode e f gate = .mul l r) :
    ∃ i b, chainNode e f l = .var (i, b) ∧
      ∀ j ∈ positions (chainVars e f r), order i < order j := by
  rcases gate with ⟨i, g⟩ | k
  · obtain ⟨left, right, hnode, rfl, rfl⟩ := (ArithNode.map_eq_mul _ _ _ _).mp hg
    obtain ⟨i', b, hl, hr⟩ := h i g left right hnode
    exact ⟨i', b, (ArithNode.map_eq_var _ _ _).mpr hl, hr⟩
  · simp only [chainNode] at hg
    split_ifs at hg with hk
    obtain ⟨left, right, hnode, rfl, rfl⟩ := (ArithNode.map_eq_mul _ _ _ _).mp hg
    obtain ⟨i', b, hl, hr⟩ := h _ _ left right hnode
    exact ⟨i', b, (ArithNode.map_eq_var _ _ _).mpr hl, hr⟩

theorem chain_isRightLinear {N : ℕ} {e : ι ≃ Fin (m + 1)}
    {f : ι → ArithCircuit (Fin N × Bool)} (order : Fin N → ℕ)
    (h : ∀ i, (f i).IsRightLinear order) : (chain e f).IsRightLinear order :=
  chainNode_mul_rightLinear order h

omit [Fintype ι] [DecidableEq ι] in
theorem chainNode_mul_disjoint {N : ℕ} {e : ι ≃ Fin (m + 1)}
    {f : ι → ArithCircuit (Fin N × Bool)} (h : ∀ i, (f i).IsSetMultilinear)
    (gate l r : ChainGate f m) (hg : chainNode e f gate = .mul l r) :
    Disjoint (positions (chainVars e f l)) (positions (chainVars e f r)) := by
  rcases gate with ⟨i, g⟩ | k
  · obtain ⟨left, right, hnode, rfl, rfl⟩ := (ArithNode.map_eq_mul _ _ _ _).mp hg
    exact (h i).1 g left right hnode
  · simp only [chainNode] at hg
    split_ifs at hg with hk
    obtain ⟨left, right, hnode, rfl, rfl⟩ := (ArithNode.map_eq_mul _ _ _ _).mp hg
    exact (h _).1 _ left right hnode

omit [Fintype ι] [DecidableEq ι] in
theorem positions_chainVars_inr {N : ℕ} {e : ι ≃ Fin (m + 1)}
    {f : ι → ArithCircuit (Fin N × Bool)} (P : Finset (Fin N))
    (hP : ∀ i, positions ((f i).vars (f i).output) = P) (k : Fin (m + 1)) :
    positions (chainVars e f (.inr k)) = P := by
  simp only [chainVars, positions_biUnion, termVars]
  rw [Finset.biUnion_congr rfl (fun j _ ↦ hP (e.symm j))]
  ext x
  simp only [Finset.mem_biUnion]
  exact ⟨fun ⟨_, _, hx⟩ ↦ hx, fun hx ↦ ⟨k, by simp [below], hx⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem chainNode_add_positions {N : ℕ} {e : ι ≃ Fin (m + 1)}
    {f : ι → ArithCircuit (Fin N × Bool)} (h : ∀ i, (f i).IsSetMultilinear)
    (P : Finset (Fin N)) (hP : ∀ i, positions ((f i).vars (f i).output) = P)
    (gate l r : ChainGate f m) (hg : chainNode e f gate = .add l r) :
    positions (chainVars e f l) = positions (chainVars e f r) := by
  rcases gate with ⟨i, g⟩ | k
  · obtain ⟨left, right, hnode, rfl, rfl⟩ := (ArithNode.map_eq_add _ _ _ _).mp hg
    exact (h i).2 g left right hnode
  · simp only [chainNode] at hg
    split_ifs at hg with hk
    · obtain ⟨left, right, hnode, rfl, rfl⟩ := (ArithNode.map_eq_add _ _ _ _).mp hg
      exact (h _).2 _ left right hnode
    · cases hg
      rw [positions_chainVars_inr P hP]
      exact (hP _).symm

/-- Summands that are set-multilinear with outputs on the same positions
give a set-multilinear chain. -/
theorem chain_isSetMultilinear {N : ℕ} {e : ι ≃ Fin (m + 1)}
    {f : ι → ArithCircuit (Fin N × Bool)} (h : ∀ i, (f i).IsSetMultilinear)
    (P : Finset (Fin N)) (hP : ∀ i, positions ((f i).vars (f i).output) = P) :
    (chain e f).IsSetMultilinear :=
  ⟨chainNode_mul_disjoint h, chainNode_add_positions h P hP⟩

end chain

end ArithCircuit

end DDNNFNegation
