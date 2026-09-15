import DDNNFNegation.Separation
import DDNNFNegation.CircuitOperations
import DDNNFNegation.CircuitTransport
import DDNNFNegation.Prune
import TutorialBox

/-!
# Polynomial nonclosure for concrete circuits

For every polynomial degree `d` and multiplier `M`, construct a d-DNNF `C`
such that every general DNNF for its negation has more than `M * C.size ^ d`
nodes. The proof-side separation is transported to the array-indexed model
of `TrustBoundary.lean`. Padding absorbs the polynomial conversion costs;
any extra variables in an adversarial circuit can be fixed to false.
-/

namespace DDNNFNegation

section

/-- Computing a function is invariant under replacing it by a pointwise
equivalent one. -/
theorem NNFCircuit.Computes.congr {Var : Type*} [DecidableEq Var]
    {C : NNFCircuit Var} {f g : (Var → Bool) → Prop}
    (h : C.Computes f) (hfg : ∀ v, f v ↔ g v) : C.Computes g :=
  fun v ↦ (h v).trans (hfg v)

/-- **Renumbering the variables.**  A separation over an arbitrary finite
variable type of cardinality `m` is a separation over `Fin m`, with the
same circuit sizes and the same lower bound.  Both directions of the
statement are carried along the numbering, the positive circuit forwards
and the adversary circuit backwards. -/
theorem exists_separation_over_fin.{u} {V : Type} [Fintype V] [DecidableEq V]
    {m : ℕ} (hcard : Fintype.card V = m)
    (orig : (V → Bool) → Prop) (Cpad : NNFCircuit.{0, 0} V)
    (hdet : Cpad.IsDeterministicDNNF) (hcomputes : Cpad.Computes orig)
    (bound : ℕ) (hsize : Cpad.size ≤ bound) (B : ℝ)
    (hlower : ∀ D : NNFCircuit.{0, u} V, D.IsDNNF →
      D.Computes (fun x ↦ ¬orig x) → B < (D.size : ℝ)) :
    ∃ f : (Fin m → Bool) → Prop,
      (∃ C : NNFCircuit.{0, 0} (Fin m),
        C.IsDeterministicDNNF ∧ C.Computes f ∧ C.size ≤ bound) ∧
      (∀ D : NNFCircuit.{0, u} (Fin m), D.IsDNNF →
        D.Computes (fun x ↦ ¬f x) → B < (D.size : ℝ)) := by
  classical
  let e : V ≃ Fin m := Fintype.equivFinOfCardEq hcard
  refine ⟨fun x ↦ orig (x ∘ e), ⟨Cpad.mapVariables e.toEmbedding,
    Cpad.mapVariables_isDeterministicDNNF _ hdet,
    Cpad.mapVariables_computes _ hcomputes, hsize⟩, ?_⟩
  intro D hDNNF hD
  have hback : (D.mapVariables e.symm.toEmbedding).Computes
      (fun w ↦ ¬orig w) := by
    refine (D.mapVariables_computes e.symm.toEmbedding hD).congr ?_
    intro w
    have hcomp : (fun v : V ↦ (w ∘ (e.symm : Fin m → V)) (e v)) = w := by
      funext v
      simp [e]
    simp only [Function.comp_def, Equiv.coe_toEmbedding]
    rw [show (fun v : V ↦ w (e.symm (e v))) = w from hcomp]
  exact hlower _ (D.mapVariables_decomposable e.symm.toEmbedding hDNNF) hback

/-- **The separation at the padded scale.**  Every quantity is measured in
the number `m` of variables: the positive circuit has at most `2 m` gates,
and every DNNF for the complement has more than `(2 m) ^ d`.  This is the
shape the explicit construction produces, reached by choosing `n` large
enough that `c · m ^ (κ log m)` exceeds `3 · (2 m) ^ (2 d)`, and then
converting the edge bounds of the construction into gate bounds. -/
theorem exists_separation_at_padded_scale.{u} (d M : ℕ) :
    ∃ (m : ℕ) (f : (Fin m → Bool) → Prop) (C : NNFCircuit.{0, 0} (Fin m)),
      C.IsDeterministicDNNF ∧ C.Computes f ∧ C.size ≤ 2 * m ∧ M ≤ m ∧
        ∀ D : NNFCircuit.{0, u} (Fin m), D.IsDNNF →
          D.Computes (fun x ↦ ¬f x) → (2 * (m : ℝ)) ^ d < (D.size : ℝ) := by
  classical
  have hc : 0 < quasipolynomialPrefactor := quasipolynomialPrefactor_pos
  have hrate : 0 < quasipolynomialRate := quasipolynomialRate_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := quasipolynomialRate * (46 * Real.log 2) with hA
  have hApos : 0 < A := by
    rw [hA]; exact mul_pos hrate (by positivity)
  obtain ⟨n₁, hn₁⟩ :=
    exists_nat_ge (max (6 / quasipolynomialPrefactor) ((4 * d + 1) / A))
  set n : ℕ := max 25 (max M n₁) with hn_def
  have h25 : 25 ≤ n := le_max_left _ _
  have hMn : M ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hn₁n : n₁ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  -- The padded length dominates `n` itself, which is all the size
  -- comparisons below need.
  set m : ℕ := exponentialPaddedLength n with hm_def
  have hnm : n ≤ m := by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ n ≤ 2 ^ (46 * n) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hm_def]
    show n ≤ 2 ^ (46 * n)
    exact le_of_lt (lt_of_lt_of_le h1 h2)
  have hMm : M ≤ m := le_trans hMn hnm
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by
    have : 2 ≤ n := by omega
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hlogm : Real.log (m : ℝ) = 46 * (n : ℝ) * Real.log 2 := by
    have hcast : ((m : ℕ) : ℝ) = (2 : ℝ) ^ (46 * n) := by
      rw [hm_def]; push_cast; ring
    rw [hcast, Real.log_pow]
    push_cast
    ring
  -- The two numeric conditions on `n`.
  have hn₁R : ((n₁ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁n
  have hexp : (4 * (d : ℝ) + 1) ≤ quasipolynomialRate * Real.log (m : ℝ) := by
    have hle : (4 * d + 1) / A ≤ (n : ℝ) :=
      le_trans (le_trans (le_max_right _ _) hn₁) hn₁R
    have := (div_le_iff₀ hApos).mp hle
    rw [hlogm]
    calc (4 * (d : ℝ) + 1) ≤ A * n := by linarith
    _ = quasipolynomialRate * (46 * (n : ℝ) * Real.log 2) := by rw [hA]; ring
  have hcm : 6 ≤ quasipolynomialPrefactor * (m : ℝ) := by
    have hle : 6 / quasipolynomialPrefactor ≤ (n : ℝ) :=
      le_trans (le_trans (le_max_left _ _) hn₁) hn₁R
    have h2 : (6 : ℝ) ≤ (n : ℝ) * quasipolynomialPrefactor :=
      (div_le_iff₀ hc).mp hle
    nlinarith
  -- The explicit separation at this `n`, in edge counts.
  obtain ⟨ranks, a, Cpad, hcard, hdet, hcomputes, hedges, hlower⟩ :=
    separation_after_padding_of_any_gates.{u} n h25
  -- The witness: the positive circuit without its unreachable gates.
  have hprune_size : Cpad.prune.size ≤ 2 * m := by
    have hm1' : 1 ≤ m := by omega
    calc Cpad.prune.size ≤ Cpad.prune.edgeCount + 1 := Cpad.prune_size_le
      _ ≤ Cpad.edgeCount + 1 := Nat.add_le_add_right Cpad.edgeCount_prune_le 1
      _ ≤ m + 1 := Nat.add_le_add_right hedges 1
      _ ≤ 2 * m := by omega
  -- The adversary bound in gate counts, through duplicate removal.
  have hgate : ∀ D : NNFCircuit.{0, u}
      (PaddedVar (encodedInputCount n) (exponentialPaddedLength n)),
      D.IsDNNF →
      D.Computes (fun x ↦ ¬paddedEncodedOuterFunction ranks
        (by omega : 0 < n) a x) →
      (2 * (m : ℝ)) ^ d < (D.size : ℝ) := by
    intro D hDNNF hD
    have hedge := hlower D.dedup (D.dedup_isDNNF hDNNF) (D.dedup_computes hD)
    have hdedup : (D.dedup.edgeCount : ℝ) ≤
        (D.size : ℝ) * ((D.size : ℝ) + 2) := by
      exact_mod_cast D.edgeCount_dedup_le
    have hspos : (1 : ℝ) ≤ (D.size : ℝ) := by exact_mod_cast circuit_size_pos D
    have hsq : (D.size : ℝ) * ((D.size : ℝ) + 2) ≤ 3 * (D.size : ℝ) ^ 2 := by
      nlinarith
    have hstep : (m : ℝ) ^ (4 * (d : ℝ) + 1) ≤
        (m : ℝ) ^ (quasipolynomialRate * Real.log (m : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1 hexp
    have hnat : (m : ℝ) ^ (4 * (d : ℝ) + 1) = (m : ℝ) ^ (4 * d) * (m : ℝ) := by
      rw [show (4 * (d : ℝ) + 1) = ((4 * d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_succ]
    have hpow : ((2 * (m : ℝ)) ^ d) ^ 2 ≤ (m : ℝ) ^ (4 * d) := by
      calc ((2 * (m : ℝ)) ^ d) ^ 2 = (2 : ℝ) ^ (2 * d) * (m : ℝ) ^ (2 * d) := by
            ring
        _ ≤ (m : ℝ) ^ (2 * d) * (m : ℝ) ^ (2 * d) := by gcongr
        _ = (m : ℝ) ^ (4 * d) := by ring
    have hm4 : 0 < (m : ℝ) ^ (4 * d) := pow_pos (by linarith) _
    have h23 : 2 ≤ quasipolynomialPrefactor * (m : ℝ) / 3 := by linarith
    have key : ((2 * (m : ℝ)) ^ d) ^ 2 < (D.size : ℝ) ^ 2 := by
      calc ((2 * (m : ℝ)) ^ d) ^ 2 ≤ (m : ℝ) ^ (4 * d) := hpow
        _ < 2 * (m : ℝ) ^ (4 * d) := by linarith
        _ ≤ (quasipolynomialPrefactor * (m : ℝ) / 3) * (m : ℝ) ^ (4 * d) :=
          mul_le_mul_of_nonneg_right h23 hm4.le
        _ = (quasipolynomialPrefactor / 3) * ((m : ℝ) ^ (4 * d) * (m : ℝ)) := by
          ring
        _ = (quasipolynomialPrefactor / 3) * (m : ℝ) ^ (4 * (d : ℝ) + 1) := by
          rw [hnat]
        _ ≤ (quasipolynomialPrefactor / 3) *
            (m : ℝ) ^ (quasipolynomialRate * Real.log (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (quasipolynomialPrefactor *
            (m : ℝ) ^ (quasipolynomialRate * Real.log (m : ℝ))) / 3 := by
          ring
        _ ≤ (D.dedup.edgeCount : ℝ) / 3 := by linarith
        _ ≤ (D.size : ℝ) * ((D.size : ℝ) + 2) / 3 := by linarith
        _ ≤ (D.size : ℝ) ^ 2 := by linarith
    have h2m : 0 ≤ (2 * (m : ℝ)) ^ d := by positivity
    nlinarith [key, h2m, hspos]
  obtain ⟨f, ⟨C, hCdet, hCcomputes, hCsize⟩, hneg⟩ :=
    exists_separation_over_fin.{u} hcard _ Cpad.prune
      (Cpad.prune_isDeterministicDNNF hdet) (Cpad.prune_computes hcomputes)
      (2 * m) hprune_size _ hgate
  exact ⟨m, f, C, hCdet, hCcomputes, hCsize, hMm, hneg⟩

/-- Finite-variable form of polynomial nonclosure, over `Fin m` with a
real-valued bound. The countable-variable form over `ℕ` is derived below. -/
def NotClosedUnderNegationOverFin.{u} : Prop :=
  ∀ d M : ℕ,
    ∃ (m : ℕ) (f : (Fin m → Bool) → Prop)
      (C : NNFCircuit.{0, 0} (Fin m)),
      C.IsDeterministicDNNF ∧ C.Computes f ∧
        ∀ D : NNFCircuit.{0, u} (Fin m), D.IsDNNF →
          D.Computes (fun x ↦ ¬f x) →
            (M : ℝ) * (C.size : ℝ) ^ d < (D.size : ℝ)

/-- The separation over `Fin m`.  The number of variables and the padding
disappear into the proof: the positive circuit has at most `2 m` gates, so
`M * s ^ d` with `s ≤ 2 m` and `M ≤ m` is at most `(2 m) ^ (d + 1)`, which
`exists_separation_at_padded_scale` beats. -/
theorem dDNNF_not_closed_under_negation_over_fin.{u} :
    NotClosedUnderNegationOverFin.{u} := by
  intro d M
  obtain ⟨m, f, C, hdet, hcomputes, hCsize, hMm, hlow⟩ :=
    exists_separation_at_padded_scale.{u} (d + 1) M
  refine ⟨m, f, C, hdet, hcomputes, ?_⟩
  intro D hDNNF hD
  have hC : (C.size : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hCsize
  have hM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hMm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hM' : (M : ℝ) ≤ 2 * (m : ℝ) := by linarith
  calc (M : ℝ) * (C.size : ℝ) ^ d
      ≤ (2 * (m : ℝ)) * (2 * (m : ℝ)) ^ d :=
        mul_le_mul hM' (pow_le_pow_left₀ (by positivity) hC d)
          (by positivity) (by positivity)
    _ = (2 * (m : ℝ)) ^ (d + 1) := by rw [pow_succ]; ring
    _ < (D.size : ℝ) := hlow D hDNNF hD

/-- Splitting the variable supply at `m`: the first `m` variables map into
`Fin m` and the rest keep their names. -/
def natSplitAt (m : ℕ) : ℕ ↪ Fin m ⊕ ℕ where
  toFun x := if h : x < m then .inl ⟨x, h⟩ else .inr x
  inj' := by
    intro a b hab
    dsimp only at hab
    by_cases ha : a < m
    · by_cases hb : b < m
      · rw [dif_pos ha, dif_pos hb] at hab
        exact congrArg Fin.val (Sum.inl.inj hab)
      · rw [dif_pos ha, dif_neg hb] at hab
        exact absurd hab (by simp)
    · by_cases hb : b < m
      · rw [dif_neg ha, dif_pos hb] at hab
        exact absurd hab (by simp)
      · rw [dif_neg ha, dif_neg hb] at hab
        exact Sum.inr.inj hab

/-- **d-DNNF is not polynomially closed under negation**, the claim stated as
`NotClosedUnderNegationNNFCircuit` in `Circuit.lean`, over the countable
variable supply.  The witness is the `Fin m` witness with its variables
renumbered into `ℕ`.  An adversary `D` over `ℕ` may mention variables
the witness never uses; fixing every variable from `m` on to `false` and
renaming the rest turns it into an adversary over `Fin m` with the same
number of gates, which the bound over `Fin m` defeats. -/
theorem dDNNF_not_closed_under_negation_nnfCircuit.{u} : NotClosedUnderNegationNNFCircuit.{u} := by
  intro d M
  obtain ⟨m, f, C, hdet, hcomputes, hlow⟩ :=
    dDNNF_not_closed_under_negation_over_fin.{u} d M
  refine ⟨C.mapVariables Fin.valEmbedding,
    C.mapVariables_isDeterministicDNNF _ hdet, ?_⟩
  intro D hDNNF hDneg
  -- `D` computes the complement of `f` read through the renumbering.
  have hDf : D.Computes (fun v ↦ ¬ f (v ∘ ⇑Fin.valEmbedding)) :=
    hDneg.congr fun v ↦ not_congr (hcomputes (v ∘ ⇑Fin.valEmbedding))
  -- Transport `D` back over `Fin m`: fix the variables from `m` on.
  set fixed : ℕ → Bool := fun _ ↦ false
  have hmap := D.mapVariables_computes (natSplitAt m) hDf
  have hres :=
    (D.mapVariables (natSplitAt m)).restrictRightVariables_computes fixed hmap
  have hkey : ∀ w : Fin m → Bool,
      (Sum.elim w fixed ∘ ⇑(natSplitAt m)) ∘ ⇑Fin.valEmbedding = w := by
    intro w
    funext x
    have hx : natSplitAt m (Fin.valEmbedding x) = Sum.inl x := by
      have hdite : natSplitAt m (Fin.valEmbedding x) =
          if h : (x : ℕ) < m then Sum.inl ⟨(x : ℕ), h⟩
          else Sum.inr (x : ℕ) := rfl
      rw [hdite, dif_pos x.isLt, Fin.eta]
    simp only [Function.comp_apply, hx, Sum.elim_inl]
  have hD' : ((D.mapVariables (natSplitAt m)).restrictRightVariables
      fixed).Computes (fun w ↦ ¬ f w) := by
    refine hres.congr fun w ↦ ?_
    rw [hkey w]
  have hbound := hlow _
    ((D.mapVariables (natSplitAt m)).restrictRightVariables_decomposable
      fixed (D.mapVariables_decomposable (natSplitAt m) hDNNF)) hD'
  -- Both transports keep the gate type, so both sizes are unchanged.
  have hDsize : ((D.mapVariables (natSplitAt m)).restrictRightVariables
      fixed).size = D.size := rfl
  rw [hDsize] at hbound
  simp only [NNFCircuit.mapVariables_size]
  exact_mod_cast hbound

/-- **d-DNNF is not polynomially closed under negation**: the claim
`NotClosedUnderNegation` stated in `TrustBoundary.lean` over array-indexed
circuits.  The witness is the shared-gate witness above with its gates
listed in order of increasing rank.  An adversary array circuit is read
as a binary shared-gate circuit.  An unbounded conjunction is replaced by
a prefix chain, giving exactly `size * (size + 1)` binary gates.  The
quasipolynomial separation absorbs this quadratic expansion. -/
theorem dDNNF_not_closed_under_negation : NotClosedUnderNegation := by
  intro d M
  obtain ⟨C, hdet, hbound⟩ :=
    dDNNF_not_closed_under_negation_nnfCircuit.{0} (2 * d + 2) ((M + 1) ^ 2)
  refine ⟨C.toCircuit, C.isDeterministicDNNF_toCircuit hdet, ?_⟩
  intro D hD hDneg
  -- Expand `D` to a binary shared-gate circuit.  It computes the same
  -- complement and remains decomposable.
  have hneg : D.toBinaryNNFCircuit.Computes
      (fun v ↦ ¬ C.semantics C.output v) := by
    intro v
    change D.binarySemantics (D.binaryRoot D.output) v ↔
      ¬ C.semantics C.output v
    rw [D.binarySemantics_root]
    rw [hDneg v, NNFCircuit.output_toCircuit, ← C.eval_toCircuit v C.output]
    simp
  have hlt := hbound D.toBinaryNNFCircuit
    (D.isDNNF_toBinaryNNFCircuit hD) hneg
  rw [D.size_toBinaryNNFCircuit] at hlt
  change M * C.size ^ d < D.size
  by_contra hnot
  have hDle : D.size ≤ M * C.size ^ d := Nat.le_of_not_gt hnot
  have hspos : 0 < C.size := Fintype.card_pos_iff.mpr ⟨C.output⟩
  have hsone : 1 ≤ C.size := hspos
  have hpownext : C.size ^ d ≤ C.size ^ (d + 1) :=
    Nat.pow_le_pow_right hsone (by omega)
  have honepow : 1 ≤ C.size ^ (d + 1) := one_le_pow₀ hsone
  let B := (M + 1) * C.size ^ (d + 1)
  have hDB : D.size ≤ B := by
    calc
      D.size ≤ M * C.size ^ d := hDle
      _ ≤ M * C.size ^ (d + 1) := Nat.mul_le_mul_left M hpownext
      _ ≤ (M + 1) * C.size ^ (d + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_succ M)
      _ = B := rfl
  have hDsuccB : D.size + 1 ≤ B := by
    calc
      D.size + 1 ≤ M * C.size ^ d + 1 := Nat.add_le_add_right hDle 1
      _ ≤ M * C.size ^ (d + 1) + C.size ^ (d + 1) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left M hpownext) honepow
      _ = B := by dsimp [B]; ring
  have hupper : D.size * (D.size + 1) ≤
      (M + 1) ^ 2 * C.size ^ (2 * d + 2) := by
    calc
      D.size * (D.size + 1) ≤ B * B := Nat.mul_le_mul hDB hDsuccB
      _ = (M + 1) ^ 2 * C.size ^ (2 * d + 2) := by
        dsimp [B]
        rw [show 2 * d + 2 = (d + 1) + (d + 1) by omega, pow_add]
        ring
  omega

end

end DDNNFNegation
