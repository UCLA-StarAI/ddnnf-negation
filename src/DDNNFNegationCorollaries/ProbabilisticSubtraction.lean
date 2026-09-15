import DDNNFNegation
import DDNNFNegationCorollaries.Supporting.LowerBoundGrowth
import DDNNFNegationCorollaries.Supporting.ConditionalDistribution
import DDNNFNegationCorollaries.Supporting.ProbabilisticCircuit
import DDNNFNegationCorollaries.AssignmentPolynomials
import TutorialBox

/-!
# Probabilistic circuit subtraction

The uniform distribution on the complement of the hard function has
a small representation with one subtraction from a constant. Every
nonnegative decomposable probabilistic circuit for it is large.
-/

namespace DDNNFNegation

open Finset ProductDist MvPolynomial
open Classical

/-- A one-node `⊥` circuit, used only to rule out an empty complement. -/
def botCircuit (N : ℕ) : NNFCircuit (Fin N) where
  Gate := Unit
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := ()
  node := fun _ => .bot
  rank := fun _ => 0
  child_rank := by intro g c h; cases h
  semantics := fun _ _ => False
  semantics_eq := by intro g x; rfl
  support := fun _ => ∅
  support_eq := by intro g; rfl

theorem botCircuit_isDNNF (N : ℕ) : (botCircuit N).IsDNNF := by
  intro g l r h; cases h

section Encoded

variable {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
  (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))

/-- The DNNF lower bound forces a countermodel once the bound exceeds one. -/
theorem exists_countermodel_of_lower
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)), D.IsDNNF →
      D.Computes (fun x ↦ ¬hardFunction ranks hn a x) → spectralNodeLower n ≤ (D.size : ℝ))
    (h300 : 300 ≤ n) : ∃ x, ¬hardFunction ranks hn a x := by
  by_contra h
  have hall : ∀ x, hardFunction ranks hn a x := by simpa using h
  have hb := hlower (botCircuit _) (botCircuit_isDNNF _)
    (fun x => ⟨fun hf => hf.elim, fun hx => hx (hall x)⟩)
  have hs : (botCircuit (encodedInputCount n)).size = 1 := rfl
  rw [hs] at hb
  exact (not_le_of_gt (spectralNodeLower_gt_one h300)) (by simpa using hb)

/-- The support lower bound for probabilistic circuits over the inputs. -/
theorem probCircuit_lower_of_support
    (hlower : ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)), D.IsDNNF →
      D.Computes (fun x ↦ ¬hardFunction ranks hn a x) → spectralNodeLower n ≤ (D.size : ℝ))
    (P : ProbCircuit.{0, 0} (Fin (encodedInputCount n))) (hnn : P.IsNonneg)
    (hdec : P.IsDecomposable)
    (hsupp : ∀ x, 0 < P.value P.output x ↔ ¬hardFunction ranks hn a x) :
    spectralNodeLower n ≤ 3 * (P.size : ℝ) := by
  have h := hlower P.toDNNF (P.toDNNF_isDNNF hdec)
    (fun x => (P.toDNNF_computes hnn x).trans (hsupp x))
  rw [P.toDNNF_size] at h
  exact_mod_cast h

/-- The uniform prior. -/
def uniformDist (N : ℕ) : ProductDist N where
  p := fun _ => 1 / 2
  pos := fun _ => by norm_num
  lt_one := fun _ => by norm_num

theorem uniformDist_prob {N : ℕ} (x : Fin N → Bool) : (uniformDist N).prob x = (1 / 2) ^ N := by
  unfold prob
  rw [Finset.prod_congr rfl (fun i _ =>
    (show (uniformDist N).w i (x i) = 1 / 2 by cases x i <;> simp [uniformDist, w]; norm_num)),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The number of countermodels `K_n`. -/
noncomputable def countermodelCount : ℕ :=
  (univ.filter (fun x ↦ ¬hardFunction ranks hn a x)).card

theorem normalizer_uniform :
    normalizer (uniformDist _) (hardFunction ranks hn a) =
      (countermodelCount ranks hn a : ℚ) * (1 / 2) ^ encodedInputCount n := by
  rw [normalizer_eq_sum]
  simp_rw [uniformDist_prob]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x ↦ hardFunction ranks hn a x)]
  rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_filter.1 hx).2),
    Finset.sum_congr rfl (fun x hx => if_neg (Finset.mem_filter.1 hx).2)]
  simp [countermodelCount]

/-- Under the uniform prior `p_n(x) = [¬L_n x] / K_n`. -/
theorem condProb_uniform (h : ∃ x, ¬hardFunction ranks hn a x) (x : Fin (encodedInputCount n) → Bool) :
    condProb (uniformDist _) (hardFunction ranks hn a) x =
      if hardFunction ranks hn a x then 0 else 1 / (countermodelCount ranks hn a : ℚ) := by
  have hK : (0 : ℚ) < countermodelCount ranks hn a := by
    obtain ⟨y, hy⟩ := h
    exact_mod_cast Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩⟩
  unfold condProb
  rw [normalizer_uniform, uniformDist_prob]
  split_ifs with hx
  · simp
  · field_simp

/-- A uniform complement distribution has a representation of size
`2^{O(n)}` with one subtraction from a constant and positive normalization.
Every nonnegative decomposable probabilistic circuit for that distribution
has size `2^{Ω(n²)}`. -/
@[tutorial_box "cor:paper-probabilistic"]
theorem probabilistic_subtraction (n : ℕ) (h300 : 300 ≤ n) :
    ∃ hn : 0 < n, ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector),
      (∃ C : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        C.IsDeterministicDNNF ∧ C.Computes (hardFunction ranks hn a) ∧
        C.size ≤ positiveCircuitBound n + 1) ∧
      0 < countermodelCount ranks hn a ∧
      (∃ P : ArithCircuit.{0, 0} (Fin (encodedInputCount n) × Bool),
        P.IsMonotone ∧ P.IsSetMultilinear ∧ P.size ≤ arithmeticCircuitBound n ∧
        ∀ x, (condProb (uniformDist _) (hardFunction ranks hn a) x : ℝ) =
          (1 - P.boolValue x) / (countermodelCount ranks hn a : ℝ)) ∧
      (∀ P : ProbCircuit.{0, 0} (Fin (encodedInputCount n)),
        P.IsNonneg → P.IsDecomposable →
        (∀ x, P.value P.output x =
          (condProb (uniformDist _) (hardFunction ranks hn a) x : ℝ)) →
        spectralNodeLower n ≤ 3 * (P.size : ℝ)) := by
  have hn : 0 < n := by omega
  obtain ⟨ranks, hwidth⟩ := every_term_short hn
  obtain ⟨a, hlower⟩ := DNNF_lower_bound_nodes n hn ranks
  obtain ⟨C, hdet, hcomputes, hsize⟩ := small_dDNNF_nodes ranks hn a hwidth
  have h := exists_countermodel_of_lower ranks hn a hlower h300
  refine ⟨hn, ranks, a, ⟨C, hdet, hcomputes, hsize.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (card_thresholdTerm_le n)) 1)⟩, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := h
    exact Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩
  · let σ := Equiv.refl (Fin (encodedInputCount n))
    refine ⟨hardCircuit ranks hn a σ, hardCircuit_isMonotone ranks hn a σ,
      hardCircuit_isSetMultilinear ranks hn a σ,
      hardCircuit_size_le ranks hn a σ hwidth, ?_⟩
    intro x
    have hP : (hardCircuit ranks hn a σ).boolValue x =
        if hardFunction ranks hn a x then 1 else 0 := by
      unfold ArithCircuit.boolValue
      rw [hardCircuit_poly_output, hardPolynomial, eval_boolPoint_sum]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hP, condProb_uniform ranks hn a h x]
    split_ifs <;> simp
  · intro P hnn hdec hval
    apply probCircuit_lower_of_support ranks hn a hlower P hnn hdec
    intro x
    rw [hval x, ← condProb_pos_iff (uniformDist _) _ h x]
    exact_mod_cast Iff.rfl

end Encoded

end DDNNFNegation
