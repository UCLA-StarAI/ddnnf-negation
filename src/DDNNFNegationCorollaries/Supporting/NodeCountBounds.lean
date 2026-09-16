import DDNNFNegation.FinalCover

/-!
# Auxiliary node-count lower bounds

The paper and circuit APIs use edges plus one. These weaker node-count
bounds are retained only for internal translations that first count a
finite gate type. Pruning transfers them to edge-based circuit size.
-/

namespace DDNNFNegation

namespace NNFCircuit

/-- Every circuit has positive size, including constants and literals. -/
theorem size_pos {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) :
    0 < C.size := Nat.zero_lt_succ _

end NNFCircuit

open Finset
noncomputable section

/-- A DNNF with unrestricted fan-in has a balanced rectangle cover
quadratic in its number of nodes. Repeated inputs in the internal circuit
model are removed before converting to binary gates. -/
theorem balanced_rectangle_cover_nodes
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))
    (D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)))
    (hDNNF : D.IsDNNF) (hDcomputes : D.Computes (fun x ↦ ¬hardFunction ranks hn a x)) :
    ∃ (r : ℕ) (_ : BalancedRectangleCover (fun x ↦ ¬hardFunction ranks hn a x) (Fin r)),
      r ≤ 7 * D.nodeCount ^ 2 := by
  obtain ⟨r, cover, hr⟩ := hardFunction_rectangle_cover ranks hn a D.dedup
    (D.dedup_isDNNF hDNNF) (D.dedup_computes hDcomputes)
  refine ⟨r, cover, ?_⟩
  have hsize : 1 ≤ D.nodeCount := by
    change 0 < Fintype.card D.Gate
    exact Fintype.card_pos_iff.mpr ⟨D.output⟩
  have he := D.edgeCount_dedup_le
  nlinarith

/-- The square-root node lower bound obtained from the quadratic
rectangle-cover reduction. Its exponential rate is half the cover rate. -/
def spectralNodeLower (n : ℕ) : ℝ :=
  Real.sqrt (1 / (64 * spectralEpsilon n) / 7)

/-- The DNNF node lower bound for the complement is `spectralNodeLower n`, asymptotically `2^{Ω(n²)}`. -/
theorem DNNF_lower_bound_nodes
    (n : ℕ) (hn : 0 < n) (ranks : LabelOrders n) :
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
        spectralNodeLower n ≤ (D.nodeCount : ℝ) := by
  obtain ⟨a, hcovers⟩ := exists_encoder_with_cover_lower_bound n hn ranks
  refine ⟨a, ?_⟩
  intro D hDNNF hDcomputes
  obtain ⟨r, cover, hr⟩ := balanced_rectangle_cover_nodes ranks hn a D hDNNF hDcomputes
  have hcover := hcovers (Fin r) cover
  rw [Fintype.card_fin] at hcover
  have hrR : (r : ℝ) ≤ 7 * (D.nodeCount : ℝ) ^ 2 := by exact_mod_cast hr
  unfold spectralNodeLower
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · linarith


end
end DDNNFNegation
