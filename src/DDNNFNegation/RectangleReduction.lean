import DDNNFNegation.GateElimination
import DDNNFNegation.Encoder
import TutorialBox

/-!
# From a DNNF to a balanced rectangle cover

The internal cover bound is stated in terms of edges. Deduplicating inputs
and pruning relate this to the number of nodes, yielding the paper's
quadratic node-count bound `balanced_rectangle_cover`.
-/

namespace DDNNFNegation

open Finset

/-- Lemma "Edge-count rectangle cover": a DNNF with `s` edges computing
the complement of `L_n` gives a cover of the zero-inputs of `L_n` by at most
`2 s + 1` balanced zero-rectangles.  This is `NNFCircuit.rectangle_cover`
at the `N = 60 n²` variables of `L_n`; the general theorem needs `N ≥ 2`
for a balanced cut to exist, which `n ≥ 1` ensures. -/
theorem hardFunction_rectangle_cover
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))
    (D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)))
    (hDNNF : D.IsDNNF) (hDcomputes : D.Computes (fun x ↦ ¬hardFunction ranks hn a x)) :
    ∃ (r : ℕ) (_ : BalancedRectangleCover (fun x ↦ ¬hardFunction ranks hn a x) (Fin r)),
      r ≤ 2 * D.edgeCount + 1 := by
  have hnn : 1 * 1 ≤ n * n := Nat.mul_le_mul hn hn
  have hVar : 2 ≤ Fintype.card (Fin (encodedInputCount n)) := by
    rw [Fintype.card_fin]
    show 2 ≤ 60 * (n * n)
    omega
  exact D.rectangle_cover hVar hDNNF hDcomputes

/-- A DNNF with unrestricted fan-in has a balanced rectangle cover
quadratic in its number of nodes. Repeated inputs in the internal circuit
model are removed before converting to binary gates. -/
@[tutorial_box "lem:tutorial-edge-cover"]
theorem balanced_rectangle_cover
    {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin (encodedInputCount n) → ((Fin n × Fin n) → GadgetVector))
    (D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)))
    (hDNNF : D.IsDNNF) (hDcomputes : D.Computes (fun x ↦ ¬hardFunction ranks hn a x)) :
    ∃ (r : ℕ) (_ : BalancedRectangleCover (fun x ↦ ¬hardFunction ranks hn a x) (Fin r)),
      r ≤ 7 * D.size ^ 2 := by
  obtain ⟨r, cover, hr⟩ := hardFunction_rectangle_cover ranks hn a D.dedup
    (D.dedup_isDNNF hDNNF) (D.dedup_computes hDcomputes)
  refine ⟨r, cover, ?_⟩
  have hsize : 1 ≤ D.size := by
    change 0 < Fintype.card D.Gate
    exact Fintype.card_pos_iff.mpr ⟨D.output⟩
  have he := D.edgeCount_dedup_le
  nlinarith

end DDNNFNegation
