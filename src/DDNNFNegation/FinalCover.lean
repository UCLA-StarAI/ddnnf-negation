import DDNNFNegation.ZeroFiber
import DDNNFNegation.EncoderExistence
import DDNNFNegation.CoverCount
import DDNNFNegation.RectangleReduction
import TutorialBox

/-!
# From rectangle covers to the DNNF lower bound

Fix the ranks and an encoder with large restricted images before choosing
any circuit for the complement. Every balanced zero rectangle meets the
encoder's zero fiber in only a small fraction of that fiber. Covering the
fiber therefore requires many rectangles. The circuit-to-cover reduction
first yields an internal edge lower bound, then the paper's node lower
bound `spectralNodeLower`.
-/

namespace DDNNFNegation

open Finset

noncomputable section

/-- The internal lower bound on the number of edges of a
DNNF for the complement: `1/(128 ε) - 1/2` with `ε = (2/3)^{n²/30}`
(`spectralEpsilon`). -/
def spectralEdgeLower (n : ℕ) : ℝ :=
  1 / (128 * spectralEpsilon n) - 1 / 2

/-! ### Counting a rectangle cover -/

/-- For one encoder with large restricted images, every balanced rectangle
cover of the zero-inputs has at least `1 / (64 * ε)` members. Each rectangle
meets the zero fiber in at most `64 * ε` of its relative size. The encoder
is fixed before the cover is quantified. -/
theorem exists_encoder_with_cover_lower_bound
    (n : ℕ) (hnpos : 0 < n) (ranks : LabelOrders n) :
    ∃ a : Fin (60 * (n * n)) → ((Fin n × Fin n) → GadgetVector),
      ∀ (J : Type*) [Fintype J],
        ∀ _cover : BalancedRectangleCover (fun x ↦ ¬hardFunction ranks hnpos a x) J,
          1 / (64 * spectralEpsilon n) ≤ (Fintype.card J : ℝ) := by
  obtain ⟨a, hencoder⟩ := encoder_with_large_images n hnpos
  refine ⟨a, fun J _ cover => ?_⟩
  have hZ : (0 : ℝ) < (zeroFiber a).card :=
    lt_of_lt_of_le (by positivity) (zeroFiber_card_ge gridVector_add_self a)
  have hε := spectralEpsilon_pos n
  have hcount := cover_card_lower_bound (zeroFiber a) (fun j => (cover.rectangle j).assignments)
    (64 * spectralEpsilon n * (zeroFiber a).card) (by positivity)
    (fun x hx => cover.complete x (zeroFiber_subset_zeroInputs ranks hnpos a x hx))
    (fun j => by
      rw [inter_comm]
      exact rectangle_estimate ranks hnpos a (cover.rectangle j) hencoder (cover.balanced j)
        (cover.sound j))
  rwa [show ((zeroFiber a).card : ℝ) / (64 * spectralEpsilon n * (zeroFiber a).card) =
    1 / (64 * spectralEpsilon n) by field_simp] at hcount
/-- For one encoder, every DNNF for the complement of `L_n` has at least
`1/(128 * ε) - 1/2` edges, where `ε = (2/3)^{n²/30}`. Combine the cover
upper bound `2*s + 1` with its lower bound `1/(64 * ε)`. -/
theorem DNNF_lower_bound
    (n : ℕ) (hn : 0 < n) (ranks : LabelOrders n) :
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
        spectralEdgeLower n ≤ (D.edgeCount : ℝ) := by
  obtain ⟨a, hcovers⟩ :=
    exists_encoder_with_cover_lower_bound n hn ranks
  refine ⟨a, ?_⟩
  intro D hDNNF hDcomputes
  obtain ⟨r, cover, hr⟩ := hardFunction_rectangle_cover ranks hn a D hDNNF hDcomputes
  have hcover := hcovers (Fin r) cover
  rw [Fintype.card_fin] at hcover
  have hrR : (r : ℝ) ≤ 2 * (D.edgeCount : ℝ) + 1 := by exact_mod_cast hr
  have hε : 0 < spectralEpsilon n := spectralEpsilon_pos n
  have hε' : spectralEpsilon n ≠ 0 := hε.ne'
  have hhalf : 1 / (128 * spectralEpsilon n) =
      (1 / (64 * spectralEpsilon n)) / 2 := by
    field_simp
    ring
  unfold spectralEdgeLower
  rw [hhalf]
  linarith


/-- The square-root node lower bound obtained from the quadratic
rectangle-cover reduction. Its exponential rate is half the cover rate. -/
def spectralNodeLower (n : ℕ) : ℝ :=
  Real.sqrt (1 / (64 * spectralEpsilon n) / 7)

/-- The DNNF node lower bound for the complement is `spectralNodeLower n`, asymptotically `2^{Ω(n²)}`. -/
@[tutorial_box "lem:tutorial-negative"]
theorem DNNF_lower_bound_nodes
    (n : ℕ) (hn : 0 < n) (ranks : LabelOrders n) :
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      ∀ D : NNFCircuit.{0, 0} (Fin (encodedInputCount n)),
        D.IsDNNF →
        D.Computes (fun x ↦ ¬hardFunction ranks hn a x) →
        spectralNodeLower n ≤ (D.size : ℝ) := by
  obtain ⟨a, hcovers⟩ := exists_encoder_with_cover_lower_bound n hn ranks
  refine ⟨a, ?_⟩
  intro D hDNNF hDcomputes
  obtain ⟨r, cover, hr⟩ := balanced_rectangle_cover ranks hn a D hDNNF hDcomputes
  have hcover := hcovers (Fin r) cover
  rw [Fintype.card_fin] at hcover
  have hrR : (r : ℝ) ≤ 7 * (D.size : ℝ) ^ 2 := by exact_mod_cast hr
  unfold spectralNodeLower
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · linarith

end

end DDNNFNegation
