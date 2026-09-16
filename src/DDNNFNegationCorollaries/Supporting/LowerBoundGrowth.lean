import DDNNFNegationCorollaries.Supporting.NodeCountBounds
import DDNNFNegation.Separation

/-! # Growth of the circuit lower bound

The lower bound exceeds the size of a constant circuit, ensuring that the
complement distribution used by the probabilistic corollary is nonempty.
-/

namespace DDNNFNegation

theorem spectralNodeLower_gt_one {n : ℕ} (hn : 300 ≤ n) :
    1 < spectralNodeLower n := by
  have he := inv_spectral_eq_exp n
  have hr := separationRate_ge
  have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp := Real.add_one_le_exp (separationRate * (n : ℝ)^2)
  have hε := spectralEpsilon_pos n
  have hlarge : (448 : ℝ) < Real.exp (separationRate * (n : ℝ)^2) := by
    nlinarith [sq_nonneg ((n : ℝ) - 300)]
  have hi : 1 < 1 / (64 * spectralEpsilon n) / 7 := by
    have heq : 1 / (64 * spectralEpsilon n) / 7 =
        Real.exp (separationRate * (n : ℝ)^2) / 448 := by
      calc _ = (1 / (128 * spectralEpsilon n)) * (2 / 7) := by field_simp; ring
        _ = _ := by rw [he]; ring
    rw [heq]
    linarith
  exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hi)

end DDNNFNegation
