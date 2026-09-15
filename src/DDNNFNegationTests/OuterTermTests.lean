import DDNNFNegation.OuterDNF

/-!
# Conflict below the eligibility threshold

At `n = 6`, a singleton label set is nonempty but too small to be retained
in the final DNF. The conflict lemma still applies: eligibility is needed
for the width bound, not for the conflict between distinct nonempty terms.
-/

namespace DDNNFNegationTests
open DDNNFNegation

private def singletonTerm (bucket : Fin 6) : OuterTerm 6 :=
  ⟨bucket, {0}, by simp⟩

example : ¬ 6 ≤ 3 * (singletonTerm 0).chosen.card := by decide

example (ranks : LabelOrders 6) :
    (termSigned ranks (by decide) (singletonTerm 0)).Incompatible
      (termSigned ranks (by decide) (singletonTerm 1)) := by
  apply distinct_terms_conflict
  intro h
  have := congrArg OuterTerm.bucket h
  norm_num [singletonTerm] at this

end DDNNFNegationTests
