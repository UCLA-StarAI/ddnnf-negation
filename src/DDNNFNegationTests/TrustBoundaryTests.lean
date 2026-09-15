import DDNNFNegation.CircuitTransport

/-!
# Small circuits exercising the trust boundary

Concrete circuits over the variables `ℕ`, with the verdict each
definition of `TrustBoundary.lean` must return on them.  Evaluation
facts are proved by unfolding `Circuit.eval_eq` once per position (through
the local equations `Circuit.eval_and` of the transport and `Circuit.eval_lit`
below, and their support counterparts), so they are checked by the kernel,
not by evaluation.
-/

namespace DDNNFNegation.Circuit

variable {Var : Type} (C : Circuit Var)

/-- Evaluation of a constant node, from the defining equation. -/
theorem eval_const {i : Fin C.size} {b : Bool} (h : C.node i = .const b)
    (v : Var → Bool) : C.eval v i = b := by
  rw [C.eval_eq, h]
  rfl

/-- Evaluation of a literal node, from the defining equation. -/
theorem eval_lit {i : Fin C.size} {x : Var} {b : Bool}
    (h : C.node i = .lit x b) (v : Var → Bool) :
    C.eval v i = (v x == b) := by
  rw [C.eval_eq, h]
  rfl

/-- Support of a constant node, from the defining equation. -/
theorem support_const [DecidableEq Var] {i : Fin C.size} {b : Bool}
    (h : C.node i = .const b) : C.support i = ∅ := by
  rw [C.support_eq, h]
  rfl

/-- Support of a literal node, from the defining equation. -/
theorem support_lit [DecidableEq Var] {i : Fin C.size} {x : Var} {b : Bool}
    (h : C.node i = .lit x b) : C.support i = {x} := by
  rw [C.support_eq, h]
  rfl

end DDNNFNegation.Circuit

namespace DDNNFNegation.TrustBoundaryTests

open DDNNFNegation

/-- `x₀ ∧ x₁`: literals at positions 0 and 1, the conjunction at 2.
Reducible, so that `Fin andCircuit.size` and `Fin 3` are the same type
for rewriting. -/
abbrev andCircuit : Circuit ℕ where
  size := 3
  node := ![.lit 0 true, .lit 1 true, .and {0, 1}]
  children_lt := by decide
  output := 2

theorem andCircuit_node_zero : andCircuit.node 0 = .lit 0 true := rfl

theorem andCircuit_node_one : andCircuit.node 1 = .lit 1 true := rfl

theorem andCircuit_node_two : andCircuit.node 2 = .and {0, 1} := rfl

theorem andCircuit_eval (v : ℕ → Bool) :
    andCircuit.eval v andCircuit.output = (v 0 && v 1) := by
  rw [Bool.eq_iff_iff, andCircuit.eval_and andCircuit_node_two]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, andCircuit.eval_lit andCircuit_node_zero,
    andCircuit.eval_lit andCircuit_node_one]
  cases v 0 <;> cases v 1 <;> simp

theorem andCircuit_computes : andCircuit.Computes (fun v ↦ v 0 && v 1) :=
  andCircuit_eval

theorem andCircuit_support_output :
    andCircuit.support andCircuit.output = {0, 1} := by
  rw [andCircuit.support_and andCircuit_node_two]
  simp only [Finset.biUnion_insert, Finset.singleton_biUnion,
    andCircuit.support_lit andCircuit_node_zero,
    andCircuit.support_lit andCircuit_node_one]
  decide

theorem andCircuit_isDeterministicDNNF : andCircuit.IsDeterministicDNNF := by
  refine ⟨?_, ?_⟩
  · intro i children hi left hleft right hright hne
    fin_cases i <;> simp [andCircuit] at hi
    subst children
    simp only [Finset.mem_insert, Finset.mem_singleton] at hleft hright
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · exact absurd rfl hne
    · rw [andCircuit.support_lit andCircuit_node_zero,
        andCircuit.support_lit andCircuit_node_one]
      decide
    · rw [andCircuit.support_lit andCircuit_node_one,
        andCircuit.support_lit andCircuit_node_zero]
      decide
    · exact absurd rfl hne
  · intro i children hi
    fin_cases i <;> simp [andCircuit] at hi

end DDNNFNegation.TrustBoundaryTests
