import DDNNFNegation.OBDD
import DDNNFNegationConsequences.AutomatonFamily

/-!
# Layered transition systems as finite-word automata

The positive construction already supplies finite-state transition systems
whose transition at layer `i` reads input bit `i`.  This file gives that
object ordinary finite-word automaton semantics and proves that, on a complete
length-`N` word, its accepting state is exactly `LayeredOBDD.runFrom`.
-/

namespace DDNNFNegation

namespace LayeredOBDD

variable {N : ℕ} {State : Type} [Fintype State] [DecidableEq State]

private def automatonNextLayer (i : Layer N) (h : i.val < N) : Layer N :=
  ⟨i.val + 1, by omega⟩

/-- The partial deterministic automaton underlying a layered transition
system.  It accepts only after exactly `N` letters have been read. -/
noncomputable def toFiniteWordAutomaton
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) :
    FiniteWordAutomaton (Gate N State) Bool where
  start := (⟨0, by omega⟩, start)
  step gate b :=
    if h : gate.1.val < N then
      {(automatonNextLayer gate.1 h,
        step ⟨gate.1.val, h⟩ gate.2 b)}
    else ∅
  final gate := gate.1.val = N ∧ accept gate.2 = true

omit [Fintype State] [DecidableEq State] in
theorem toFiniteWordAutomaton_hasAtMostOneSuccessor
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) :
    (toFiniteWordAutomaton step accept start).HasAtMostOneSuccessor := by
  intro gate b left right hleft hright
  simp only [toFiniteWordAutomaton] at hleft hright
  by_cases h : gate.1.val < N
  · simp only [h, ↓reduceDIte, Finset.mem_singleton] at hleft hright
    exact hleft.trans hright.symm
  · simp [h] at hleft

omit [Fintype State] [DecidableEq State] in
theorem toFiniteWordAutomaton_isUnambiguous
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) :
    (toFiniteWordAutomaton step accept start).IsUnambiguous :=
  (toFiniteWordAutomaton step accept start).isUnambiguous_of_hasAtMostOneSuccessor
    (toFiniteWordAutomaton_hasAtMostOneSuccessor step accept start)

omit [Fintype State] [DecidableEq State] in
/-- A run from layer `i` can accept only after reading the remaining
`N - i` letters. -/
theorem toFiniteWordAutomaton_acceptsFrom_length
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State)
    {i : Layer N} {state : State} {word : List Bool}
    (haccepts : (toFiniteWordAutomaton step accept start).ExistentialAcceptsFrom
      (i, state) word) :
    word.length = N - i.val := by
  induction word generalizing i state with
  | nil =>
      change i.val = N ∧ accept state = true at haccepts
      simp [haccepts.1]
  | cons b word ih =>
      rcases haccepts with ⟨target, hstep, htail⟩
      simp only [toFiniteWordAutomaton] at hstep
      by_cases hi : i.val < N
      · simp only [hi, ↓reduceDIte, Finset.mem_singleton] at hstep
        subst target
        have hlength := ih htail
        simp only [List.length_cons, automatonNextLayer] at hlength ⊢
        omega
      · simp [hi] at hstep

omit [Fintype State] [DecidableEq State] in
theorem toFiniteWordAutomaton_accepts_length
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) {word : List Bool}
    (haccepts : (toFiniteWordAutomaton step accept start).ExistentialAccepts
      word) :
    word.length = N := by
  exact (toFiniteWordAutomaton_acceptsFrom_length step accept start
    haccepts)

omit [Fintype State] [DecidableEq State] in
theorem toFiniteWordAutomaton_acceptsFrom_drop_iff
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State)
    (v : Fin N → Bool) (i : Layer N) (state : State) :
    (toFiniteWordAutomaton step accept start).ExistentialAcceptsFrom
        (i, state) ((List.ofFn v).drop i.val) ↔
      accept (runFrom step v i.val state) = true := by
  by_cases hi : i.val < N
  · have hilength : i.val < (List.ofFn v).length := by simpa using hi
    rw [List.drop_eq_getElem_cons hilength]
    simp only [List.getElem_ofFn,
      FiniteWordAutomaton.ExistentialAcceptsFrom]
    have hdrop :
        (List.ofFn v).drop (i.val + 1) =
          (List.ofFn v).drop (automatonNextLayer i hi).val := rfl
    simp only [toFiniteWordAutomaton, hi, ↓reduceDIte, Finset.mem_singleton]
    rw [runFrom_of_lt step v i.val state hi]
    constructor
    · rintro ⟨gate, rfl, htail⟩
      rw [hdrop] at htail
      exact (toFiniteWordAutomaton_acceptsFrom_drop_iff
        step accept start v (automatonNextLayer i hi) _).mp htail
    · intro htail
      refine ⟨_, rfl, ?_⟩
      rw [hdrop]
      exact (toFiniteWordAutomaton_acceptsFrom_drop_iff
        step accept start v (automatonNextLayer i hi) _).mpr htail
  · have hiN : i.val = N := by omega
    have hdrop : (List.ofFn v).drop i.val = [] := by
      apply List.drop_eq_nil_of_le
      simp [hiN]
    rw [hdrop]
    simp only [FiniteWordAutomaton.ExistentialAcceptsFrom,
      toFiniteWordAutomaton, hiN, true_and]
    rw [runFrom]
    simp
termination_by N - i.val
decreasing_by
  all_goals
    change N - (i.val + 1) < N - i.val
    omega

omit [Fintype State] [DecidableEq State] in
/-- On a full length-`N` word, automaton acceptance is exactly the terminal
predicate applied to the layered transition run. -/
theorem toFiniteWordAutomaton_accepts_iff
    (step : Fin N → State → Bool → State)
    (accept : State → Bool) (start : State) (v : Fin N → Bool) :
    (toFiniteWordAutomaton step accept start).ExistentialAccepts
        (List.ofFn v) ↔
      accept (runFrom step v 0 start) = true := by
  unfold FiniteWordAutomaton.ExistentialAccepts
  change
    (toFiniteWordAutomaton step accept start).ExistentialAcceptsFrom
        ((⟨0, by omega⟩ : Layer N), start) (List.ofFn v) ↔ _
  simpa only [List.drop_zero] using
    (toFiniteWordAutomaton_acceptsFrom_drop_iff step accept start v
      (⟨0, by omega⟩ : Layer N) start)

end LayeredOBDD

end DDNNFNegation
