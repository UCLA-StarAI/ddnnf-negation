import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

/-!
# Automaton duality and right-linear conjunctive grammars

Swapping final states exchanges existential and universal acceptance
with complementation. Universal transitions can be expressed as
right-linear conjunctive grammar productions. These definitions work
over arbitrary alphabets; the hard language later uses Boolean words.
-/

namespace DDNNFNegation

open scoped BigOperators

/-- A finite-state transition system over finite words. -/
structure FiniteWordAutomaton (State Symbol : Type*) where
  start : State
  step : State → Symbol → Finset State
  final : State → Prop

namespace FiniteWordAutomaton

variable {State Symbol : Type*} [DecidableEq State]

/-- Existential, or ordinary nondeterministic, acceptance from one state. -/
def ExistentialAcceptsFrom (A : FiniteWordAutomaton State Symbol) :
    State → List Symbol → Prop
  | q, [] => A.final q
  | q, a :: w => ∃ r ∈ A.step q a, A.ExistentialAcceptsFrom r w

/-- Universal acceptance from one state. -/
def UniversalAcceptsFrom (A : FiniteWordAutomaton State Symbol) :
    State → List Symbol → Prop
  | q, [] => A.final q
  | q, a :: w => ∀ r ∈ A.step q a, A.UniversalAcceptsFrom r w

def ExistentialAccepts (A : FiniteWordAutomaton State Symbol)
    (w : List Symbol) : Prop :=
  A.ExistentialAcceptsFrom A.start w

def UniversalAccepts (A : FiniteWordAutomaton State Symbol)
    (w : List Symbol) : Prop :=
  A.UniversalAcceptsFrom A.start w

/-- The number of successor occurrences in an explicit transition table. -/
def transitionEntryCount [Fintype State] [Fintype Symbol]
    (A : FiniteWordAutomaton State Symbol) : ℕ :=
  ∑ q : State, ∑ a : Symbol, (A.step q a).card

/-- Swap the final states.  Universal evaluation of this automaton is the
dual of existential evaluation of the original one. -/
def dual (A : FiniteWordAutomaton State Symbol) :
    FiniteWordAutomaton State Symbol where
  start := A.start
  step := A.step
  final q := ¬A.final q

/-- Add one rejecting sink and include it among the successors of every state.
This deliberately adds the sink even where the original transition was
already nonempty.  Existential acceptance is unchanged, and every transition
of the resulting automaton is visibly nonempty. -/
def withRejectingSink (A : FiniteWordAutomaton State Symbol) :
    FiniteWordAutomaton (Option State) Symbol where
  start := some A.start
  step
    | none, _ => {none}
    | some q, a => insert none ((A.step q a).image some)
  final
    | none => False
    | some q => A.final q

theorem withRejectingSink_step_nonempty
    (A : FiniteWordAutomaton State Symbol) (q : Option State) (a : Symbol) :
    (A.withRejectingSink.step q a).Nonempty := by
  cases q <;> simp [withRejectingSink]

omit [DecidableEq State] in
theorem withRejectingSink_state_card [Fintype State] :
    Fintype.card (Option State) = Fintype.card State + 1 := by
  simp

theorem withRejectingSink_step_card_none
    (A : FiniteWordAutomaton State Symbol) (a : Symbol) :
    (A.withRejectingSink.step none a).card = 1 := by
  simp [withRejectingSink]

theorem withRejectingSink_step_card_some
    (A : FiniteWordAutomaton State Symbol) (q : State) (a : Symbol) :
    (A.withRejectingSink.step (some q) a).card = (A.step q a).card + 1 := by
  change (insert none ((A.step q a).image some)).card = (A.step q a).card + 1
  calc
    _ = ((A.step q a).image some).card + 1 := by
      rw [Finset.card_insert_of_notMem]
      simp
    _ = (A.step q a).card + 1 := by
      rw [Finset.card_image_of_injective _ (Option.some_injective State)]

theorem withRejectingSink_transitionEntryCount
    [Fintype State] [Fintype Symbol]
    (A : FiniteWordAutomaton State Symbol) :
    A.withRejectingSink.transitionEntryCount =
      A.transitionEntryCount +
        (Fintype.card State + 1) * Fintype.card Symbol := by
  simp [transitionEntryCount, withRejectingSink_step_card_none,
    withRejectingSink_step_card_some, Finset.sum_add_distrib,
    Nat.add_mul]
  omega

theorem withRejectingSink_sink_never_accepts
    (A : FiniteWordAutomaton State Symbol) (w : List Symbol) :
    ¬A.withRejectingSink.ExistentialAcceptsFrom none w := by
  induction w with
  | nil => simp [ExistentialAcceptsFrom, withRejectingSink]
  | cons a w ih =>
      simpa [ExistentialAcceptsFrom, withRejectingSink] using ih

theorem withRejectingSink_acceptsFrom_iff
    (A : FiniteWordAutomaton State Symbol) (q : State) (w : List Symbol) :
    A.withRejectingSink.ExistentialAcceptsFrom (some q) w ↔
      A.ExistentialAcceptsFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      simp only [ExistentialAcceptsFrom, withRejectingSink,
        Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨r, hr, haccepts⟩
        rcases hr with rfl | hr
        · exact (A.withRejectingSink_sink_never_accepts w haccepts).elim
        · obtain ⟨s, hs, rfl⟩ := hr
          exact ⟨s, hs, (ih s).mp haccepts⟩
      · rintro ⟨r, hr, haccepts⟩
        exact ⟨some r, Or.inr ⟨r, hr, rfl⟩, (ih r).mpr haccepts⟩

theorem withRejectingSink_accepts_iff
    (A : FiniteWordAutomaton State Symbol) (w : List Symbol) :
    A.withRejectingSink.ExistentialAccepts w ↔ A.ExistentialAccepts w :=
  A.withRejectingSink_acceptsFrom_iff A.start w

omit [DecidableEq State] in
theorem universal_dual_acceptsFrom_iff_not_existential
    (A : FiniteWordAutomaton State Symbol) (q : State) (w : List Symbol) :
    A.dual.UniversalAcceptsFrom q w ↔ ¬A.ExistentialAcceptsFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      change
        (∀ r ∈ A.step q a, A.dual.UniversalAcceptsFrom r w) ↔
          ¬∃ r ∈ A.step q a, A.ExistentialAcceptsFrom r w
      constructor
      · intro allFail someSucceeds
        obtain ⟨r, hr, haccepts⟩ := someSucceeds
        exact ((ih r).mp (allFail r hr)) haccepts
      · intro noSuccess r hr
        rw [ih r]
        intro haccepts
        exact noSuccess ⟨r, hr, haccepts⟩

omit [DecidableEq State] in
theorem universal_dual_accepts_iff_not_existential
    (A : FiniteWordAutomaton State Symbol) (w : List Symbol) :
    A.dual.UniversalAccepts w ↔ ¬A.ExistentialAccepts w := by
  exact A.universal_dual_acceptsFrom_iff_not_existential A.start w

end FiniteWordAutomaton

/-- The restricted conjunctive grammars used in the downstream corollary.
`obligations q a` lists the nonterminals whose languages must all contain the
suffix after reading `a`. -/
structure RightLinearConjGrammar (Nonterminal Symbol : Type*) where
  start : Nonterminal
  obligations : Nonterminal → Symbol → Finset Nonterminal
  nullable : Nonterminal → Prop

namespace RightLinearConjGrammar

variable {Nonterminal Symbol : Type*} [DecidableEq Nonterminal]

def DerivesFrom (G : RightLinearConjGrammar Nonterminal Symbol) :
    Nonterminal → List Symbol → Prop
  | q, [] => G.nullable q
  | q, a :: w => ∀ r ∈ G.obligations q a, G.DerivesFrom r w

def Derives (G : RightLinearConjGrammar Nonterminal Symbol)
    (w : List Symbol) : Prop :=
  G.DerivesFrom G.start w

/-- The number of nonterminal occurrences in all explicit conjunctions. -/
def conjunctEntryCount [Fintype Nonterminal] [Fintype Symbol]
    (G : RightLinearConjGrammar Nonterminal Symbol) : ℕ :=
  ∑ q : Nonterminal, ∑ a : Symbol, (G.obligations q a).card

/-- Proof-tree semantics for the restricted grammar.  The empty rule proves
the empty word at a nullable nonterminal.  A letter rule proves `a :: w` at
`q` after proving `w` at every nonterminal named by the rule's conjunction. -/
inductive HasDerivation (G : RightLinearConjGrammar Nonterminal Symbol) :
    Nonterminal → List Symbol → Prop where
  | empty {q} (hq : G.nullable q) : G.HasDerivation q []
  | letter {q a w}
      (hall : ∀ r ∈ G.obligations q a, G.HasDerivation r w) :
      G.HasDerivation q (a :: w)

omit [DecidableEq Nonterminal] in
theorem hasDerivation_iff_derivesFrom
    (G : RightLinearConjGrammar Nonterminal Symbol)
    (q : Nonterminal) (w : List Symbol) :
    G.HasDerivation q w ↔ G.DerivesFrom q w := by
  induction w generalizing q with
  | nil =>
      constructor
      · intro h
        cases h with
        | empty hq => exact hq
      · exact HasDerivation.empty
  | cons a w ih =>
      constructor
      · intro h
        cases h with
        | letter hall =>
            exact fun r hr ↦ (ih r).mp (hall r hr)
      · intro hall
        exact HasDerivation.letter fun r hr ↦ (ih r).mpr (hall r hr)

def HasCompleteDerivation (G : RightLinearConjGrammar Nonterminal Symbol)
    (w : List Symbol) : Prop :=
  G.HasDerivation G.start w

omit [DecidableEq Nonterminal] in
theorem hasCompleteDerivation_iff_derives
    (G : RightLinearConjGrammar Nonterminal Symbol) (w : List Symbol) :
    G.HasCompleteDerivation w ↔ G.Derives w :=
  G.hasDerivation_iff_derivesFrom G.start w

end RightLinearConjGrammar

namespace FiniteWordAutomaton

variable {State Symbol : Type*} [DecidableEq State]

/-- Read every universal transition as one right-linear conjunctive rule. -/
def toRightLinearConj (A : FiniteWordAutomaton State Symbol) :
    RightLinearConjGrammar State Symbol where
  start := A.start
  obligations := A.step
  nullable := A.final

omit [DecidableEq State] in
theorem toRightLinearConj_obligations_card
    (A : FiniteWordAutomaton State Symbol) (q : State) (a : Symbol) :
    (A.toRightLinearConj.obligations q a).card = (A.step q a).card := rfl

omit [DecidableEq State] in
theorem toRightLinearConj_conjunctEntryCount
    [Fintype State] [Fintype Symbol]
    (A : FiniteWordAutomaton State Symbol) :
    A.toRightLinearConj.conjunctEntryCount = A.transitionEntryCount := rfl

omit [DecidableEq State] in
theorem toRightLinearConj_derivesFrom_iff_universal
    (A : FiniteWordAutomaton State Symbol) (q : State) (w : List Symbol) :
    A.toRightLinearConj.DerivesFrom q w ↔ A.UniversalAcceptsFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      simp only [RightLinearConjGrammar.DerivesFrom, toRightLinearConj,
        UniversalAcceptsFrom]
      exact forall_congr' fun r ↦ forall_congr' fun _ ↦ ih r

omit [DecidableEq State] in
theorem dual_conjGrammar_derives_iff_complement
    (A : FiniteWordAutomaton State Symbol) (w : List Symbol) :
    A.dual.toRightLinearConj.Derives w ↔ ¬A.ExistentialAccepts w := by
  rw [RightLinearConjGrammar.Derives,
    A.dual.toRightLinearConj_derivesFrom_iff_universal]
  exact A.universal_dual_accepts_iff_not_existential w

omit [DecidableEq State] in
theorem dual_conjGrammar_hasDerivation_iff_complement
    (A : FiniteWordAutomaton State Symbol) (w : List Symbol) :
    A.dual.toRightLinearConj.HasCompleteDerivation w ↔
      ¬A.ExistentialAccepts w := by
  rw [A.dual.toRightLinearConj.hasCompleteDerivation_iff_derives]
  exact A.dual_conjGrammar_derives_iff_complement w

theorem completedDualGrammar_obligations_nonempty
    (A : FiniteWordAutomaton State Symbol) (q : Option State) (a : Symbol) :
    (A.withRejectingSink.dual.toRightLinearConj.obligations q a).Nonempty := by
  simpa [dual, toRightLinearConj] using
    A.withRejectingSink_step_nonempty q a

theorem completedDualGrammar_hasDerivation_iff_complement
    (A : FiniteWordAutomaton State Symbol) (w : List Symbol) :
    A.withRejectingSink.dual.toRightLinearConj.HasCompleteDerivation w ↔
      ¬A.ExistentialAccepts w := by
  calc
    _ ↔ ¬A.withRejectingSink.ExistentialAccepts w :=
      A.withRejectingSink.dual_conjGrammar_hasDerivation_iff_complement w
    _ ↔ ¬A.ExistentialAccepts w :=
      not_congr (A.withRejectingSink_accepts_iff w)

end FiniteWordAutomaton

end DDNNFNegation
