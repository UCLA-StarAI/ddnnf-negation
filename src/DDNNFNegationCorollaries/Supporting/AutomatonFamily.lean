import DDNNFNegationCorollaries.Supporting.AutomatonToCFG

/-!
# Unambiguous union of a finite family of automata

The positive construction is a finite family of deterministic term machines.
This file performs the generic operation needed there: add one fresh start
state, choose a component on the first input letter, and preserve the chosen
component afterward.  If the components are unambiguous and their accepting
languages are pairwise disjoint, the resulting automaton is unambiguous.
-/

namespace DDNNFNegation

open scoped BigOperators

/-- A finite indexed family whose component state types may differ. -/
structure FiniteAutomatonFamily (Index : Type) where
  State : Index → Type
  stateFintype : ∀ i, Fintype (State i)
  stateDecidableEq : ∀ i, DecidableEq (State i)
  automaton : ∀ i, FiniteWordAutomaton (State i) Bool

namespace FiniteAutomatonFamily

variable {Index : Type} [Fintype Index] [DecidableEq Index]

instance (F : FiniteAutomatonFamily Index) (i : Index) :
    Fintype (F.State i) := F.stateFintype i

instance (F : FiniteAutomatonFamily Index) (i : Index) :
    DecidableEq (F.State i) := F.stateDecidableEq i

/-- A fresh start state or a state tagged by its chosen component. -/
abbrev UnionState (F : FiniteAutomatonFamily Index) :=
  Sum Unit (Sigma F.State)

abbrev running (F : FiniteAutomatonFamily Index) (i : Index) (q : F.State i) :
    F.UnionState :=
  Sum.inr ⟨i, q⟩

def runningEmbedding (F : FiniteAutomatonFamily Index) (i : Index) :
    F.State i ↪ F.UnionState where
  toFun := F.running i
  inj' := by
    intro q r h
    exact sigma_mk_injective (Sum.inr.inj h)

/-- Union the family without epsilon transitions.  On the first letter the
fresh start state takes every first transition of every component. -/
noncomputable def unionAutomaton (F : FiniteAutomatonFamily Index) :
    FiniteWordAutomaton F.UnionState Bool := by
  classical
  exact
    { start := Sum.inl ()
      step
        | .inl _, b =>
            Finset.univ.biUnion fun i ↦
              ((F.automaton i).step (F.automaton i).start b).map
                (F.runningEmbedding i)
        | .inr ⟨i, q⟩, b =>
            ((F.automaton i).step q b).map (F.runningEmbedding i)
      final
        | .inl _ => ∃ i, (F.automaton i).final (F.automaton i).start
        | .inr ⟨i, q⟩ => (F.automaton i).final q }

@[simp] theorem mem_unionAutomaton_step_start
    (F : FiniteAutomatonFamily Index) (b : Bool) (target : F.UnionState) :
    target ∈ F.unionAutomaton.step F.unionAutomaton.start b ↔
      ∃ i q, q ∈ (F.automaton i).step (F.automaton i).start b ∧
        target = F.running i q := by
  classical
  simp only [unionAutomaton, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · rintro ⟨i, q, hq, rfl⟩
    exact ⟨i, q, hq, rfl⟩
  · rintro ⟨i, q, hq, rfl⟩
    exact ⟨i, q, hq, rfl⟩

@[simp] theorem mem_unionAutomaton_step_running
    (F : FiniteAutomatonFamily Index) (i : Index) (q : F.State i)
    (b : Bool) (target : F.UnionState) :
    target ∈ F.unionAutomaton.step (F.running i q) b ↔
      ∃ r, r ∈ (F.automaton i).step q b ∧ target = F.running i r := by
  classical
  change target ∈ ((F.automaton i).step q b).map (F.runningEmbedding i) ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩

@[simp] theorem unionAutomaton_final_start
    (F : FiniteAutomatonFamily Index) :
    F.unionAutomaton.final F.unionAutomaton.start ↔
      ∃ i, (F.automaton i).final (F.automaton i).start := by
  rfl

@[simp] theorem unionAutomaton_final_running
    (F : FiniteAutomatonFamily Index) (i : Index) (q : F.State i) :
    F.unionAutomaton.final (F.running i q) ↔
      (F.automaton i).final q := by
  rfl

theorem unionAutomaton_acceptsFrom_running_iff
    (F : FiniteAutomatonFamily Index) (i : Index) (q : F.State i)
    (word : List Bool) :
    F.unionAutomaton.ExistentialAcceptsFrom (F.running i q) word ↔
      (F.automaton i).ExistentialAcceptsFrom q word := by
  induction word generalizing q with
  | nil => rfl
  | cons b word ih =>
      simp only [FiniteWordAutomaton.ExistentialAcceptsFrom]
      constructor
      · rintro ⟨target, htarget, htail⟩
        rw [mem_unionAutomaton_step_running] at htarget
        rcases htarget with ⟨r, hr, rfl⟩
        exact ⟨r, hr, (ih r).mp htail⟩
      · rintro ⟨r, hr, htail⟩
        exact ⟨F.running i r,
          (mem_unionAutomaton_step_running F i q b _).mpr ⟨r, hr, rfl⟩,
          (ih r).mpr htail⟩

/-- The union automaton accepts exactly the union of the component
languages, including on the empty word. -/
theorem unionAutomaton_accepts_iff
    (F : FiniteAutomatonFamily Index) (word : List Bool) :
    F.unionAutomaton.ExistentialAccepts word ↔
      ∃ i, (F.automaton i).ExistentialAccepts word := by
  cases word with
  | nil => rfl
  | cons b word =>
      simp only [FiniteWordAutomaton.ExistentialAccepts,
        FiniteWordAutomaton.ExistentialAcceptsFrom]
      constructor
      · rintro ⟨target, htarget, htail⟩
        rw [mem_unionAutomaton_step_start] at htarget
        rcases htarget with ⟨i, q, hq, rfl⟩
        exact ⟨i, q, hq,
          (F.unionAutomaton_acceptsFrom_running_iff i q word).mp htail⟩
      · rintro ⟨i, q, hq, htail⟩
        exact ⟨F.running i q,
          (mem_unionAutomaton_step_start F b _).mpr ⟨i, q, hq, rfl⟩,
          (F.unionAutomaton_acceptsFrom_running_iff i q word).mpr htail⟩

/-! ## Run-level preservation -/

open FiniteWordAutomaton

noncomputable def liftRunningRun (F : FiniteAutomatonFamily Index) (i : Index) :
    ∀ {q : F.State i} {word : List Bool},
      (F.automaton i).AcceptingRunFrom q word →
        F.unionAutomaton.AcceptingRunFrom (F.running i q) word
  | _, _, .empty hfinal => .empty hfinal
  | _, _, @AcceptingRunFrom.letter _ _ _ r b word hstep tail =>
      .letter
        ((mem_unionAutomaton_step_running F i _ b _).mpr
          ⟨r, hstep, rfl⟩)
        (F.liftRunningRun i tail)

noncomputable def lowerRunningRun (F : FiniteAutomatonFamily Index) (i : Index) :
    ∀ {q : F.State i} {word : List Bool},
      F.unionAutomaton.AcceptingRunFrom (F.running i q) word →
        (F.automaton i).AcceptingRunFrom q word
  | _, _, .empty hfinal => .empty hfinal
  | q, _, @AcceptingRunFrom.letter _ _ _ target b word hstep tail => by
      cases target with
      | inl value =>
          exfalso
          have hex := (mem_unionAutomaton_step_running F i q b _).mp hstep
          rcases hex with ⟨r, hr, hfalse⟩
          cases hfalse
      | inr tagged =>
          rcases tagged with ⟨j, r⟩
          have hji : j = i := by
            have hex :=
              (mem_unionAutomaton_step_running F i q b _).mp hstep
            rcases hex with ⟨s, hs, heq⟩
            exact (Sigma.mk.inj_iff.mp (Sum.inr.inj heq)).1
          subst j
          have hr : r ∈ (F.automaton i).step q b := by
            have hex :=
              (mem_unionAutomaton_step_running F i q b _).mp hstep
            rcases hex with ⟨s, hs, heq⟩
            have hrs : r = s :=
              sigma_mk_injective (Sum.inr.inj heq)
            subst s
            exact hs
          exact .letter hr (F.lowerRunningRun i tail)

theorem lowerRunningRun_liftRunningRun
    (F : FiniteAutomatonFamily Index) (i : Index)
    {q : F.State i} {word : List Bool}
    (run : (F.automaton i).AcceptingRunFrom q word) :
    F.lowerRunningRun i (F.liftRunningRun i run) = run := by
  induction run with
  | empty => rfl
  | letter hstep tail ih =>
      simp only [liftRunningRun, lowerRunningRun]
      rw [ih]

theorem liftRunningRun_lowerRunningRun
    (F : FiniteAutomatonFamily Index) (i : Index)
    {q : F.State i} {word : List Bool}
    (run : F.unionAutomaton.AcceptingRunFrom (F.running i q) word) :
    F.liftRunningRun i (F.lowerRunningRun i run) = run := by
  induction word generalizing q with
  | nil =>
      cases run with
      | empty =>
          simp only [lowerRunningRun, liftRunningRun]
  | cons b word ih =>
      cases run
      case letter target hstep tail =>
          cases target with
          | inl value =>
              exfalso
              have hex :=
                (mem_unionAutomaton_step_running F i q b _).mp hstep
              rcases hex with ⟨r, hr, hfalse⟩
              cases hfalse
          | inr tagged =>
              rcases tagged with ⟨j, r⟩
              have hji : j = i := by
                have hex :=
                  (mem_unionAutomaton_step_running F i q b _).mp hstep
                rcases hex with ⟨s, hs, heq⟩
                exact (Sigma.mk.inj_iff.mp (Sum.inr.inj heq)).1
              subst j
              simp only [lowerRunningRun, liftRunningRun]
              congr
              exact ih tail

noncomputable def runningRunEquiv (F : FiniteAutomatonFamily Index) (i : Index)
    (q : F.State i) (word : List Bool) :
    F.unionAutomaton.AcceptingRunFrom (F.running i q) word ≃
      (F.automaton i).AcceptingRunFrom q word where
  toFun := F.lowerRunningRun i
  invFun := F.liftRunningRun i
  left_inv := F.liftRunningRun_lowerRunningRun i
  right_inv := F.lowerRunningRun_liftRunningRun i

abbrev ComponentRun (F : FiniteAutomatonFamily Index) (word : List Bool) :=
  Sigma fun i ↦ (F.automaton i).AcceptingRunFrom (F.automaton i).start word

noncomputable def nonemptyUnionRunToComponent (F : FiniteAutomatonFamily Index)
    (b : Bool) (word : List Bool) :
    F.unionAutomaton.AcceptingRunFrom F.unionAutomaton.start (b :: word) →
      F.ComponentRun (b :: word)
  | @AcceptingRunFrom.letter _ _ _ target _ _ hstep tail => by
      cases target with
      | inl value =>
          exfalso
          have hex := (mem_unionAutomaton_step_start F b _).mp hstep
          rcases hex with ⟨i, q, hq, hfalse⟩
          cases hfalse
      | inr tagged =>
          rcases tagged with ⟨i, q⟩
          have hq : q ∈
              (F.automaton i).step (F.automaton i).start b := by
            have hex := (mem_unionAutomaton_step_start F b _).mp hstep
            rcases hex with ⟨j, r, hr, heq⟩
            have hji : i = j :=
              (Sigma.mk.inj_iff.mp (Sum.inr.inj heq)).1
            subst j
            have hqr : q = r :=
              sigma_mk_injective (Sum.inr.inj heq)
            subst r
            exact hr
          exact ⟨i, .letter hq (F.lowerRunningRun i tail)⟩

noncomputable def componentToNonemptyUnionRun (F : FiniteAutomatonFamily Index)
    (b : Bool) (word : List Bool) :
    F.ComponentRun (b :: word) →
      F.unionAutomaton.AcceptingRunFrom F.unionAutomaton.start (b :: word)
  | ⟨i, @AcceptingRunFrom.letter _ _ _ q _ _ hstep tail⟩ =>
      .letter
        ((mem_unionAutomaton_step_start F b _).mpr ⟨i, q, hstep, rfl⟩)
        (F.liftRunningRun i tail)

theorem componentToNonemptyUnionRun_toComponent
    (F : FiniteAutomatonFamily Index) (b : Bool) (word : List Bool)
    (run : F.unionAutomaton.AcceptingRunFrom
      F.unionAutomaton.start (b :: word)) :
    F.componentToNonemptyUnionRun b word
      (F.nonemptyUnionRunToComponent b word run) = run := by
  cases run
  case letter target hstep tail =>
      rw [mem_unionAutomaton_step_start] at hstep
      rcases hstep with ⟨i, q, hq, htarget⟩
      subst target
      simp only [nonemptyUnionRunToComponent, componentToNonemptyUnionRun]
      rw [F.liftRunningRun_lowerRunningRun i tail]

theorem nonemptyUnionRunToComponent_toUnionRun
    (F : FiniteAutomatonFamily Index) (b : Bool) (word : List Bool)
    (run : F.ComponentRun (b :: word)) :
    F.nonemptyUnionRunToComponent b word
      (F.componentToNonemptyUnionRun b word run) = run := by
  rcases run with ⟨i, run⟩
  cases run
  case letter q hstep tail =>
      simp only [componentToNonemptyUnionRun, nonemptyUnionRunToComponent]
      rw [F.lowerRunningRun_liftRunningRun i tail]

noncomputable def nonemptyUnionRunEquiv (F : FiniteAutomatonFamily Index)
    (b : Bool) (word : List Bool) :
    F.unionAutomaton.AcceptingRunFrom F.unionAutomaton.start (b :: word) ≃
      F.ComponentRun (b :: word) where
  toFun := F.nonemptyUnionRunToComponent b word
  invFun := F.componentToNonemptyUnionRun b word
  left_inv := F.componentToNonemptyUnionRun_toComponent b word
  right_inv := F.nonemptyUnionRunToComponent_toUnionRun b word

/-- No word is accepted by two differently indexed component automata. -/
def HasDisjointLanguages (F : FiniteAutomatonFamily Index) : Prop :=
  ∀ {i j word},
    (F.automaton i).ExistentialAccepts word →
    (F.automaton j).ExistentialAccepts word → i = j

omit [Fintype Index] [DecidableEq Index] in
private theorem componentRun_subsingleton
    (F : FiniteAutomatonFamily Index)
    (hcomponents : ∀ i, (F.automaton i).IsUnambiguous)
    (hdisjoint : F.HasDisjointLanguages) (word : List Bool) :
    Subsingleton (F.ComponentRun word) := by
  constructor
  rintro ⟨i, left⟩ ⟨j, right⟩
  have hi : (F.automaton i).ExistentialAccepts word :=
    ((F.automaton i).nonempty_acceptingRun_iff word).mp ⟨left⟩
  have hj : (F.automaton j).ExistentialAccepts word :=
    ((F.automaton j).nonempty_acceptingRun_iff word).mp ⟨right⟩
  have hij : i = j := hdisjoint hi hj
  subst j
  have hruns : left = right := (hcomponents i word).allEq left right
  subst right
  rfl

/-- A disjoint union of unambiguous component languages is unambiguous. -/
theorem unionAutomaton_isUnambiguous
    (F : FiniteAutomatonFamily Index)
    (hcomponents : ∀ i, (F.automaton i).IsUnambiguous)
    (hdisjoint : F.HasDisjointLanguages) :
    F.unionAutomaton.IsUnambiguous := by
  intro word
  cases word with
  | nil =>
      constructor
      intro left right
      cases left with
      | empty hleft =>
          cases right with
          | empty hright => congr
  | cons b word =>
      constructor
      intro left right
      apply (F.nonemptyUnionRunEquiv b word).injective
      exact (componentRun_subsingleton F hcomponents hdisjoint
        (b :: word)).allEq _ _

end FiniteAutomatonFamily

end DDNNFNegation
