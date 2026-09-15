import DDNNFNegationConsequences.AutomatonDuality
import DDNNFNegationConsequences.ExtendedCFGStandardSemantics

/-!
# Converting a finite automaton to a grammar

Use states as nonterminals, a rule `q → a r` for every transition, and
`q → ε` at accepting states. The derivation lemmas identify the grammar's
language with the automaton's. A binary presentation supports the circuit
construction for fixed-length words.
-/

namespace DDNNFNegation

namespace FiniteWordAutomaton

variable {State : Type} [Fintype State] [DecidableEq State]

/-! ## Accepting runs and unambiguity -/

/-- An accepting run, retaining the chosen successor at every position. -/
inductive AcceptingRunFrom (A : FiniteWordAutomaton State Bool) :
    State → List Bool → Type where
  | empty {q : State} (final : A.final q) : A.AcceptingRunFrom q []
  | letter {q r : State} {b : Bool} {word : List Bool}
      (step : r ∈ A.step q b)
      (tail : A.AcceptingRunFrom r word) :
      A.AcceptingRunFrom q (b :: word)

/-- The automaton is unambiguous when every word has at most one accepting
run from its start state. -/
def IsUnambiguous (A : FiniteWordAutomaton State Bool) : Prop :=
  ∀ word, Subsingleton (A.AcceptingRunFrom A.start word)

omit [Fintype State] [DecidableEq State] in
theorem nonempty_acceptingRunFrom_iff
    (A : FiniteWordAutomaton State Bool) (q : State) (word : List Bool) :
    Nonempty (A.AcceptingRunFrom q word) ↔
      A.ExistentialAcceptsFrom q word := by
  induction word generalizing q with
  | nil =>
      constructor
      · rintro ⟨run⟩
        cases run with
        | empty hfinal => exact hfinal
      · exact fun hfinal ↦ ⟨.empty hfinal⟩
  | cons b word ih =>
      constructor
      · rintro ⟨run⟩
        cases run with
        | letter hstep tail =>
            exact ⟨_, hstep, (ih _).mp ⟨tail⟩⟩
      · rintro ⟨r, hstep, htail⟩
        obtain ⟨tail⟩ := (ih r).mpr htail
        exact ⟨.letter hstep tail⟩

omit [Fintype State] [DecidableEq State] in
theorem nonempty_acceptingRun_iff
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    Nonempty (A.AcceptingRunFrom A.start word) ↔
      A.ExistentialAccepts word :=
  A.nonempty_acceptingRunFrom_iff A.start word

/-- A semantic determinism condition for a transition relation. -/
def HasAtMostOneSuccessor (A : FiniteWordAutomaton State Bool) : Prop :=
  ∀ q b r s, r ∈ A.step q b → s ∈ A.step q b → r = s

omit [Fintype State] [DecidableEq State] in
private theorem acceptingRunFrom_subsingleton_of_deterministic
    (A : FiniteWordAutomaton State Bool)
    (hdet : A.HasAtMostOneSuccessor) (q : State) (word : List Bool) :
    Subsingleton (A.AcceptingRunFrom q word) := by
  induction word generalizing q with
  | nil =>
      constructor
      intro left right
      cases left with
      | empty hleft =>
          cases right with
          | empty hright =>
              congr
  | cons b word ih =>
      constructor
      intro left right
      cases left with
      | @letter _ r _ _ hleftStep leftTail =>
          cases right with
          | @letter _ s _ _ hrightStep rightTail =>
              have hrs : r = s := hdet q b r s hleftStep hrightStep
              subst s
              have htail : leftTail = rightTail :=
                (ih r).allEq leftTail rightTail
              subst rightTail
              congr

omit [Fintype State] [DecidableEq State] in
theorem isUnambiguous_of_hasAtMostOneSuccessor
    (A : FiniteWordAutomaton State Bool)
    (hdet : A.HasAtMostOneSuccessor) : A.IsUnambiguous := by
  intro word
  exact acceptingRunFrom_subsingleton_of_deterministic A hdet A.start word

/-! ## The right-linear grammar -/

/-- State nonterminals and one terminal proxy for each Boolean letter. -/
abbrev RightLinearNonterminal (State : Type) := Sum State Bool

def stateNonterminal (q : State) : RightLinearNonterminal State := Sum.inl q

def terminalProxy (b : Bool) : RightLinearNonterminal State := Sum.inr b

def IsAutomatonEpsilonRule (A : FiniteWordAutomaton State Bool)
    (X : RightLinearNonterminal State) : Prop :=
  ∃ q, A.final q ∧ X = stateNonterminal q

def IsAutomatonTerminalRule
    (entry : RightLinearNonterminal State × Bool) : Prop :=
  ∃ b, entry = (terminalProxy b, b)

def IsAutomatonBinaryRule (A : FiniteWordAutomaton State Bool)
    (entry : RightLinearNonterminal State ×
      RightLinearNonterminal State × RightLinearNonterminal State) : Prop :=
  ∃ q b r, r ∈ A.step q b ∧
    entry = (stateNonterminal q, terminalProxy b, stateNonterminal r)

/-- The right-linear grammar associated with a Boolean finite automaton.
The binary rule `q -> P_b r` represents the transition `q -b-> r`, and
`P_b -> b` emits the letter. -/
noncomputable def toExtendedRightLinearCFG
    (A : FiniteWordAutomaton State Bool) :
    ExtendedBinaryCFG (RightLinearNonterminal State) := by
  classical
  exact
    { start := stateNonterminal A.start
      epsilonRules := Finset.univ.filter (IsAutomatonEpsilonRule A)
      terminalRules := Finset.univ.filter IsAutomatonTerminalRule
      unitRules := ∅
      binaryRules := Finset.univ.filter (IsAutomatonBinaryRule A) }

omit [DecidableEq State] in
@[simp] theorem mem_toExtendedRightLinearCFG_epsilon
    (A : FiniteWordAutomaton State Bool)
    (X : RightLinearNonterminal State) :
    X ∈ A.toExtendedRightLinearCFG.epsilonRules ↔
      IsAutomatonEpsilonRule A X := by
  classical
  simp [toExtendedRightLinearCFG]

omit [DecidableEq State] in
@[simp] theorem mem_toExtendedRightLinearCFG_terminal
    (A : FiniteWordAutomaton State Bool)
    (entry : RightLinearNonterminal State × Bool) :
    entry ∈ A.toExtendedRightLinearCFG.terminalRules ↔
      IsAutomatonTerminalRule entry := by
  classical
  simp [toExtendedRightLinearCFG]

omit [DecidableEq State] in
@[simp] theorem mem_toExtendedRightLinearCFG_unit
    (A : FiniteWordAutomaton State Bool)
    (entry : RightLinearNonterminal State × RightLinearNonterminal State) :
    entry ∉ A.toExtendedRightLinearCFG.unitRules := by
  simp [toExtendedRightLinearCFG]

omit [DecidableEq State] in
@[simp] theorem mem_toExtendedRightLinearCFG_binary
    (A : FiniteWordAutomaton State Bool)
    (entry : RightLinearNonterminal State ×
      RightLinearNonterminal State × RightLinearNonterminal State) :
    entry ∈ A.toExtendedRightLinearCFG.binaryRules ↔
      IsAutomatonBinaryRule A entry := by
  classical
  simp [toExtendedRightLinearCFG]

omit [DecidableEq State] in
theorem final_epsilon_mem (A : FiniteWordAutomaton State Bool)
    {q : State} (hfinal : A.final q) :
    stateNonterminal q ∈ A.toExtendedRightLinearCFG.epsilonRules := by
  rw [mem_toExtendedRightLinearCFG_epsilon]
  exact ⟨q, hfinal, rfl⟩

omit [DecidableEq State] in
theorem proxy_terminal_mem (A : FiniteWordAutomaton State Bool) (b : Bool) :
    (terminalProxy b, b) ∈ A.toExtendedRightLinearCFG.terminalRules := by
  rw [mem_toExtendedRightLinearCFG_terminal]
  exact ⟨b, rfl⟩

omit [DecidableEq State] in
theorem transition_binary_mem (A : FiniteWordAutomaton State Bool)
    {q r : State} {b : Bool} (hstep : r ∈ A.step q b) :
    (stateNonterminal q, terminalProxy b, stateNonterminal r) ∈
      A.toExtendedRightLinearCFG.binaryRules := by
  rw [mem_toExtendedRightLinearCFG_binary]
  exact ⟨q, b, r, hstep, rfl⟩

omit [Fintype State] [DecidableEq State] in
private def rightLinearMeaning (A : FiniteWordAutomaton State Bool) :
    RightLinearNonterminal State → List Bool → Prop
  | .inl q, word => A.ExistentialAcceptsFrom q word
  | .inr b, word => word = [b]

omit [DecidableEq State] in
private theorem wordDerives_implies_rightLinearMeaning
    (A : FiniteWordAutomaton State Bool)
    {X : RightLinearNonterminal State} {word : List Bool}
    (h : A.toExtendedRightLinearCFG.WordDerives X word) :
    rightLinearMeaning A X word := by
  induction h with
  | @epsilon X hrule =>
      rw [mem_toExtendedRightLinearCFG_epsilon] at hrule
      rcases hrule with ⟨q, hfinal, rfl⟩
      exact hfinal
  | @terminal X b hrule =>
      rw [mem_toExtendedRightLinearCFG_terminal] at hrule
      rcases hrule with ⟨value, hentry⟩
      injection hentry with hX hb
      subst X
      subst b
      rfl
  | @unit X Y word hrule child ih =>
      simp [toExtendedRightLinearCFG] at hrule
  | @binary X Y Z left right hrule leftDerives rightDerives ihLeft ihRight =>
      rw [mem_toExtendedRightLinearCFG_binary] at hrule
      rcases hrule with ⟨q, b, r, hstep, hentry⟩
      have hX : X = stateNonterminal q := by
        simpa only using congrArg Prod.fst hentry
      have hY : Y = terminalProxy b := by
        simpa only using congrArg (fun p ↦ p.2.1) hentry
      have hZ : Z = stateNonterminal r := by
        simpa only using congrArg (fun p ↦ p.2.2) hentry
      subst X
      subst Y
      subst Z
      change left = [b] at ihLeft
      change A.ExistentialAcceptsFrom r right at ihRight
      subst left
      exact ⟨r, hstep, ihRight⟩

omit [DecidableEq State] in
theorem terminalProxy_wordDerives_iff
    (A : FiniteWordAutomaton State Bool) (b : Bool) (word : List Bool) :
    A.toExtendedRightLinearCFG.WordDerives (terminalProxy b) word ↔
      word = [b] := by
  constructor
  · exact wordDerives_implies_rightLinearMeaning A
  · rintro rfl
    exact .terminal (proxy_terminal_mem A b)

omit [DecidableEq State] in
theorem state_wordDerives_iff_acceptsFrom
    (A : FiniteWordAutomaton State Bool) (q : State) (word : List Bool) :
    A.toExtendedRightLinearCFG.WordDerives (stateNonterminal q) word ↔
      A.ExistentialAcceptsFrom q word := by
  constructor
  · exact wordDerives_implies_rightLinearMeaning A
  · intro haccepts
    induction word generalizing q with
    | nil =>
        exact .epsilon (final_epsilon_mem A haccepts)
    | cons b word ih =>
        rcases haccepts with ⟨r, hstep, htail⟩
        simpa using ExtendedBinaryCFG.WordDerives.binary
          (transition_binary_mem A hstep)
          (ExtendedBinaryCFG.WordDerives.terminal (proxy_terminal_mem A b))
          (ih r htail)

omit [DecidableEq State] in
theorem wordDerives_start_iff_accepts
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    A.toExtendedRightLinearCFG.WordDerives
        A.toExtendedRightLinearCFG.start word ↔
      A.ExistentialAccepts word := by
  exact A.state_wordDerives_iff_acceptsFrom A.start word

/-- The actual Mathlib CFG produced by the translation recognizes exactly the
automaton language under standard reflexive-transitive rewriting semantics. -/
theorem mem_rightLinear_language_iff_accepts
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    word ∈ A.toExtendedRightLinearCFG.toContextFreeGrammar.language ↔
      A.ExistentialAccepts word := by
  rw [← A.toExtendedRightLinearCFG.wordDerives_start_iff_mem_standard_language]
  exact A.wordDerives_start_iff_accepts word

/-- Run-shaped parse data for the automaton grammars.  For the direct grammar
below, the two constructors correspond exactly to `q -> epsilon` and
`q -> b r`. -/
def RightLinearParse (A : FiniteWordAutomaton State Bool)
    (word : List Bool) : Type :=
  A.AcceptingRunFrom A.start word

theorem rightLinear_parse_exists_iff_mem_language
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    Nonempty (A.RightLinearParse word) ↔
      word ∈ A.toExtendedRightLinearCFG.toContextFreeGrammar.language := by
  unfold RightLinearParse
  rw [A.nonempty_acceptingRun_iff, A.mem_rightLinear_language_iff_accepts]

omit [Fintype State] [DecidableEq State] in
theorem rightLinear_parse_subsingleton
    (A : FiniteWordAutomaton State Bool) (hA : A.IsUnambiguous)
    (word : List Bool) : Subsingleton (A.RightLinearParse word) :=
  hA word

/-! ## Direct conventional right-linear grammar -/

/-- The direct right-linear rules are `q -> epsilon` at a final state and
`q -> b r` for an automaton transition `q -b-> r`. -/
def IsDirectRightLinearRule (A : FiniteWordAutomaton State Bool)
    (rule : ContextFreeRule Bool State) : Prop :=
  (∃ q, A.final q ∧ rule = ⟨q, []⟩) ∨
  (∃ q b r, r ∈ A.step q b ∧
    rule = ⟨q, [.terminal b, .nonterminal r]⟩)

private def directEpsilonRule (q : State) : ContextFreeRule Bool State :=
  ⟨q, []⟩

private def directTransitionRule (entry : State × Bool × State) :
    ContextFreeRule Bool State :=
  ⟨entry.1, [.terminal entry.2.1, .nonterminal entry.2.2]⟩

noncomputable def directRightLinearRules
    (A : FiniteWordAutomaton State Bool) :
    Finset (ContextFreeRule Bool State) := by
  classical
  exact
    (Finset.univ.filter A.final).image directEpsilonRule ∪
      Finset.univ.biUnion fun q ↦
        Finset.univ.biUnion fun b ↦
          (A.step q b).image fun r ↦ directTransitionRule (q, b, r)

/-- The conventional right-linear CFG associated with an automaton.  Unlike
the binary implementation above, this grammar writes a terminal directly in
front of the unique nonterminal on a transition rule. -/
noncomputable def toRightLinearCFG (A : FiniteWordAutomaton State Bool) :
    ContextFreeGrammar Bool where
  NT := State
  initial := A.start
  rules := directRightLinearRules A

@[simp] theorem mem_toRightLinearCFG_rules
    (A : FiniteWordAutomaton State Bool)
    (rule : ContextFreeRule Bool State) :
    rule ∈ A.toRightLinearCFG.rules ↔ IsDirectRightLinearRule A rule := by
  classical
  change rule ∈ directRightLinearRules A ↔ _
  simp [directRightLinearRules, IsDirectRightLinearRule,
    directEpsilonRule, directTransitionRule]
  aesop

theorem direct_final_rule_mem (A : FiniteWordAutomaton State Bool)
    {q : State} (hfinal : A.final q) :
    (⟨q, []⟩ : ContextFreeRule Bool State) ∈ A.toRightLinearCFG.rules := by
  rw [mem_toRightLinearCFG_rules]
  exact Or.inl ⟨q, hfinal, rfl⟩

theorem direct_transition_rule_mem (A : FiniteWordAutomaton State Bool)
    {q r : State} {b : Bool} (hstep : r ∈ A.step q b) :
    (⟨q, [.terminal b, .nonterminal r]⟩ :
      ContextFreeRule Bool State) ∈ A.toRightLinearCFG.rules := by
  rw [mem_toRightLinearCFG_rules]
  exact Or.inr ⟨q, b, r, hstep, rfl⟩

@[simp] theorem direct_epsilon_rule_mem_iff
    (A : FiniteWordAutomaton State Bool) (q : State) :
    (⟨q, []⟩ : ContextFreeRule Bool State) ∈ A.toRightLinearCFG.rules ↔
      A.final q := by
  rw [mem_toRightLinearCFG_rules]
  simp [IsDirectRightLinearRule]

@[simp] theorem direct_transition_rule_mem_iff
    (A : FiniteWordAutomaton State Bool) (q r : State) (b : Bool) :
    (⟨q, [.terminal b, .nonterminal r]⟩ :
      ContextFreeRule Bool State) ∈ A.toRightLinearCFG.rules ↔
      r ∈ A.step q b := by
  rw [mem_toRightLinearCFG_rules]
  simp [IsDirectRightLinearRule]

/-- Every production has conventional right-linear shape: either an empty
production or one terminal followed by one nonterminal. -/
theorem toRightLinearCFG_rule_shape
    (A : FiniteWordAutomaton State Bool)
    (rule : ContextFreeRule Bool State) (hrule : rule ∈ A.toRightLinearCFG.rules) :
    (∃ q, A.final q ∧ rule = ⟨q, []⟩) ∨
    (∃ q b r, r ∈ A.step q b ∧
      rule = ⟨q, [.terminal b, .nonterminal r]⟩) :=
  (A.mem_toRightLinearCFG_rules rule).mp hrule

/-! ## Parse trees of the direct grammar -/

/-- A syntactic parse tree for the direct grammar, with the grammar production
used at every node retained as data. -/
inductive DirectRightLinearParseFrom (A : FiniteWordAutomaton State Bool) :
    State → List Bool → Type where
  | empty {q : State}
      (rule : (⟨q, []⟩ : ContextFreeRule Bool State) ∈
        A.toRightLinearCFG.rules) :
      A.DirectRightLinearParseFrom q []
  | letter {q r : State} {b : Bool} {word : List Bool}
      (rule : (⟨q, [.terminal b, .nonterminal r]⟩ :
        ContextFreeRule Bool State) ∈ A.toRightLinearCFG.rules)
      (tail : A.DirectRightLinearParseFrom r word) :
      A.DirectRightLinearParseFrom q (b :: word)

def DirectRightLinearParse (A : FiniteWordAutomaton State Bool)
    (word : List Bool) : Type :=
  A.DirectRightLinearParseFrom A.start word

omit [Fintype State] [DecidableEq State] in
private def DirectRightLinearParseFrom.toAcceptingRun
    (A : FiniteWordAutomaton State Bool) :
    A.DirectRightLinearParseFrom q word → A.AcceptingRunFrom q word
  | .empty rule => .empty ((A.direct_epsilon_rule_mem_iff q).mp rule)
  | .letter rule tail =>
      .letter ((A.direct_transition_rule_mem_iff _ _ _).mp rule)
        (tail.toAcceptingRun A)

private def DirectRightLinearParseFrom.ofAcceptingRun
    (A : FiniteWordAutomaton State Bool) :
    A.AcceptingRunFrom q word → A.DirectRightLinearParseFrom q word
  | .empty final =>
      .empty ((A.direct_epsilon_rule_mem_iff q).mpr final)
  | .letter step tail =>
      .letter ((A.direct_transition_rule_mem_iff _ _ _).mpr step)
        (DirectRightLinearParseFrom.ofAcceptingRun A tail)

private theorem DirectRightLinearParseFrom.of_to
    (A : FiniteWordAutomaton State Bool)
    (parse : A.DirectRightLinearParseFrom q word) :
    DirectRightLinearParseFrom.ofAcceptingRun A
      (parse.toAcceptingRun A) = parse := by
  induction parse with
  | empty => congr
  | letter _ _ ih => simp only [toAcceptingRun, ofAcceptingRun]; congr

private theorem AcceptingRunFrom.to_of
    (A : FiniteWordAutomaton State Bool)
    (run : A.AcceptingRunFrom q word) :
    (DirectRightLinearParseFrom.ofAcceptingRun A run).toAcceptingRun A = run := by
  induction run with
  | empty => congr
  | letter _ _ ih => simp only [DirectRightLinearParseFrom.ofAcceptingRun,
      DirectRightLinearParseFrom.toAcceptingRun]; congr

/-- Direct right-linear grammar parse trees are exactly automaton accepting
runs. -/
def directRightLinearParseFromEquiv
    (A : FiniteWordAutomaton State Bool) (q : State) (word : List Bool) :
    A.DirectRightLinearParseFrom q word ≃ A.AcceptingRunFrom q word where
  toFun := DirectRightLinearParseFrom.toAcceptingRun A
  invFun := DirectRightLinearParseFrom.ofAcceptingRun A
  left_inv := DirectRightLinearParseFrom.of_to A
  right_inv := AcceptingRunFrom.to_of A

/-- The direct grammar has at most one final rule per state and one rule per
labeled transition.  Thus the automaton-to-grammar translation has linear
description overhead. -/
theorem toRightLinearCFG_rule_card_le
    (A : FiniteWordAutomaton State Bool) :
    A.toRightLinearCFG.rules.card ≤
      Fintype.card State + A.transitionEntryCount := by
  classical
  change (directRightLinearRules A).card ≤ _
  unfold directRightLinearRules
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · exact Finset.card_image_le.trans
      (Finset.card_le_card (Finset.filter_subset _ _))
  · calc
      (Finset.univ.biUnion fun q : State ↦
          Finset.univ.biUnion fun b : Bool ↦
            (A.step q b).image fun r ↦
              directTransitionRule (q, b, r)).card ≤
          ∑ q : State,
            (Finset.univ.biUnion fun b : Bool ↦
              (A.step q b).image fun r ↦
                directTransitionRule (q, b, r)).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ q : State, ∑ b : Bool, (A.step q b).card := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.card_biUnion_le.trans
        apply Finset.sum_le_sum
        intro b hb
        exact Finset.card_image_le
      _ = A.transitionEntryCount := rfl

omit [DecidableEq State] in
theorem transitionEntryCount_le_two_mul_state_sq
    (A : FiniteWordAutomaton State Bool) :
    A.transitionEntryCount ≤
      2 * Fintype.card State * Fintype.card State := by
  unfold transitionEntryCount
  calc
    (∑ q : State, ∑ b : Bool, (A.step q b).card) ≤
        ∑ _q : State, ∑ _b : Bool, Fintype.card State := by
          apply Finset.sum_le_sum
          intro q hq
          apply Finset.sum_le_sum
          intro b hb
          exact Finset.card_le_univ _
    _ = 2 * Fintype.card State * Fintype.card State := by
      simp [mul_comm]

theorem toRightLinearCFG_rule_card_le_state_sq
    (A : FiniteWordAutomaton State Bool) :
    A.toRightLinearCFG.rules.card ≤
      Fintype.card State +
        2 * Fintype.card State * Fintype.card State :=
  (A.toRightLinearCFG_rule_card_le).trans
    (Nat.add_le_add_left A.transitionEntryCount_le_two_mul_state_sq _)

private theorem direct_derives_of_acceptsFrom
    (A : FiniteWordAutomaton State Bool) (q : State) (word : List Bool)
    (haccepts : A.ExistentialAcceptsFrom q word) :
    A.toRightLinearCFG.Derives [.nonterminal q]
      (word.map Symbol.terminal) := by
  induction word generalizing q with
  | nil =>
      exact (show A.toRightLinearCFG.Produces [.nonterminal q] [] from
        ⟨⟨q, []⟩, direct_final_rule_mem A haccepts,
          ContextFreeRule.Rewrites.input_output⟩).single
  | cons b word ih =>
      rcases haccepts with ⟨r, hstep, htail⟩
      have hfirst : A.toRightLinearCFG.Produces [.nonterminal q]
          [.terminal b, .nonterminal r] :=
        ⟨⟨q, [.terminal b, .nonterminal r]⟩,
          direct_transition_rule_mem A hstep,
          ContextFreeRule.Rewrites.input_output⟩
      apply hfirst.trans_derives
      simpa [List.map_cons] using
        (ih r htail).append_left [.terminal b]

private inductive DirectTree (A : FiniteWordAutomaton State Bool) :
    Symbol Bool State → List Bool → Prop where
  | terminal (b : Bool) : DirectTree A (.terminal b) [b]
  | nonterminal {q : State} {word : List Bool}
      (run : A.AcceptingRunFrom q word) :
      DirectTree A (.nonterminal q) word

private inductive DirectForest (A : FiniteWordAutomaton State Bool) :
    List (Symbol Bool State) → List Bool → Prop where
  | nil : DirectForest A [] []
  | cons {symbol : Symbol Bool State}
      {symbols : List (Symbol Bool State)} {left right : List Bool}
      (head : DirectTree A symbol left)
      (rest : DirectForest A symbols right) :
      DirectForest A (symbol :: symbols) (left ++ right)

omit [Fintype State] [DecidableEq State] in
private theorem direct_terminal_forest (A : FiniteWordAutomaton State Bool)
    (word : List Bool) :
    DirectForest A (word.map Symbol.terminal) word := by
  induction word with
  | nil => exact .nil
  | cons b word ih =>
      simpa using DirectForest.cons (DirectTree.terminal b) ih

omit [Fintype State] [DecidableEq State] in
private theorem DirectForest.split_append
    (A : FiniteWordAutomaton State Bool)
    {front suffix : List (Symbol Bool State)} {word : List Bool}
    (h : DirectForest A (front ++ suffix) word) :
    ∃ left right,
      word = left ++ right ∧
      DirectForest A front left ∧ DirectForest A suffix right := by
  induction front generalizing word with
  | nil => exact ⟨[], word, rfl, .nil, h⟩
  | cons symbol remaining ih =>
      cases h with
      | cons head rest =>
          rcases ih rest with ⟨left, right, hword, hleft, hright⟩
          refine ⟨_, right, ?_, .cons head hleft, hright⟩
          rw [hword, List.append_assoc]

private theorem directTree_of_rule_forest
    (A : FiniteWordAutomaton State Bool)
    (rule : ContextFreeRule Bool State) (hrule : rule ∈ A.toRightLinearCFG.rules)
    {word : List Bool} (hforest : DirectForest A rule.output word) :
    DirectTree A (.nonterminal rule.input) word := by
  rw [mem_toRightLinearCFG_rules] at hrule
  rcases hrule with hepsilon | htransition
  · rcases hepsilon with ⟨q, hfinal, rfl⟩
    cases hforest
    exact .nonterminal (.empty hfinal)
  · rcases htransition with ⟨q, b, r, hstep, rfl⟩
    cases hforest with
    | cons first rest =>
        cases first with
        | terminal =>
            cases rest with
            | cons second suffix =>
                cases second with
                | nonterminal run =>
                    cases suffix
                    simpa using DirectTree.nonterminal
                      (AcceptingRunFrom.letter hstep run)

private theorem directForest_of_rule_head
    (A : FiniteWordAutomaton State Bool)
    (rule : ContextFreeRule Bool State) (hrule : rule ∈ A.toRightLinearCFG.rules)
    (suffix : List (Symbol Bool State)) {word : List Bool}
    (hforest : DirectForest A (rule.output ++ suffix) word) :
    DirectForest A (.nonterminal rule.input :: suffix) word := by
  rcases hforest.split_append A with
    ⟨left, right, rfl, hleft, hright⟩
  exact .cons (directTree_of_rule_forest A rule hrule hleft) hright

private theorem directForest_of_rewrites
    (A : FiniteWordAutomaton State Bool)
    (rule : ContextFreeRule Bool State) (hrule : rule ∈ A.toRightLinearCFG.rules)
    {before after : List (Symbol Bool State)}
    (hrewrite : rule.Rewrites before after) {word : List Bool}
    (hforest : DirectForest A after word) : DirectForest A before word := by
  induction hrewrite generalizing word with
  | head suffix =>
      exact directForest_of_rule_head A rule hrule suffix hforest
  | cons symbol _ ih =>
      cases hforest with
      | cons head rest => exact .cons head (ih rest)

private theorem directForest_of_produces
    (A : FiniteWordAutomaton State Bool)
    {before after : List (Symbol Bool State)}
    (hstep : A.toRightLinearCFG.Produces before after) {word : List Bool}
    (hforest : DirectForest A after word) : DirectForest A before word := by
  rcases hstep with ⟨rule, hrule, hrewrite⟩
  exact directForest_of_rewrites A rule hrule hrewrite hforest

private theorem directForest_of_derives
    (A : FiniteWordAutomaton State Bool)
    {symbols : List (Symbol Bool State)} {word : List Bool}
    (h : A.toRightLinearCFG.Derives symbols (word.map Symbol.terminal)) :
    DirectForest A symbols word := by
  refine Relation.ReflTransGen.head_induction_on h
    (direct_terminal_forest A word) ?_
  intro before after hstep _ ih
  exact directForest_of_produces A hstep ih

private theorem nonempty_acceptingRunFrom_of_direct_derives
    (A : FiniteWordAutomaton State Bool) (q : State) (word : List Bool)
    (h : A.toRightLinearCFG.Derives [.nonterminal q]
      (word.map Symbol.terminal)) :
    Nonempty (A.AcceptingRunFrom q word) := by
  have hforest := directForest_of_derives A h
  change DirectForest A [.nonterminal q] word at hforest
  cases hforest with
  | cons head rest =>
      cases head with
      | nonterminal run =>
          cases rest
          exact ⟨by simpa using run⟩

/-- The direct conventional right-linear grammar recognizes exactly the
automaton language under Mathlib's standard rewriting semantics. -/
theorem mem_directRightLinear_language_iff_accepts
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    word ∈ A.toRightLinearCFG.language ↔ A.ExistentialAccepts word := by
  rw [ContextFreeGrammar.mem_language_iff]
  constructor
  · intro hderives
    exact (A.nonempty_acceptingRun_iff word).mp
      (nonempty_acceptingRunFrom_of_direct_derives A A.start word hderives)
  · intro haccepts
    exact direct_derives_of_acceptsFrom A A.start word haccepts

/-- Canonical right-linear parses exist exactly for words in the direct
grammar's standard Mathlib language. -/
theorem directRightLinear_parse_exists_iff_mem_language
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    Nonempty (A.RightLinearParse word) ↔ word ∈ A.toRightLinearCFG.language := by
  unfold RightLinearParse
  rw [A.nonempty_acceptingRun_iff,
    A.mem_directRightLinear_language_iff_accepts]

/-- Syntactic parse trees of the direct grammar exist exactly for words in
its standard Mathlib language. -/
theorem directGrammar_parse_exists_iff_mem_language
    (A : FiniteWordAutomaton State Bool) (word : List Bool) :
    Nonempty (A.DirectRightLinearParse word) ↔
      word ∈ A.toRightLinearCFG.language := by
  unfold DirectRightLinearParse
  calc
    Nonempty (A.DirectRightLinearParseFrom A.start word) ↔
        Nonempty (A.AcceptingRunFrom A.start word) :=
      Equiv.nonempty_congr (A.directRightLinearParseFromEquiv A.start word)
    _ ↔ A.ExistentialAccepts word := A.nonempty_acceptingRun_iff word
    _ ↔ word ∈ A.toRightLinearCFG.language :=
      (A.mem_directRightLinear_language_iff_accepts word).symm

/-- An unambiguous automaton gives at most one syntactic parse tree for every
word in its direct right-linear grammar. -/
theorem directGrammar_parse_subsingleton
    (A : FiniteWordAutomaton State Bool) (hA : A.IsUnambiguous)
    (word : List Bool) : Subsingleton (A.DirectRightLinearParse word) := by
  unfold DirectRightLinearParse
  exact (Equiv.subsingleton_congr
    (A.directRightLinearParseFromEquiv A.start word)).mpr (hA word)

end FiniteWordAutomaton

end DDNNFNegation
