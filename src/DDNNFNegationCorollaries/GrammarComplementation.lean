import DDNNFNegationCorollaries.Supporting.FiniteLanguageSeparation
import TutorialBox

/-!
# Complementation of unambiguous finite-language grammars

The hard language has a small unambiguous right-linear grammar. Every
context-free grammar for its complement on the relevant word lengths
gives a DNNF, so the circuit lower bound yields a grammar lower bound.
The proof accounts separately for grammar description size and the
source parameter used by the fixed-length parsing construction.
-/

namespace DDNNFNegation

open Finset

/-! ## The paper's size measure -/

/-- Productions plus right-hand-side symbol occurrences. -/
noncomputable def descriptionSize {T : Type*} (G : ContextFreeGrammar T) : ℕ :=
  G.rules.card + ∑ rule ∈ G.rules, rule.output.length

/-- Every production is `A → ε`, `A → b`, or `A → b B`. -/
def IsRightLinear {T : Type*} (G : ContextFreeGrammar T) : Prop :=
  ∀ rule ∈ G.rules, rule.output = [] ∨
    (∃ b : T, rule.output = [.terminal b]) ∨
    ∃ (b : T) (B : G.NT), rule.output = [.terminal b, .nonterminal B]

/-! ## Deleting unused nonterminals -/

/-- The nonterminals occurring in a symbol string. -/
def symbolNonterminals {T N : Type*} : List (Symbol T N) → List N
  | [] => []
  | .terminal _ :: rest => symbolNonterminals rest
  | .nonterminal A :: rest => A :: symbolNonterminals rest

theorem mem_symbolNonterminals {T N : Type*} (A : N) (l : List (Symbol T N)) :
    A ∈ symbolNonterminals l ↔ Symbol.nonterminal A ∈ l := by
  induction l with
  | nil => simp [symbolNonterminals]
  | cons s rest ih =>
      cases s with
      | terminal t => simp [symbolNonterminals, ih]
      | nonterminal B => simp [symbolNonterminals, ih]

theorem length_symbolNonterminals_le {T N : Type*} (l : List (Symbol T N)) :
    (symbolNonterminals l).length ≤ l.length := by
  induction l with
  | nil => simp [symbolNonterminals]
  | cons s rest ih =>
      cases s with
      | terminal t => simp [symbolNonterminals]; omega
      | nonterminal B => simp [symbolNonterminals]; omega

/-- Sums over an image are at most the sums over the source. -/
theorem sum_image_le_sum {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (g : β → ℕ) : ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.image_insert, Finset.sum_insert ha]
      by_cases hmem : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hmem]
        omega
      · rw [Finset.sum_insert hmem]
        omega

end DDNNFNegation

namespace ContextFreeGrammar

open DDNNFNegation

section generic

variable {T : Type*} (G : ContextFreeGrammar T) [DecidableEq G.NT]

/-- The nonterminals a production mentions. -/
def ruleNonterminals (rule : ContextFreeRule T G.NT) : Finset G.NT :=
  insert rule.input (symbolNonterminals rule.output).toFinset

/-- The start symbol and every nonterminal some production mentions. -/
def used : Finset G.NT :=
  insert G.initial (G.rules.biUnion G.ruleNonterminals)

theorem initial_mem_used : G.initial ∈ G.used :=
  Finset.mem_insert_self _ _

theorem input_mem_used {rule : ContextFreeRule T G.NT} (hrule : rule ∈ G.rules) :
    rule.input ∈ G.used := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨rule, hrule, Finset.mem_insert_self _ _⟩

theorem output_mem_used {rule : ContextFreeRule T G.NT} (hrule : rule ∈ G.rules)
    {A : G.NT} (hA : Symbol.nonterminal A ∈ rule.output) : A ∈ G.used := by
  apply Finset.mem_insert_of_mem
  refine Finset.mem_biUnion.mpr ⟨rule, hrule, Finset.mem_insert_of_mem ?_⟩
  rw [List.mem_toFinset, mem_symbolNonterminals]
  exact hA

theorem card_used_le : G.used.card ≤ descriptionSize G + 1 := by
  unfold used descriptionSize
  calc (insert G.initial (G.rules.biUnion G.ruleNonterminals)).card
      ≤ (G.rules.biUnion G.ruleNonterminals).card + 1 := Finset.card_insert_le _ _
    _ ≤ (∑ rule ∈ G.rules, (G.ruleNonterminals rule).card) + 1 := by
        exact Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ rule ∈ G.rules, (1 + rule.output.length)) + 1 := by
        apply Nat.add_le_add_right
        apply Finset.sum_le_sum
        intro rule _
        unfold ruleNonterminals
        calc (insert rule.input (symbolNonterminals rule.output).toFinset).card
            ≤ (symbolNonterminals rule.output).toFinset.card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (symbolNonterminals rule.output).length + 1 :=
              Nat.add_le_add_right (List.toFinset_card_le _) 1
          _ ≤ 1 + rule.output.length := by
              have := length_symbolNonterminals_le rule.output
              omega
    _ = G.rules.card + (∑ rule ∈ G.rules, rule.output.length) + 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]

/-- The nonterminals of the restricted grammar. -/
abbrev UsedNT := {A : G.NT // A ∈ G.used}

/-- Send a nonterminal to its copy; a nonterminal that is not used, and hence
occurs in no production, is sent to the start symbol. -/
def liftNT (A : G.NT) : G.UsedNT :=
  if h : A ∈ G.used then ⟨A, h⟩ else ⟨G.initial, G.initial_mem_used⟩

theorem liftNT_val {A : G.NT} (h : A ∈ G.used) : (G.liftNT A).1 = A := by
  unfold liftNT
  rw [dif_pos h]

/-- Lift a symbol string to the restricted grammar. -/
def liftSym : Symbol T G.NT → Symbol T G.UsedNT
  | .terminal t => .terminal t
  | .nonterminal A => .nonterminal (G.liftNT A)

/-- Forget the restriction. -/
def lowerSym : Symbol T G.UsedNT → Symbol T G.NT
  | .terminal t => .terminal t
  | .nonterminal A => .nonterminal A.1

/-- A symbol string mentioning only used nonterminals. -/
def Good (u : List (Symbol T G.NT)) : Prop :=
  ∀ A, Symbol.nonterminal A ∈ u → A ∈ G.used

theorem good_append {u v : List (Symbol T G.NT)} (hu : G.Good u) (hv : G.Good v) :
    G.Good (u ++ v) := by
  intro A hA
  rcases List.mem_append.mp hA with h | h
  · exact hu A h
  · exact hv A h

theorem good_of_append_left {u v : List (Symbol T G.NT)} (h : G.Good (u ++ v)) :
    G.Good u :=
  fun A hA ↦ h A (List.mem_append_left _ hA)

theorem good_of_append_right {u v : List (Symbol T G.NT)} (h : G.Good (u ++ v)) :
    G.Good v :=
  fun A hA ↦ h A (List.mem_append_right _ hA)

theorem good_output {rule : ContextFreeRule T G.NT} (hrule : rule ∈ G.rules) :
    G.Good rule.output :=
  fun _ hA ↦ G.output_mem_used hrule hA

theorem map_lowerSym_map_liftSym {u : List (Symbol T G.NT)} (hu : G.Good u) :
    (u.map G.liftSym).map G.lowerSym = u := by
  rw [List.map_map]
  refine (List.map_congr_left ?_).trans (List.map_id u)
  intro s hs
  cases s with
  | terminal t => rfl
  | nonterminal A =>
      simp only [Function.comp, liftSym, lowerSym, id]
      rw [G.liftNT_val (hu A hs)]

theorem map_lowerSym_map_terminal (w : List T) :
    (w.map (Symbol.terminal (N := G.UsedNT))).map G.lowerSym = w.map Symbol.terminal := by
  rw [List.map_map]
  rfl

theorem map_liftSym_map_terminal (w : List T) :
    (w.map (Symbol.terminal (N := G.NT))).map G.liftSym = w.map Symbol.terminal := by
  rw [List.map_map]
  rfl

/-- The production with its nonterminals restricted. -/
def restrictRule (rule : ContextFreeRule T G.NT) : ContextFreeRule T G.UsedNT :=
  ⟨G.liftNT rule.input, rule.output.map G.liftSym⟩

variable [DecidableEq T]

/-- The grammar without its unused nonterminals. -/
noncomputable abbrev restrict : ContextFreeGrammar T where
  NT := G.UsedNT
  initial := ⟨G.initial, G.initial_mem_used⟩
  rules := G.rules.image G.restrictRule

theorem mem_restrict_rules (rule : ContextFreeRule T G.UsedNT) :
    rule ∈ G.restrict.rules ↔ ∃ source ∈ G.rules, G.restrictRule source = rule :=
  Finset.mem_image

theorem restrict_initial : G.restrict.initial = ⟨G.initial, G.initial_mem_used⟩ := rfl

theorem liftNT_initial : G.liftNT G.initial = G.restrict.initial := by
  rw [restrict_initial]
  unfold liftNT
  rw [dif_pos G.initial_mem_used]

/-- Derivations of the restricted grammar are derivations of the original. -/
theorem derives_of_restrict_derives {u v : List (Symbol T G.UsedNT)}
    (h : G.restrict.Derives u v) :
    G.Derives (u.map G.lowerSym) (v.map G.lowerSym) := by
  induction h with
  | refl => exact ContextFreeGrammar.Derives.refl _
  | tail _ hstep ih =>
      refine ih.trans_produces ?_
      obtain ⟨rule', hrule', hrewrites⟩ := hstep
      obtain ⟨rule, hrule, rfl⟩ := (G.mem_restrict_rules rule').mp hrule'
      obtain ⟨p, q, rfl, rfl⟩ := hrewrites.exists_parts
      refine ⟨rule, hrule, ?_⟩
      simp only [restrictRule, List.map_append, List.map_cons, List.map_nil, lowerSym]
      rw [G.liftNT_val (G.input_mem_used hrule),
        G.map_lowerSym_map_liftSym (G.good_output hrule)]
      exact ContextFreeRule.rewrites_of_exists_parts rule _ _

/-- Derivations of the original grammar from a string of used nonterminals
stay among used nonterminals and lift to the restricted grammar. -/
theorem restrict_derives_of_derives {u v : List (Symbol T G.NT)} (hu : G.Good u)
    (h : G.Derives u v) :
    G.Good v ∧ G.restrict.Derives (u.map G.liftSym) (v.map G.liftSym) := by
  induction h with
  | refl => exact ⟨hu, ContextFreeGrammar.Derives.refl _⟩
  | tail _ hstep ih =>
      obtain ⟨hgood, hderives⟩ := ih
      obtain ⟨rule, hrule, hrewrites⟩ := hstep
      obtain ⟨p, q, rfl, rfl⟩ := hrewrites.exists_parts
      refine ⟨?_, hderives.trans_produces ?_⟩
      · exact G.good_append (G.good_append (G.good_of_append_left
          (G.good_of_append_left hgood)) (G.good_output hrule))
          (G.good_of_append_right hgood)
      · refine ⟨G.restrictRule rule, (G.mem_restrict_rules _).mpr ⟨rule, hrule, rfl⟩, ?_⟩
        simp only [List.map_append, List.map_cons, List.map_nil, liftSym]
        exact ContextFreeRule.rewrites_of_exists_parts (G.restrictRule rule) _ _

/-- Deleting unused nonterminals keeps the language. -/
theorem restrict_language (w : List T) : w ∈ G.restrict.language ↔ w ∈ G.language := by
  rw [ContextFreeGrammar.mem_language_iff, ContextFreeGrammar.mem_language_iff]
  constructor
  · intro h
    have h' := G.derives_of_restrict_derives h
    rw [G.map_lowerSym_map_terminal] at h'
    exact h'
  · intro h
    have hgood : G.Good [Symbol.nonterminal G.initial] := by
      intro A hA
      rw [List.mem_singleton, Symbol.nonterminal.injEq] at hA
      rw [hA]
      exact G.initial_mem_used
    have h' := (G.restrict_derives_of_derives hgood h).2
    rw [G.map_liftSym_map_terminal, List.map_cons, List.map_nil] at h'
    have hinit : G.liftSym (Symbol.nonterminal G.initial) =
        Symbol.nonterminal G.restrict.initial := by
      simp only [liftSym, liftNT_initial]
    rw [hinit] at h'
    exact h'

instance : Fintype G.restrict.NT := by
  change Fintype G.UsedNT
  infer_instance

instance : DecidableEq G.restrict.NT := by
  change DecidableEq G.UsedNT
  infer_instance

end generic

section bool

open DDNNFNegation.CFGBinarization

variable (G : ContextFreeGrammar Bool) [DecidableEq G.NT]

/-- The restricted grammar's source parameter is controlled by the paper's
description size of the original. -/
theorem sourceParameter_restrict_le :
    sourceParameter G.restrict ≤ 2 * descriptionSize G + 1 := by
  classical
  unfold sourceParameter
  have hcard : Fintype.card G.restrict.NT = G.used.card := by
    change Fintype.card G.UsedNT = _
    exact Fintype.card_coe _
  have hsum : (∑ rule : RuleRef G.restrict, rule.1.output.length) ≤
      ∑ rule ∈ G.rules, rule.output.length := by
    rw [Finset.sum_coe_sort (G.restrict.rules) (fun rule ↦ rule.output.length)]
    change (∑ rule ∈ G.rules.image G.restrictRule, rule.output.length) ≤ _
    refine (sum_image_le_sum G.rules G.restrictRule (fun rule ↦ rule.output.length)).trans ?_
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro rule _
    simp [restrictRule]
  have hused := G.card_used_le
  have hsize : (∑ rule ∈ G.rules, rule.output.length) ≤ descriptionSize G := by
    unfold descriptionSize
    omega
  omega

end bool

end ContextFreeGrammar

namespace DDNNFNegation

open CFGBinarization

/-! ## The positive grammar is right-linear -/

theorem encodedOuterRightLinearCFG_isRightLinear {n bitCount : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n)
    (a : Fin bitCount → ((Fin n × Fin n) → GadgetVector)) :
    IsRightLinear (encodedOuterRightLinearCFG ranks hn a) := by
  classical
  intro rule hrule
  change rule ∈ (encodedOuterAutomaton ranks hn a).toRightLinearCFG.rules at hrule
  rcases (encodedOuterAutomaton ranks hn a).toRightLinearCFG_rule_shape rule hrule with
    ⟨q, _, hrule⟩ | ⟨q, b, r, _, hrule⟩
  · left
    rw [hrule]
    rfl
  · right
    right
    exact ⟨b, r, by rw [hrule]; rfl⟩

/-! ## The corollary -/

/-- Grammar complementation, in the paper's size measure.  For one
choice of label orders and encoder, the length-`N` language of `L_n`
(`N = encodedInputCount n`) has a right-linear grammar with unique parses
and description size at most `3 · candidatePositiveGrammarRuleBound n`,
which is `2^{O(n)}`; and every context-free grammar `H`, over any
nonterminal type, whose language agrees with the complement of that
language on the words of length `N` has description size at least
`(cfgDescriptionExponentialLower n − N − 4) / 2`, which is `2^{Ω(n²)}`. -/
@[tutorial_box "cor:paper-grammar"]
theorem grammar_complementation (n : ℕ) (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
    ∃ a : Fin (encodedInputCount n) →
        ((Fin n × Fin n) → GadgetVector),
      (∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ (encodedOuterRightLinearCFG ranks hn a).language ↔
          hardFunction ranks hn a x) ∧
      IsRightLinear (encodedOuterRightLinearCFG ranks hn a) ∧
      (∀ word : List Bool,
        Subsingleton (encodedOuterRightLinearParse ranks hn a word)) ∧
      descriptionSize (encodedOuterRightLinearCFG ranks hn a) ≤
        3 * candidatePositiveGrammarRuleBound n ∧
      ∀ H : ContextFreeGrammar Bool,
        (∀ x : Fin (encodedInputCount n) → Bool,
          List.ofFn x ∈ H.language ↔ ¬hardFunction ranks hn a x) →
        cfgDescriptionExponentialLower n ≤
          (2 * descriptionSize H + encodedInputCount n + 4 : ℕ) := by
  classical
  obtain ⟨ranks, a, _C, hwidth, _hdet, _hcomputes, _hsize, hlower⟩ :=
    exists_candidate_dDNNF_width_and_complement_DNNF_lower_bound n hn
  have hstates :
      Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState ≤
        candidatePositiveGrammarStateBound n := by
    calc
      Fintype.card (encodedTermAutomatonFamily ranks hn a).UnionState ≤
          1 + Fintype.card (ThresholdTerm n) *
            ((encodedInputCount n + 1) * 16 ^ (10 * n)) :=
        encodedOuterAutomaton_state_card_le_of_width ranks hn a hwidth
      _ ≤ 1 + (n * 2 ^ n) *
            ((encodedInputCount n + 1) * 16 ^ (10 * n)) := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ (card_thresholdTerm_le n)
      _ = candidatePositiveGrammarStateBound n := rfl
  have hrules :
      (encodedOuterRightLinearCFG ranks hn a).rules.card ≤
        candidatePositiveGrammarRuleBound n := by
    apply (encodedOuterRightLinear_rule_card_le ranks hn a).trans
    apply Nat.add_le_add hstates
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hstates) hstates
  have hrhs := encodedOuterRightLinear_rhsSymbolCount_le ranks hn a
  rw [Finset.sum_coe_sort (encodedOuterRightLinearCFG ranks hn a).rules
    (fun rule ↦ rule.output.length)] at hrhs
  refine ⟨ranks, a, encodedOuterRightLinearCFG_language_iff ranks hn a,
    encodedOuterRightLinearCFG_isRightLinear ranks hn a,
    encodedOuterRightLinearCFG_parse_subsingleton ranks hn a, ?_, ?_⟩
  · unfold descriptionSize
    omega
  · intro H hH
    have hH' : ∀ x : Fin (encodedInputCount n) → Bool,
        List.ofFn x ∈ H.restrict.language ↔ ¬hardFunction ranks hn a x := by
      intro x
      rw [H.restrict_language]
      exact hH x
    have h := complement_CFG_exponential_description_lower_bound_of_DNNF_lower_bound
      ranks hn a hlower H.restrict hH'
    have hparam := H.sourceParameter_restrict_le
    calc cfgDescriptionExponentialLower n
        ≤ ((sourceParameter H.restrict + encodedInputCount n + 3 : ℕ) : ℝ) := h
      _ ≤ ((2 * descriptionSize H + encodedInputCount n + 4 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : sourceParameter H.restrict + encodedInputCount n + 3 ≤
            2 * descriptionSize H + encodedInputCount n + 4)

end DDNNFNegation
