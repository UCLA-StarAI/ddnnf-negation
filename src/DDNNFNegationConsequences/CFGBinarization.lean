import DDNNFNegationConsequences.ExtendedCFGToDNNF

/-!
# Structural binarization of finite context-free grammars

This file performs only the structural part of grammar normalization.  It
keeps epsilon and unit rules.  For each source rule it adds a right-branching
chain with one auxiliary nonterminal per nonempty suffix position.  Two more
nonterminals act as terminal proxies.  Every resulting rule is epsilon,
terminal, unit, or binary, so it is accepted by `ExtendedBinaryCFG`.
-/

namespace DDNNFNegation

namespace CFGBinarization

variable (G : ContextFreeGrammar Bool)

/-- A source rule together with evidence that it belongs to the grammar. -/
abbrev RuleRef := { rule : ContextFreeRule Bool G.NT // rule ∈ G.rules }

/-- The source parameter used by the interval parser: original
nonterminals plus right-hand-side symbol occurrences. -/
noncomputable def sourceParameter [Fintype G.NT] : ℕ :=
  Fintype.card G.NT + ∑ rule : RuleRef G, rule.1.output.length

/-- A nonempty suffix position of a source rule. -/
abbrev TailRef := Sigma fun rule : RuleRef G ↦ Fin rule.1.output.length

/-- Original nonterminals, two terminal proxies, and rule-tail auxiliaries. -/
abbrev Nonterminal := Sum G.NT (Sum Bool (TailRef G))

def original (A : G.NT) : Nonterminal G := Sum.inl A

def terminalProxy (b : Bool) : Nonterminal G := Sum.inr (Sum.inl b)

def tail (t : TailRef G) : Nonterminal G := Sum.inr (Sum.inr t)

def symbolNonterminal : Symbol Bool G.NT → Nonterminal G
  | .terminal b => terminalProxy G b
  | .nonterminal A => original G A

def IsEpsilon (A : Nonterminal G) : Prop :=
  ∃ rule : RuleRef G,
    rule.1.output = [] ∧ A = original G rule.1.input

def IsTerminal (entry : Nonterminal G × Bool) : Prop :=
  ∃ b : Bool, entry = (terminalProxy G b, b)

def IsTopUnit (entry : Nonterminal G × Nonterminal G) : Prop :=
  ∃ t : TailRef G,
    t.2.val = 0 ∧ entry = (original G t.1.1.input, tail G t)

def IsLastUnit (entry : Nonterminal G × Nonterminal G) : Prop :=
  ∃ t : TailRef G,
    t.2.val + 1 = t.1.1.output.length ∧
      entry = (tail G t, symbolNonterminal G (t.1.1.output.get t.2))

def IsUnit (entry : Nonterminal G × Nonterminal G) : Prop :=
  IsTopUnit G entry ∨ IsLastUnit G entry

def IsBinary
    (entry : Nonterminal G × Nonterminal G × Nonterminal G) : Prop :=
  ∃ (t : TailRef G) (hnext : t.2.val + 1 < t.1.1.output.length),
    entry =
      (tail G t,
        symbolNonterminal G (t.1.1.output.get t.2),
        tail G ⟨t.1, ⟨t.2.val + 1, hnext⟩⟩)

/-- Structural binarization.  No epsilon or unit elimination is performed. -/
noncomputable def grammar [Fintype G.NT] [DecidableEq G.NT] :
    ExtendedBinaryCFG (Nonterminal G) := by
  classical
  exact
    { start := original G G.initial
      epsilonRules := Finset.univ.filter (IsEpsilon G)
      terminalRules := Finset.univ.filter (IsTerminal G)
      unitRules := Finset.univ.filter (IsUnit G)
      binaryRules := Finset.univ.filter (IsBinary G) }

variable [Fintype G.NT] [DecidableEq G.NT]

@[simp] theorem mem_grammar_epsilon (A : Nonterminal G) :
    A ∈ (grammar G).epsilonRules ↔ IsEpsilon G A := by
  classical
  simp [grammar]

@[simp] theorem mem_grammar_terminal (entry : Nonterminal G × Bool) :
    entry ∈ (grammar G).terminalRules ↔ IsTerminal G entry := by
  classical
  simp [grammar]

@[simp] theorem mem_grammar_unit
    (entry : Nonterminal G × Nonterminal G) :
    entry ∈ (grammar G).unitRules ↔ IsUnit G entry := by
  classical
  simp [grammar]

@[simp] theorem mem_grammar_binary
    (entry : Nonterminal G × Nonterminal G × Nonterminal G) :
    entry ∈ (grammar G).binaryRules ↔ IsBinary G entry := by
  classical
  simp [grammar]

theorem epsilon_mem {rule : ContextFreeRule Bool G.NT}
    (hrule : rule ∈ G.rules) (hempty : rule.output = []) :
    original G rule.input ∈ (grammar G).epsilonRules := by
  rw [mem_grammar_epsilon]
  exact ⟨⟨rule, hrule⟩, hempty, rfl⟩

theorem terminal_mem (b : Bool) :
    (terminalProxy G b, b) ∈ (grammar G).terminalRules := by
  rw [mem_grammar_terminal]
  exact ⟨b, rfl⟩

theorem top_unit_mem {rule : ContextFreeRule Bool G.NT}
    (hrule : rule ∈ G.rules) (hnonempty : rule.output ≠ []) :
    (original G rule.input,
      tail G ⟨⟨rule, hrule⟩,
        ⟨0, List.length_pos_iff.mpr hnonempty⟩⟩) ∈
      (grammar G).unitRules := by
  rw [mem_grammar_unit]
  exact Or.inl ⟨⟨⟨rule, hrule⟩,
    ⟨0, List.length_pos_iff.mpr hnonempty⟩⟩, rfl, rfl⟩

theorem last_unit_mem (t : TailRef G)
    (hlast : t.2.val + 1 = t.1.1.output.length) :
    (tail G t, symbolNonterminal G (t.1.1.output.get t.2)) ∈
      (grammar G).unitRules := by
  rw [mem_grammar_unit]
  exact Or.inr ⟨t, hlast, rfl⟩

theorem binary_mem (t : TailRef G)
    (hnext : t.2.val + 1 < t.1.1.output.length) :
    (tail G t,
        symbolNonterminal G (t.1.1.output.get t.2),
        tail G ⟨t.1, ⟨t.2.val + 1, hnext⟩⟩) ∈
      (grammar G).binaryRules := by
  rw [mem_grammar_binary]
  exact ⟨t, hnext, rfl⟩

/-- The source sentential form represented by one binarized nonterminal. -/
def interpretation : Nonterminal G → List (Symbol Bool G.NT)
  | .inl A => [.nonterminal A]
  | .inr (.inl b) => [.terminal b]
  | .inr (.inr t) => t.1.1.output.drop t.2.val

omit [Fintype G.NT] [DecidableEq G.NT] in
@[simp] theorem interpretation_original (A : G.NT) :
    interpretation G (original G A) = [.nonterminal A] := rfl

omit [Fintype G.NT] [DecidableEq G.NT] in
@[simp] theorem interpretation_terminalProxy (b : Bool) :
    interpretation G (terminalProxy G b) = [.terminal b] := rfl

omit [Fintype G.NT] [DecidableEq G.NT] in
@[simp] theorem interpretation_tail (t : TailRef G) :
    interpretation G (tail G t) = t.1.1.output.drop t.2.val := rfl

omit [Fintype G.NT] [DecidableEq G.NT] in
@[simp] theorem interpretation_symbolNonterminal
    (symbol : Symbol Bool G.NT) :
    interpretation G (symbolNonterminal G symbol) = [symbol] := by
  cases symbol <;> rfl

omit [Fintype G.NT] [DecidableEq G.NT] in
private theorem source_rule_step (rule : RuleRef G) :
    G.Produces [.nonterminal rule.1.input] rule.1.output :=
  ⟨rule.1, rule.2, ContextFreeRule.Rewrites.input_output⟩

/-- Every derivation created by the binarized grammar expands to a derivation
of the represented sentential form in the source grammar.  This is the
no-spurious-words direction of structural binarization. -/
theorem source_derives_of_wordDerives
    {A : Nonterminal G} {word : List Bool}
    (h : (grammar G).WordDerives A word) :
    G.Derives (interpretation G A) (word.map Symbol.terminal) := by
  induction h with
  | @epsilon A hrule =>
      rw [mem_grammar_epsilon] at hrule
      rcases hrule with ⟨rule, hempty, rfl⟩
      simpa [hempty] using (source_rule_step G rule).single
  | @terminal A b hrule =>
      rw [mem_grammar_terminal] at hrule
      rcases hrule with ⟨value, hentry⟩
      injection hentry with hA hb
      subst A
      subst b
      rfl
  | @unit A B word hrule _ ih =>
      rw [mem_grammar_unit] at hrule
      rcases hrule with htop | hlast
      · rcases htop with ⟨t, hzero, hentry⟩
        injection hentry with hA hB
        subst A
        subst B
        rw [interpretation_tail, hzero, List.drop_zero] at ih
        rw [interpretation_original]
        apply (source_rule_step G t.1).trans_derives
        exact ih
      · rcases hlast with ⟨t, hlast, hentry⟩
        injection hentry with hA hB
        subst A
        subst B
        have hdrop :
            t.1.1.output.drop t.2.val = [t.1.1.output.get t.2] := by
          rw [List.drop_eq_getElem_cons t.2.isLt]
          have hnil : t.1.1.output.drop (t.2.val + 1) = [] :=
            List.drop_eq_nil_of_le (by omega)
          rw [hnil]
          simp only [List.get_eq_getElem]
        rw [interpretation_symbolNonterminal] at ih
        rw [interpretation_tail, hdrop]
        exact ih
  | @binary A B C left right hrule _ _ ihLeft ihRight =>
      rw [mem_grammar_binary] at hrule
      rcases hrule with ⟨t, hnext, hentry⟩
      have hA : A = tail G t := by
        simpa only using congrArg Prod.fst hentry
      have hB : B = symbolNonterminal G (t.1.1.output.get t.2) := by
        simpa only using congrArg (fun p ↦ p.2.1) hentry
      have hC : C = tail G ⟨t.1, ⟨t.2.val + 1, hnext⟩⟩ := by
        simpa only using congrArg (fun p ↦ p.2.2) hentry
      subst A
      subst B
      subst C
      rw [interpretation_symbolNonterminal] at ihLeft
      rw [interpretation_tail] at ihRight
      have hleft := ihLeft.append_right
        (t.1.1.output.drop (t.2.val + 1))
      have hright := ihRight.append_left (left.map Symbol.terminal)
      have hboth := hleft.trans hright
      have hdrop :
          t.1.1.output.drop t.2.val =
            t.1.1.output.get t.2 ::
              t.1.1.output.drop (t.2.val + 1) := by
        simpa only [List.get_eq_getElem] using
          (List.drop_eq_getElem_cons t.2.isLt)
      rw [interpretation_tail, hdrop]
      simpa [List.map_append] using hboth

private inductive CompiledForest (G : ContextFreeGrammar Bool)
    [Fintype G.NT] [DecidableEq G.NT] :
    List (Symbol Bool G.NT) → List Bool → Prop where
  | nil : CompiledForest G [] []
  | cons {symbol : Symbol Bool G.NT}
      {symbols : List (Symbol Bool G.NT)} {left right : List Bool}
      (head : (grammar G).WordDerives (symbolNonterminal G symbol) left)
      (rest : CompiledForest G symbols right) :
      CompiledForest G (symbol :: symbols) (left ++ right)

private theorem terminal_forest (word : List Bool) :
    CompiledForest G (word.map Symbol.terminal) word := by
  induction word with
  | nil => exact .nil
  | cons b word ih =>
      simpa using CompiledForest.cons
        (ExtendedBinaryCFG.WordDerives.terminal (terminal_mem G b)) ih

private theorem CompiledForest.split_append
    {front suffix : List (Symbol Bool G.NT)} {word : List Bool}
    (h : CompiledForest G (front ++ suffix) word) :
    ∃ left right,
      word = left ++ right ∧
      CompiledForest G front left ∧ CompiledForest G suffix right := by
  induction front generalizing word with
  | nil => exact ⟨[], word, rfl, .nil, h⟩
  | cons symbol remaining ih =>
      cases h with
      | cons head rest =>
          rcases ih rest with ⟨left, right, hword, hleft, hright⟩
          refine ⟨_, right, ?_, .cons head hleft, hright⟩
          rw [hword, List.append_assoc]

private theorem wordDerives_tail_of_forest
    (t : TailRef G) {word : List Bool}
    (hforest : CompiledForest G
      (t.1.1.output.drop t.2.val) word) :
    (grammar G).WordDerives (tail G t) word := by
  have hdrop :
      t.1.1.output.drop t.2.val =
        t.1.1.output.get t.2 :: t.1.1.output.drop (t.2.val + 1) := by
    simpa only [List.get_eq_getElem] using
      (List.drop_eq_getElem_cons t.2.isLt)
  rw [hdrop] at hforest
  cases hforest with
  | @cons _ symbols left right head rest =>
      by_cases hlast : t.2.val + 1 = t.1.1.output.length
      · have hnil : t.1.1.output.drop (t.2.val + 1) = [] :=
          List.drop_eq_nil_of_le (by omega)
        rw [hnil] at rest
        cases rest
        simpa using ExtendedBinaryCFG.WordDerives.unit
          (last_unit_mem G t hlast) head
      · have hnext : t.2.val + 1 < t.1.1.output.length := by
          omega
        let next : TailRef G :=
          ⟨t.1, ⟨t.2.val + 1, hnext⟩⟩
        exact ExtendedBinaryCFG.WordDerives.binary
          (binary_mem G t hnext) head
          (wordDerives_tail_of_forest next rest)
termination_by t.1.1.output.length - t.2.val
decreasing_by
  omega

private theorem wordDerives_original_of_rule_forest
    (rule : RuleRef G) {word : List Bool}
    (hforest : CompiledForest G rule.1.output word) :
    (grammar G).WordDerives (original G rule.1.input) word := by
  by_cases hempty : rule.1.output = []
  · rw [hempty] at hforest
    cases hforest
    exact .epsilon (epsilon_mem G rule.2 hempty)
  · let first : Fin rule.1.output.length :=
      ⟨0, List.length_pos_iff.mpr hempty⟩
    let t : TailRef G := ⟨rule, first⟩
    apply ExtendedBinaryCFG.WordDerives.unit
      (top_unit_mem G rule.2 hempty)
    apply wordDerives_tail_of_forest (G := G) t
    simpa [t, first] using hforest

private theorem forest_of_source_rule_head
    (rule : RuleRef G) (suffix : List (Symbol Bool G.NT))
    {word : List Bool}
    (hforest : CompiledForest G (rule.1.output ++ suffix) word) :
    CompiledForest G (.nonterminal rule.1.input :: suffix) word := by
  rcases hforest.split_append with
    ⟨left, right, rfl, hleft, hright⟩
  exact .cons
    (wordDerives_original_of_rule_forest (G := G) rule hleft) hright

private theorem forest_of_source_rewrites
    (rule : RuleRef G) {before after : List (Symbol Bool G.NT)}
    (hrewrite : rule.1.Rewrites before after) {word : List Bool}
    (hforest : CompiledForest G after word) :
    CompiledForest G before word := by
  induction hrewrite generalizing word with
  | head suffix =>
      exact forest_of_source_rule_head (G := G) rule suffix hforest
  | cons symbol _ ih =>
      cases hforest with
      | cons head rest => exact .cons head (ih rest)

private theorem forest_of_source_produces
    {before after : List (Symbol Bool G.NT)}
    (hstep : G.Produces before after) {word : List Bool}
    (hforest : CompiledForest G after word) :
    CompiledForest G before word := by
  rcases hstep with ⟨rule, hrule, hrewrite⟩
  exact forest_of_source_rewrites (G := G)
    ⟨rule, hrule⟩ hrewrite hforest

private theorem forest_of_source_derives
    {symbols : List (Symbol Bool G.NT)} {word : List Bool}
    (h : G.Derives symbols (word.map Symbol.terminal)) :
    CompiledForest G symbols word := by
  refine Relation.ReflTransGen.head_induction_on h
    (terminal_forest (G := G) word) ?_
  intro before after hstep _ ih
  exact forest_of_source_produces (G := G) hstep ih

/-- Every standard source derivation compiles to a derivation in the
binarized grammar.  The proof permits arbitrary interleavings of source
rewrites. -/
theorem wordDerives_of_source_derives
    {A : G.NT} {word : List Bool}
    (h : G.Derives [.nonterminal A] (word.map Symbol.terminal)) :
    (grammar G).WordDerives (original G A) word := by
  have hforest := forest_of_source_derives (G := G) h
  change CompiledForest G [.nonterminal A] word at hforest
  cases hforest with
  | cons head rest =>
      cases rest
      simpa [symbolNonterminal] using head

theorem source_derives_iff_wordDerives
    {A : G.NT} {word : List Bool} :
    G.Derives [.nonterminal A] (word.map Symbol.terminal) ↔
      (grammar G).WordDerives (original G A) word :=
  ⟨wordDerives_of_source_derives G, fun h ↦ by
    simpa using source_derives_of_wordDerives G h⟩

/-- Structural binarization preserves the standard context-free language. -/
theorem mem_binarized_language_iff {word : List Bool} :
    word ∈ (grammar G).toContextFreeGrammar.language ↔ word ∈ G.language := by
  rw [← (grammar G).wordDerives_start_iff_mem_standard_language]
  change
    (grammar G).WordDerives (original G G.initial) word ↔ word ∈ G.language
  rw [← source_derives_iff_wordDerives G,
    ContextFreeGrammar.mem_language_iff]

theorem binarized_language_eq :
    (grammar G).toContextFreeGrammar.language = G.language := by
  ext word
  exact mem_binarized_language_iff G

/-- The shared interval circuit for an arbitrary finite Mathlib CFG computes
membership in its length-`N` slice. -/
theorem intervalCircuit_computes_source_language {N : ℕ} :
    ((grammar G).closureIntervalCircuit (N := N)).Computes
      (fun v : Fin N → Bool ↦ List.ofFn v ∈ G.language) := by
  intro v
  exact ((grammar G).closureIntervalCircuit_computes_standard_language v).trans
    (mem_binarized_language_iff G)

theorem intervalCircuit_isDNNF {N : ℕ} :
    ((grammar G).closureIntervalCircuit (N := N)).IsDNNF :=
  (grammar G).closureIntervalCircuit_isDNNF

omit [Fintype G.NT] [DecidableEq G.NT] in
/-- The number of auxiliary tail nonterminals is the total length of all
source right-hand sides. -/
theorem tailRef_card :
    Fintype.card (TailRef G) =
      ∑ rule : RuleRef G, rule.1.output.length := by
  simp [TailRef]

omit [DecidableEq G.NT] in
/-- Binarization adds two terminal proxies and one nonterminal for each
right-hand-side position. -/
theorem nonterminal_card :
    Fintype.card (Nonterminal G) =
      Fintype.card G.NT + 2 +
        ∑ rule : RuleRef G, rule.1.output.length := by
  simp [Nonterminal, Nat.add_assoc]

/-- Explicit polynomial node bound for the DNNF compiled from an arbitrary
finite CFG. -/
theorem intervalCircuit_size_le {N : ℕ} :
    let q := Fintype.card G.NT + 2 +
      ∑ rule : RuleRef G, rule.1.output.length
    ((grammar G).closureIntervalCircuit (N := N)).size ≤
      1 + 2 * N +
        (q * (N + 1) ^ 2) * q ^ 3 * (N + 1) ^ 3 +
        (q * (N + 1) ^ 2 + 1) * q * (N + 1) ^ 2 := by
  rw [← nonterminal_card G]
  exact (grammar G).closureIntervalCircuit_size_le

/-- End-to-end fixed-length compilation theorem for arbitrary finite CFGs. -/
theorem exists_intervalDNNF (N : ℕ) :
    let q := Fintype.card G.NT + 2 +
      ∑ rule : RuleRef G, rule.1.output.length
    ∃ D : NNFCircuit.{0, 0} (Fin N),
      D.Computes (fun v : Fin N → Bool ↦ List.ofFn v ∈ G.language) ∧
      D.IsDNNF ∧
      D.size ≤
        1 + 2 * N +
          (q * (N + 1) ^ 2) * q ^ 3 * (N + 1) ^ 3 +
          (q * (N + 1) ^ 2 + 1) * q * (N + 1) ^ 2 := by
  refine ⟨(grammar G).closureIntervalCircuit (N := N),
    intervalCircuit_computes_source_language (N := N) G,
    intervalCircuit_isDNNF (N := N) G,
    intervalCircuit_size_le (N := N) G⟩

end CFGBinarization

end DDNNFNegation
