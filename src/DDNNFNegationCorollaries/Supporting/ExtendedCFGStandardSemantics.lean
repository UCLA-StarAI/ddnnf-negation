import DDNNFNegationCorollaries.Supporting.ExtendedCFGClosure
import Mathlib.Computability.ContextFreeGrammar

/-!
# Extended binary grammars and Mathlib's standard CFG semantics

The grammar permits epsilon, terminal, unit, and binary rules.  This file
relates its span derivations to terminal yields and then to Mathlib's general
reflexive-transitive rewriting semantics.  A parse-forest invariant handles
arbitrary interleavings of rewrites.
-/

namespace DDNNFNegation

namespace WordSpan

def contents {N : ℕ} (s : WordSpan N) (v : Fin N → Bool) : List Bool :=
  ((List.ofFn v).drop s.start).take s.length

@[simp] theorem contents_length {N : ℕ} (s : WordSpan N)
    (v : Fin N → Bool) : (s.contents v).length = s.length := by
  unfold contents
  rw [List.length_take_of_le]
  simp only [List.length_drop, List.length_ofFn]
  have := s.stop_le
  have := s.start_le_stop
  simp only [WordSpan.length]
  omega

theorem contents_eq_single_of_bounds {N : ℕ} (s : WordSpan N)
    (v : Fin N → Bool) (i : Fin N)
    (hstart : s.start = i.val) (hstop : s.stop = i.val + 1) :
    s.contents v = [v i] := by
  have hlength : s.length = 1 := by simp [WordSpan.length, hstart, hstop]
  unfold contents
  rw [hlength]
  have hi : s.start < (List.ofFn v).length := by
    simp [hstart]
  rw [List.take_one_drop_eq_of_lt_length hi]
  congr 2
  simp [hstart]

theorem contents_split {N : ℕ} (s : WordSpan N) (k : s.Split)
    (v : Fin N → Bool) :
    (s.left k).contents v ++ (s.right k).contents v = s.contents v := by
  unfold contents
  change
    ((List.ofFn v).drop s.start).take (k.1.val - s.start) ++
        ((List.ofFn v).drop k.1.val).take (s.stop - k.1.val) =
      ((List.ofFn v).drop s.start).take (s.stop - s.start)
  have hkStart : s.start ≤ k.1.val := by
    change s.1.1.val ≤ k.1.val
    exact k.2.1
  have hkStop : k.1.val ≤ s.stop := by
    change k.1.val ≤ s.1.2.val
    exact k.2.2
  have hdrop :
      (List.ofFn v).drop k.1.val =
        ((List.ofFn v).drop s.start).drop (k.1.val - s.start) := by
    rw [List.drop_drop]
    congr 2
    omega
  rw [hdrop, ← List.take_add]
  congr 2
  omega

@[simp] theorem full_contents {N : ℕ} (v : Fin N → Bool) :
    (WordSpan.full N).contents v = List.ofFn v := by
  simp [contents, WordSpan.full, WordSpan.length, WordSpan.start, WordSpan.stop]

end WordSpan

namespace ExtendedBinaryCFG

variable {Nonterminal : Type} [DecidableEq Nonterminal]

inductive WordDerives (G : ExtendedBinaryCFG Nonterminal) :
    Nonterminal → List Bool → Prop where
  | epsilon {A : Nonterminal} (rule_mem : A ∈ G.epsilonRules) :
      G.WordDerives A []
  | terminal {A : Nonterminal} {b : Bool}
      (rule_mem : (A, b) ∈ G.terminalRules) : G.WordDerives A [b]
  | unit {A B : Nonterminal} {word : List Bool}
      (rule_mem : (A, B) ∈ G.unitRules)
      (child : G.WordDerives B word) : G.WordDerives A word
  | binary {A B C : Nonterminal} {left right : List Bool}
      (rule_mem : (A, B, C) ∈ G.binaryRules)
      (left_derives : G.WordDerives B left)
      (right_derives : G.WordDerives C right) :
      G.WordDerives A (left ++ right)

omit [DecidableEq Nonterminal] in
theorem wordDerives_of_derivesSpan {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    {A : Nonterminal} {s : WordSpan N} (h : G.DerivesSpan v A s) :
    G.WordDerives A (s.contents v) := by
  induction h with
  | @epsilon A span hlength hrule =>
      have hempty : span.contents v = [] := List.length_eq_zero_iff.mp (by simpa)
      rw [hempty]
      exact .epsilon hrule
  | @terminal A span i hstart hstop hrule =>
      rw [span.contents_eq_single_of_bounds v i hstart hstop]
      exact .terminal hrule
  | unit hrule _ ih => exact .unit hrule ih
  | binary hrule k _ _ ihLeft ihRight =>
      rw [← WordSpan.contents_split]
      exact .binary hrule ihLeft ihRight

omit [DecidableEq Nonterminal] in
theorem derivesSpan_of_wordDerives_of_contents_eq {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    {A : Nonterminal} {word : List Bool} (h : G.WordDerives A word)
    (s : WordSpan N) (hword : s.contents v = word) :
    G.DerivesSpan v A s := by
  induction h generalizing s with
  | @epsilon A hrule =>
      apply DerivesSpan.epsilon (rule_mem := hrule)
      have := congrArg List.length hword
      simpa using this
  | @terminal A b hrule =>
      have hlength : s.length = 1 := by
        have := congrArg List.length hword
        simpa using this
      let i : Fin N := ⟨s.start, by
        have hlt : s.start < s.stop := by
          simp only [WordSpan.length] at hlength
          omega
        exact hlt.trans_le s.stop_le⟩
      have hstop : s.stop = i.val + 1 := by
        simp only [WordSpan.length] at hlength
        change s.stop = s.start + 1
        omega
      have hvalue : v i = b := by
        have hsingle := s.contents_eq_single_of_bounds v i rfl hstop
        rw [hword] at hsingle
        simpa using hsingle.symm
      exact .terminal i rfl hstop (by simpa [hvalue] using hrule)
  | @unit A B word hrule _ ih =>
      exact .unit hrule (ih s hword)
  | @binary A B C left right hrule hleft hright ihLeft ihRight =>
      have hspanLength : s.length = left.length + right.length := by
        have := congrArg List.length hword
        simpa using this
      have hsumeq : s.start + (left.length + right.length) = s.stop := by
        rw [← hspanLength]
        exact Nat.add_sub_of_le s.start_le_stop
      let boundary : Fin (N + 1) :=
        ⟨s.start + left.length, by
          have htoStop : s.start + left.length ≤ s.stop := by
            omega
          exact Nat.lt_succ_of_le (htoStop.trans s.stop_le)⟩
      have hboundary : s.1.1 ≤ boundary ∧ boundary ≤ s.1.2 := by
        change s.start ≤ s.start + left.length ∧
          s.start + left.length ≤ s.stop
        omega
      let k : s.Split := ⟨boundary, hboundary⟩
      have hparts :
          (s.left k).contents v ++ (s.right k).contents v = left ++ right :=
        (s.contents_split k v).trans hword
      have hleftLength : ((s.left k).contents v).length = left.length := by
        rw [WordSpan.contents_length]
        change boundary.val - s.start = left.length
        simp [boundary]
      have hleftWord : (s.left k).contents v = left := by
        have := congrArg (List.take left.length) hparts
        simpa [List.take_left', hleftLength] using this
      have hrightWord : (s.right k).contents v = right := by
        have := congrArg (List.drop left.length) hparts
        simpa [List.drop_left', hleftLength] using this
      exact .binary hrule k (ihLeft (s.left k) hleftWord)
        (ihRight (s.right k) hrightWord)

omit [DecidableEq Nonterminal] in
theorem derivesSpan_iff_wordDerives_contents {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    (A : Nonterminal) (s : WordSpan N) :
    G.DerivesSpan v A s ↔ G.WordDerives A (s.contents v) :=
  ⟨G.wordDerives_of_derivesSpan v,
    fun h ↦ G.derivesSpan_of_wordDerives_of_contents_eq v h s rfl⟩

private def epsilonRule (A : Nonterminal) : ContextFreeRule Bool Nonterminal :=
  ⟨A, []⟩

private def terminalRule (rule : Nonterminal × Bool) :
    ContextFreeRule Bool Nonterminal := ⟨rule.1, [.terminal rule.2]⟩

private def unitRule (rule : Nonterminal × Nonterminal) :
    ContextFreeRule Bool Nonterminal := ⟨rule.1, [.nonterminal rule.2]⟩

private def binaryRule (rule : Nonterminal × Nonterminal × Nonterminal) :
    ContextFreeRule Bool Nonterminal :=
  ⟨rule.1, [.nonterminal rule.2.1, .nonterminal rule.2.2]⟩

def toContextFreeGrammar (G : ExtendedBinaryCFG Nonterminal) :
    ContextFreeGrammar Bool where
  NT := Nonterminal
  initial := G.start
  rules := G.epsilonRules.image epsilonRule ∪
    G.terminalRules.image terminalRule ∪
    G.unitRules.image unitRule ∪ G.binaryRules.image binaryRule

private theorem epsilonRule_mem (G : ExtendedBinaryCFG Nonterminal)
    {A : Nonterminal} (h : A ∈ G.epsilonRules) :
    epsilonRule A ∈ G.toContextFreeGrammar.rules := by
  change epsilonRule A ∈
    G.epsilonRules.image epsilonRule ∪ G.terminalRules.image terminalRule ∪
      G.unitRules.image unitRule ∪ G.binaryRules.image binaryRule
  simp only [Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Finset.mem_image.mpr ⟨A, h, rfl⟩)))

private theorem terminalRule_mem (G : ExtendedBinaryCFG Nonterminal)
    {A : Nonterminal} {b : Bool} (h : (A, b) ∈ G.terminalRules) :
    terminalRule (A, b) ∈ G.toContextFreeGrammar.rules := by
  change terminalRule (A, b) ∈
    G.epsilonRules.image epsilonRule ∪ G.terminalRules.image terminalRule ∪
      G.unitRules.image unitRule ∪ G.binaryRules.image binaryRule
  simp only [Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr
    (Finset.mem_image.mpr ⟨(A, b), h, rfl⟩)))

private theorem unitRule_mem (G : ExtendedBinaryCFG Nonterminal)
    {A B : Nonterminal} (h : (A, B) ∈ G.unitRules) :
    unitRule (A, B) ∈ G.toContextFreeGrammar.rules := by
  change unitRule (A, B) ∈
    G.epsilonRules.image epsilonRule ∪ G.terminalRules.image terminalRule ∪
      G.unitRules.image unitRule ∪ G.binaryRules.image binaryRule
  simp only [Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨(A, B), h, rfl⟩))

private theorem binaryRule_mem (G : ExtendedBinaryCFG Nonterminal)
    {A B C : Nonterminal} (h : (A, B, C) ∈ G.binaryRules) :
    binaryRule (A, B, C) ∈ G.toContextFreeGrammar.rules := by
  change binaryRule (A, B, C) ∈
    G.epsilonRules.image epsilonRule ∪ G.terminalRules.image terminalRule ∪
      G.unitRules.image unitRule ∪ G.binaryRules.image binaryRule
  simp only [Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨(A, B, C), h, rfl⟩)

private theorem standard_derives_of_wordDerives
    (G : ExtendedBinaryCFG Nonterminal) {A : Nonterminal} {word : List Bool}
    (h : G.WordDerives A word) :
    G.toContextFreeGrammar.Derives [.nonterminal A]
      (word.map Symbol.terminal) := by
  induction h with
  | epsilon hrule =>
      apply ContextFreeGrammar.Produces.single
      exact ⟨epsilonRule _, epsilonRule_mem G hrule,
        ContextFreeRule.Rewrites.input_output⟩
  | terminal hrule =>
      apply ContextFreeGrammar.Produces.single
      exact ⟨terminalRule _, terminalRule_mem G hrule,
        ContextFreeRule.Rewrites.input_output⟩
  | @unit A B word hrule _ ih =>
      have hroot : G.toContextFreeGrammar.Produces
          [.nonterminal A] [.nonterminal B] :=
        ⟨unitRule _, unitRule_mem G hrule,
          ContextFreeRule.Rewrites.input_output⟩
      exact hroot.trans_derives ih
  | @binary A B C left right hrule _ _ ihLeft ihRight =>
      have hroot : G.toContextFreeGrammar.Produces
          [.nonterminal A] [.nonterminal B, .nonterminal C] :=
        ⟨binaryRule _, binaryRule_mem G hrule,
          ContextFreeRule.Rewrites.input_output⟩
      have hleft' := ihLeft.append_right [.nonterminal C]
      have hright' := ihRight.append_left (left.map Symbol.terminal)
      simpa [List.map_append, List.append_assoc] using
        hroot.trans_derives (hleft'.trans hright')

private inductive ForestDerives (G : ExtendedBinaryCFG Nonterminal) :
    List (Symbol Bool Nonterminal) → List Bool → Prop where
  | nil : G.ForestDerives [] []
  | terminal {b : Bool} {symbols : List (Symbol Bool Nonterminal)}
      {word : List Bool} (tail : G.ForestDerives symbols word) :
      G.ForestDerives (.terminal b :: symbols) (b :: word)
  | nonterminal {A : Nonterminal} {symbols : List (Symbol Bool Nonterminal)}
      {left right : List Bool} (head : G.WordDerives A left)
      (tail : G.ForestDerives symbols right) :
      G.ForestDerives (.nonterminal A :: symbols) (left ++ right)

omit [DecidableEq Nonterminal] in
private theorem terminals_forest (G : ExtendedBinaryCFG Nonterminal)
    (word : List Bool) : G.ForestDerives (word.map Symbol.terminal) word := by
  induction word with
  | nil => exact .nil
  | cons b word ih => exact .terminal ih

private theorem rule_mem_cases (G : ExtendedBinaryCFG Nonterminal)
    {rule : ContextFreeRule Bool Nonterminal}
    (h : rule ∈ G.toContextFreeGrammar.rules) :
    (∃ A, A ∈ G.epsilonRules ∧ rule = epsilonRule A) ∨
    (∃ A b, (A, b) ∈ G.terminalRules ∧ rule = terminalRule (A, b)) ∨
    (∃ A B, (A, B) ∈ G.unitRules ∧ rule = unitRule (A, B)) ∨
    ∃ A B C, (A, B, C) ∈ G.binaryRules ∧
      rule = binaryRule (A, B, C) := by
  change rule ∈
    G.epsilonRules.image epsilonRule ∪ G.terminalRules.image terminalRule ∪
      G.unitRules.image unitRule ∪ G.binaryRules.image binaryRule at h
  simp only [Finset.mem_union, Finset.mem_image] at h
  rcases h with ((⟨source, hsource, rfl⟩ | ⟨source, hsource, rfl⟩) |
      ⟨source, hsource, rfl⟩) | ⟨source, hsource, rfl⟩
  · exact Or.inl ⟨source, hsource, rfl⟩
  · exact Or.inr (Or.inl ⟨source.1, source.2, hsource, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨source.1, source.2, hsource, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨source.1, source.2.1, source.2.2, hsource, rfl⟩))

private theorem forest_of_rule_head (G : ExtendedBinaryCFG Nonterminal)
    {rule : ContextFreeRule Bool Nonterminal}
    (hrule : rule ∈ G.toContextFreeGrammar.rules)
    (suffix : List (Symbol Bool Nonterminal)) {word : List Bool}
    (hforest : G.ForestDerives (rule.output ++ suffix) word) :
    G.ForestDerives (.nonterminal rule.input :: suffix) word := by
  rcases rule_mem_cases G hrule with
      ⟨A, hsource, rfl⟩ | ⟨A, b, hsource, rfl⟩ |
      ⟨A, B, hsource, rfl⟩ | ⟨A, B, C, hsource, rfl⟩
  · simp only [epsilonRule, List.nil_append] at hforest ⊢
    simpa using ForestDerives.nonterminal (.epsilon hsource) hforest
  · simp only [terminalRule, List.singleton_append] at hforest ⊢
    cases hforest with
    | terminal tail => exact .nonterminal (.terminal hsource) tail
  · simp only [unitRule, List.singleton_append] at hforest ⊢
    cases hforest with
    | nonterminal hhead tail => exact .nonterminal (.unit hsource hhead) tail
  · simp only [binaryRule, List.cons_append, List.nil_append] at hforest ⊢
    cases hforest with
    | nonterminal hleft tail =>
        cases tail with
        | nonterminal hright rest =>
            simpa [List.append_assoc] using
              ForestDerives.nonterminal (.binary hsource hleft hright) rest

private theorem forest_of_rewrites (G : ExtendedBinaryCFG Nonterminal)
    {rule : ContextFreeRule Bool Nonterminal}
    (hrule : rule ∈ G.toContextFreeGrammar.rules)
    {before after : List (Symbol Bool Nonterminal)}
    (hrewrite : rule.Rewrites before after) {word : List Bool}
    (hforest : G.ForestDerives after word) : G.ForestDerives before word := by
  induction hrewrite generalizing word with
  | head suffix => exact forest_of_rule_head G hrule suffix hforest
  | cons symbol _ ih =>
      cases hforest with
      | terminal tail => exact .terminal (ih tail)
      | nonterminal head tail => exact .nonterminal head (ih tail)

private theorem forest_of_produces (G : ExtendedBinaryCFG Nonterminal)
    {before after : List (Symbol Bool Nonterminal)}
    (hstep : G.toContextFreeGrammar.Produces before after)
    {word : List Bool} (hforest : G.ForestDerives after word) :
    G.ForestDerives before word := by
  rcases hstep with ⟨rule, hrule, hrewrite⟩
  exact forest_of_rewrites G hrule hrewrite hforest

private theorem forest_of_standard_derives (G : ExtendedBinaryCFG Nonterminal)
    {symbols : List (Symbol Bool Nonterminal)} {word : List Bool}
    (h : G.toContextFreeGrammar.Derives symbols
      (word.map Symbol.terminal)) : G.ForestDerives symbols word := by
  refine Relation.ReflTransGen.head_induction_on h (terminals_forest G word) ?_
  intro before after hstep _ ih
  exact forest_of_produces G hstep ih

private theorem wordDerives_of_standard_derives
    (G : ExtendedBinaryCFG Nonterminal) {A : Nonterminal} {word : List Bool}
    (h : G.toContextFreeGrammar.Derives [.nonterminal A]
      (word.map Symbol.terminal)) : G.WordDerives A word := by
  have hforest := forest_of_standard_derives G h
  change G.ForestDerives [.nonterminal A] word at hforest
  cases hforest with
  | nonterminal hhead htail =>
      cases htail
      simpa using hhead

theorem wordDerives_iff_standard_derives
    (G : ExtendedBinaryCFG Nonterminal) {A : Nonterminal} {word : List Bool} :
    G.WordDerives A word ↔
      G.toContextFreeGrammar.Derives [.nonterminal A]
        (word.map Symbol.terminal) :=
  ⟨standard_derives_of_wordDerives G, wordDerives_of_standard_derives G⟩

theorem wordDerives_start_iff_mem_standard_language
    (G : ExtendedBinaryCFG Nonterminal) {word : List Bool} :
    G.WordDerives G.start word ↔ word ∈ G.toContextFreeGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  exact G.wordDerives_iff_standard_derives

theorem derivesSpan_full_iff_mem_standard_language {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool) :
    G.DerivesSpan v G.start (WordSpan.full N) ↔
      List.ofFn v ∈ G.toContextFreeGrammar.language := by
  rw [G.derivesSpan_iff_wordDerives_contents v,
    WordSpan.full_contents,
    G.wordDerives_start_iff_mem_standard_language]

end ExtendedBinaryCFG

end DDNNFNegation
