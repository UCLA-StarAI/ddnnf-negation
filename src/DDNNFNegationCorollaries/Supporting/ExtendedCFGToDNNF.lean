import DDNNFNegationCorollaries.Supporting.AcyclicCircuitBuilder
import DDNNFNegationCorollaries.Supporting.ExtendedCFGStandardSemantics

/-!
# A DNNF parser with epsilon and unit rules

This file unrolls the finite grammar closure one round per layer.  Parse nodes
are shared across all uses.  Binary rules are the only conjunctions, and their
two children occupy disjoint half-open spans even when one child is empty.
-/

namespace DDNNFNegation

namespace ExtendedBinaryCFG

variable {Nonterminal : Type} [Fintype Nonterminal]
  [DecidableEq Nonterminal]

structure ClosureCombineIndex (Nonterminal : Type*) (N rounds : ℕ) where
  round : Fin rounds
  lhs : Nonterminal
  left : Nonterminal
  right : Nonterminal
  span : WordSpan N
  split : span.Split
deriving DecidableEq

private abbrev ClosureCombineCode (Nonterminal : Type*) (N rounds : ℕ) :=
  Fin rounds × Nonterminal × Nonterminal × Nonterminal ×
    Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

private def closureCombineCode {Nonterminal : Type*} {N rounds : ℕ} :
    ClosureCombineIndex Nonterminal N rounds →
      ClosureCombineCode Nonterminal N rounds := fun c ↦
  (c.round, c.lhs, c.left, c.right, c.span.1.1, c.span.1.2, c.split.1)

private theorem closureCombineCode_injective
    {Nonterminal : Type*} {N rounds : ℕ} :
    Function.Injective
      (closureCombineCode : ClosureCombineIndex Nonterminal N rounds →
        ClosureCombineCode Nonterminal N rounds) := by
  intro c d h
  cases c with
  | mk cr clhs cleft cright cspan csplit =>
      cases d with
      | mk dr dlhs dleft dright dspan dsplit =>
          simp only [closureCombineCode, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl, hstart, hstop, hsplit⟩
          have hspan : cspan = dspan :=
            Subtype.ext (Prod.ext hstart hstop)
          subst dspan
          have : csplit = dsplit := Subtype.ext hsplit
          subst dsplit
          rfl

private theorem wordSpan_card_le (N : ℕ) :
    Fintype.card (WordSpan N) ≤ (N + 1) ^ 2 := by
  have h := Fintype.card_le_of_injective
    (fun s : WordSpan N ↦ s.1) Subtype.val_injective
  simpa [Fintype.card_prod, pow_two] using h

noncomputable instance {Nonterminal : Type*} [Fintype Nonterminal]
    {N rounds : ℕ} : Fintype (ClosureCombineIndex Nonterminal N rounds) :=
  Fintype.ofInjective closureCombineCode closureCombineCode_injective

private theorem closureCombine_card_le
    (Nonterminal : Type*) [Fintype Nonterminal] (N rounds : ℕ) :
    Fintype.card (ClosureCombineIndex Nonterminal N rounds) ≤
      rounds * Fintype.card Nonterminal ^ 3 * (N + 1) ^ 3 := by
  have h := Fintype.card_le_of_injective closureCombineCode
    (closureCombineCode_injective
      (Nonterminal := Nonterminal) (N := N) (rounds := rounds))
  simpa [ClosureCombineCode, pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using h

inductive ClosureParserGate (Nonterminal : Type*) (N rounds : ℕ) where
  | truth
  | literal (position : Fin N) (value : Bool)
  | combine (index : ClosureCombineIndex Nonterminal N rounds)
  | parse (round : Fin (rounds + 1))
      (nonterminal : Nonterminal) (span : WordSpan N)
deriving DecidableEq

private abbrev ClosureParserGateCode (Nonterminal : Type*) (N rounds : ℕ) :=
  Sum Unit
    (Sum (Fin N × Bool)
      (Sum (ClosureCombineIndex Nonterminal N rounds)
        (Fin (rounds + 1) × Nonterminal × WordSpan N)))

private def closureParserGateCode {Nonterminal : Type*} {N rounds : ℕ} :
    ClosureParserGate Nonterminal N rounds →
      ClosureParserGateCode Nonterminal N rounds
  | .truth => Sum.inl ()
  | .literal i b => Sum.inr (Sum.inl (i, b))
  | .combine c => Sum.inr (Sum.inr (Sum.inl c))
  | .parse round A s => Sum.inr (Sum.inr (Sum.inr (round, A, s)))

private theorem closureParserGateCode_injective
    {Nonterminal : Type*} {N rounds : ℕ} :
    Function.Injective
      (closureParserGateCode : ClosureParserGate Nonterminal N rounds →
        ClosureParserGateCode Nonterminal N rounds) := by
  intro x y h
  cases x <;> cases y <;> simp [closureParserGateCode] at h
  · rfl
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · cases h
    rfl
  · rcases h with ⟨rfl, rfl, hspan⟩
    cases hspan
    rfl

noncomputable instance {Nonterminal : Type*} [Fintype Nonterminal]
    {N rounds : ℕ} : Fintype (ClosureParserGate Nonterminal N rounds) :=
  Fintype.ofInjective closureParserGateCode closureParserGateCode_injective

private theorem closureParserGate_card_le
    (Nonterminal : Type*) [Fintype Nonterminal] (N rounds : ℕ) :
    Fintype.card (ClosureParserGate Nonterminal N rounds) ≤
      1 + 2 * N +
        rounds * Fintype.card Nonterminal ^ 3 * (N + 1) ^ 3 +
        (rounds + 1) * Fintype.card Nonterminal * (N + 1) ^ 2 := by
  have hgate := Fintype.card_le_of_injective closureParserGateCode
    (closureParserGateCode_injective
      (Nonterminal := Nonterminal) (N := N) (rounds := rounds))
  have hcombine := closureCombine_card_le Nonterminal N rounds
  have hspan := wordSpan_card_le N
  simp only [ClosureParserGateCode, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hgate
  calc
    Fintype.card (ClosureParserGate Nonterminal N rounds)
        ≤ 1 + 2 * N +
            Fintype.card (ClosureCombineIndex Nonterminal N rounds) +
            (rounds + 1) * Fintype.card Nonterminal *
              Fintype.card (WordSpan N) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.add_assoc] using hgate
    _ ≤ 1 + 2 * N +
          rounds * Fintype.card Nonterminal ^ 3 * (N + 1) ^ 3 +
          (rounds + 1) * Fintype.card Nonterminal * (N + 1) ^ 2 := by
        gcongr

private def previousRound {rounds : ℕ} (round : Fin (rounds + 1))
    (hround : round.val ≠ 0) : Fin rounds :=
  ⟨round.val - 1, by omega⟩

@[simp] private theorem previousRound_succ {rounds : ℕ}
    (round : Fin rounds) :
    previousRound round.succ (by simp) = round := by
  apply Fin.ext
  simp [previousRound]

private noncomputable def epsilonChildren {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N) :
    List (ClosureParserGate Nonterminal N rounds) :=
  if s.length = 0 ∧ A ∈ G.epsilonRules then [.truth] else []

private noncomputable def terminalChildren {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N) :
    List (ClosureParserGate Nonterminal N rounds) :=
  ((Finset.univ : Finset (Fin N × Bool)).filter fun x ↦
      s.start = x.1.val ∧ s.stop = x.1.val + 1 ∧
        (A, x.2) ∈ G.terminalRules).toList.map fun x ↦
    .literal x.1 x.2

private noncomputable def unitChildren {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N)
    (round : Fin rounds) : List (ClosureParserGate Nonterminal N rounds) :=
  ((Finset.univ : Finset Nonterminal).filter fun B ↦
      (A, B) ∈ G.unitRules).toList.map fun B ↦
    .parse round.castSucc B s

private noncomputable def combineChildren {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N)
    (round : Fin rounds) : List (ClosureParserGate Nonterminal N rounds) :=
  ((Finset.univ : Finset (Nonterminal × Nonterminal × s.Split)).filter
      fun x ↦ (A, x.1, x.2.1) ∈ G.binaryRules).toList.map fun x ↦
    .combine {
      round := round
      lhs := A
      left := x.1
      right := x.2.1
      span := s
      split := x.2.2
    }

private noncomputable def parseChildren {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N)
    (round : Fin rounds) : List (ClosureParserGate Nonterminal N rounds) :=
  .parse round.castSucc A s ::
    epsilonChildren G A s ++ terminalChildren G A s ++
      unitChildren G A s round ++ combineChildren G A s round

private noncomputable def closureParserNode {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) :
    ClosureParserGate Nonterminal N rounds →
      NNFNode (Fin N) (ClosureParserGate Nonterminal N rounds)
  | .truth => .top
  | .literal i true => .pos i
  | .literal i false => .neg i
  | .combine c =>
      if (c.lhs, c.left, c.right) ∈ G.binaryRules then
        .conj (.parse c.round.castSucc c.left (c.span.left c.split))
          (.parse c.round.castSucc c.right (c.span.right c.split))
      else
        .bot
  | .parse round A s =>
      if hround : round.val = 0 then .bot
      else .disj (parseChildren G A s (previousRound round hround))

private def closureParserRank {N rounds : ℕ} :
    ClosureParserGate Nonterminal N rounds → ℕ
  | .truth => 0
  | .literal _ _ => 0
  | .combine c => 2 * c.round.val + 2
  | .parse round _ _ => 2 * round.val + 1

private def spanPositions {N : ℕ} (s : WordSpan N) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ s.start ≤ i.val ∧ i.val < s.stop

@[simp] private theorem mem_spanPositions {N : ℕ} (s : WordSpan N)
    (i : Fin N) :
    i ∈ spanPositions s ↔ s.start ≤ i.val ∧ i.val < s.stop := by
  simp [spanPositions]

private def closureParserScope {N rounds : ℕ} :
    ClosureParserGate Nonterminal N rounds → Finset (Fin N)
  | .truth => ∅
  | .literal i _ => {i}
  | .combine c => spanPositions c.span
  | .parse _ _ s => spanPositions s

private theorem left_positions_subset {N : ℕ} (s : WordSpan N)
    (k : s.Split) : spanPositions (s.left k) ⊆ spanPositions s := by
  intro i hi
  rw [mem_spanPositions] at hi ⊢
  change s.1.1.val ≤ i.val ∧ i.val < k.1.val at hi
  change s.1.1.val ≤ i.val ∧ i.val < s.1.2.val
  exact ⟨hi.1, hi.2.trans_le k.2.2⟩

private theorem right_positions_subset {N : ℕ} (s : WordSpan N)
    (k : s.Split) : spanPositions (s.right k) ⊆ spanPositions s := by
  intro i hi
  rw [mem_spanPositions] at hi ⊢
  change k.1.val ≤ i.val ∧ i.val < s.1.2.val at hi
  change s.1.1.val ≤ i.val ∧ i.val < s.1.2.val
  constructor
  · have hk : s.1.1.val ≤ k.1.val := k.2.1
    omega
  · exact hi.2

private theorem left_right_positions_disjoint {N : ℕ} (s : WordSpan N)
    (k : s.Split) :
    Disjoint (spanPositions (s.left k)) (spanPositions (s.right k)) := by
  rw [Finset.disjoint_left]
  intro i hleft hright
  rw [mem_spanPositions] at hleft hright
  change s.1.1.val ≤ i.val ∧ i.val < k.1.val at hleft
  change k.1.val ≤ i.val ∧ i.val < s.1.2.val at hright
  exact (Nat.not_lt_of_ge hright.1) hleft.2

private theorem rank_lt_parse_of_mem {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N)
    (round : Fin rounds) (child : ClosureParserGate Nonterminal N rounds)
    (hchild : child ∈ parseChildren G A s round) :
    closureParserRank child <
      closureParserRank (.parse round.succ A s) := by
  simp only [parseChildren, List.mem_cons, List.mem_append] at hchild
  rcases hchild with (((rfl | hepsilon) | hterminal) | hunit) | hcombine
  · simp [closureParserRank]
  · simp only [epsilonChildren] at hepsilon
    split at hepsilon <;> simp_all [closureParserRank]
  · obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hterminal
    simp [closureParserRank]
  · obtain ⟨B, _hB, rfl⟩ := List.mem_map.mp hunit
    simp [closureParserRank]
  · obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hcombine
    change 2 * round.val + 2 < 2 * (round.val + 1) + 1
    omega

private theorem parseChild_scope_subset {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (A : Nonterminal) (s : WordSpan N)
    (round : Fin rounds) (child : ClosureParserGate Nonterminal N rounds)
    (hchild : child ∈ parseChildren G A s round) :
    closureParserScope child ⊆ spanPositions s := by
  simp only [parseChildren, List.mem_cons, List.mem_append] at hchild
  rcases hchild with (((hcarry | hepsilon) | hterminal) | hunit) | hcombine
  · subst child
    rfl
  · by_cases hsource : s.length = 0 ∧ A ∈ G.epsilonRules
    · simp [epsilonChildren, hsource] at hepsilon
      subst child
      simp [closureParserScope]
    · simp [epsilonChildren, hsource] at hepsilon
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hterminal
    have hx' :
        s.start = x.1.val ∧ s.stop = x.1.val + 1 ∧
          (A, x.2) ∈ G.terminalRules := by
      simpa [terminalChildren] using hx
    intro i hi
    simp only [closureParserScope, Finset.mem_singleton] at hi
    subst i
    rw [mem_spanPositions]
    omega
  · obtain ⟨B, _hB, rfl⟩ := List.mem_map.mp hunit
    rfl
  · obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hcombine
    rfl

private theorem closureParser_child_rank {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate child : ClosureParserGate Nonterminal N rounds)
    (hchild : (closureParserNode G gate).IsChild child) :
    closureParserRank child < closureParserRank gate := by
  cases gate with
  | truth => simp [closureParserNode, NNFNode.IsChild] at hchild
  | literal i b => cases b <;> simp [closureParserNode, NNFNode.IsChild] at hchild
  | combine c =>
      by_cases hrule : (c.lhs, c.left, c.right) ∈ G.binaryRules
      · simp only [closureParserNode, hrule, if_pos, NNFNode.IsChild] at hchild
        rcases hchild with rfl | rfl <;> simp [closureParserRank]
      · simp [closureParserNode, hrule, NNFNode.IsChild] at hchild
  | parse round A s =>
      by_cases hround : round.val = 0
      · simp [closureParserNode, hround, NNFNode.IsChild] at hchild
      · simp only [closureParserNode, hround, dite_false,
          NNFNode.IsChild] at hchild
        have hsucc : (previousRound round hround).succ = round := by
          apply Fin.ext
          simp [previousRound]
          omega
        rw [← hsucc]
        exact rank_lt_parse_of_mem G A s (previousRound round hround) child hchild

private theorem closureParser_child_scope_subset {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate child : ClosureParserGate Nonterminal N rounds)
    (hchild : (closureParserNode G gate).IsChild child) :
    closureParserScope child ⊆ closureParserScope gate := by
  cases gate with
  | truth => simp [closureParserNode, NNFNode.IsChild] at hchild
  | literal i b => cases b <;> simp [closureParserNode, NNFNode.IsChild] at hchild
  | combine c =>
      by_cases hrule : (c.lhs, c.left, c.right) ∈ G.binaryRules
      · simp only [closureParserNode, hrule, if_pos, NNFNode.IsChild] at hchild
        rcases hchild with rfl | rfl
        · exact left_positions_subset c.span c.split
        · exact right_positions_subset c.span c.split
      · simp [closureParserNode, hrule, NNFNode.IsChild] at hchild
  | parse round A s =>
      by_cases hround : round.val = 0
      · simp [closureParserNode, hround, NNFNode.IsChild] at hchild
      · simp only [closureParserNode, hround, dite_false,
          NNFNode.IsChild] at hchild
        exact parseChild_scope_subset G A s (previousRound round hround)
          child hchild

private theorem mem_foldl_union {Alpha Beta : Type*} [DecidableEq Beta]
    (x : Beta) (children : List Alpha) (child : Alpha → Finset Beta)
    (acc : Finset Beta) :
    x ∈ children.foldl (fun result gate ↦ result ∪ child gate) acc ↔
      x ∈ acc ∨ ∃ gate ∈ children, x ∈ child gate := by
  induction children generalizing acc with
  | nil => simp
  | cons gate children ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

omit [Fintype Nonterminal] [DecidableEq Nonterminal] in
private theorem nodeSupport_mono {N rounds : ℕ}
    (node : NNFNode (Fin N) (ClosureParserGate Nonterminal N rounds))
    (f g : ClosureParserGate Nonterminal N rounds → Finset (Fin N))
    (hfg : ∀ child, node.IsChild child → f child ⊆ g child) :
    node.Support f ⊆ node.Support g := by
  cases node with
  | top => simp [NNFNode.Support]
  | bot => simp [NNFNode.Support]
  | pos i => simp [NNFNode.Support]
  | neg i => simp [NNFNode.Support]
  | conj left right =>
      intro i hi
      simp only [NNFNode.Support, Finset.mem_union] at hi ⊢
      rcases hi with hleft | hright
      · exact Or.inl (hfg left (Or.inl rfl) hleft)
      · exact Or.inr (hfg right (Or.inr rfl) hright)
  | disj children =>
      intro i hi
      simp only [NNFNode.Support] at hi ⊢
      rw [mem_foldl_union] at hi ⊢
      rcases hi with hi | ⟨child, hchild, hi⟩
      · exact Or.inl hi
      · exact Or.inr ⟨child, hchild, hfg child hchild hi⟩

private theorem closureParserNode_scope_closed {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate : ClosureParserGate Nonterminal N rounds) :
    (closureParserNode G gate).Support closureParserScope ⊆
      closureParserScope gate := by
  cases gate with
  | truth => simp [closureParserNode, closureParserScope, NNFNode.Support]
  | literal i b =>
      cases b <;> simp [closureParserNode, closureParserScope, NNFNode.Support]
  | combine c =>
      by_cases hrule : (c.lhs, c.left, c.right) ∈ G.binaryRules
      · simp only [closureParserNode, hrule, if_pos, NNFNode.Support,
          closureParserScope]
        exact Finset.union_subset (left_positions_subset c.span c.split)
          (right_positions_subset c.span c.split)
      · simp [closureParserNode, hrule, closureParserScope, NNFNode.Support]
  | parse round A s =>
      by_cases hround : round.val = 0
      · simp [closureParserNode, hround, closureParserScope, NNFNode.Support]
      · intro i hi
        simp only [closureParserNode, hround, dite_false,
          NNFNode.Support] at hi
        rw [mem_foldl_union] at hi
        rcases hi with hi | ⟨child, hchild, hi⟩
        · simp at hi
        · exact parseChild_scope_subset G A s (previousRound round hround)
            child hchild hi

private noncomputable def closureParserDescription {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) :
    AcyclicNNFDescription (Fin N) (ClosureParserGate Nonterminal N rounds) where
  output := .parse (Fin.last rounds) G.start (WordSpan.full N)
  node := closureParserNode G
  rank := closureParserRank
  child_rank := closureParser_child_rank G

private def closureParserMeaning {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate : ClosureParserGate Nonterminal N rounds) (v : Fin N → Bool) : Prop :=
  match gate with
  | .truth => True
  | .literal i b => v i = b
  | .combine c =>
      (c.lhs, c.left, c.right) ∈ G.binaryRules ∧
        (c.left, c.span.left c.split) ∈ G.parseFactsAt v c.round.val ∧
        (c.right, c.span.right c.split) ∈ G.parseFactsAt v c.round.val
  | .parse round A s => (A, s) ∈ G.parseFactsAt v round.val

private theorem parseChildren_meaning_iff {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    (A : Nonterminal) (s : WordSpan N) (round : Fin rounds) :
    (∃ child ∈ parseChildren G A s round,
      closureParserMeaning G child v) ↔
      CanDeriveFrom G v (G.parseFactsAt v round.val) (A, s) := by
  constructor
  · rintro ⟨child, hchild, hmeaning⟩
    simp only [parseChildren, List.mem_cons, List.mem_append] at hchild
    rcases hchild with (((hcarry | hepsilon) | hterminal) | hunit) | hcombine
    · subst child
      exact Or.inl hmeaning
    · by_cases hsource : s.length = 0 ∧ A ∈ G.epsilonRules
      · simp [epsilonChildren, hsource] at hepsilon
        subst child
        exact Or.inr (Or.inl hsource)
      · simp [epsilonChildren, hsource] at hepsilon
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hterminal
      have hx' :
          s.start = x.1.val ∧ s.stop = x.1.val + 1 ∧
            (A, x.2) ∈ G.terminalRules := by
        simpa [terminalChildren] using hx
      change v x.1 = x.2 at hmeaning
      exact Or.inr (Or.inr (Or.inl
        ⟨x.1, hx'.1, hx'.2.1, by simpa [hmeaning] using hx'.2.2⟩))
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hunit
      have hrule : (A, B) ∈ G.unitRules := by
        simpa [unitChildren] using hB
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨B, hrule, hmeaning⟩)))
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcombine
      rcases x with ⟨B, C, k⟩
      change
        (A, B, C) ∈ G.binaryRules ∧
          (B, s.left k) ∈ G.parseFactsAt v round.val ∧
          (C, s.right k) ∈ G.parseFactsAt v round.val at hmeaning
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨B, C, hmeaning.1, k, hmeaning.2.1, hmeaning.2.2⟩)))
  · intro hcan
    rcases hcan with hknown | hepsilon | hterminal | hunit | hbinary
    · exact ⟨.parse round.castSucc A s, by simp [parseChildren], hknown⟩
    · refine ⟨.truth, ?_, trivial⟩
      simp [parseChildren, epsilonChildren, hepsilon]
    · rcases hterminal with ⟨i, hstart, hstop, hrule⟩
      refine ⟨.literal i (v i), ?_, rfl⟩
      simp [parseChildren, terminalChildren, hstart, hstop, hrule]
    · rcases hunit with ⟨B, hrule, hchild⟩
      refine ⟨.parse round.castSucc B s, ?_, hchild⟩
      simp [parseChildren, unitChildren, hrule]
    · rcases hbinary with ⟨B, C, hrule, k, hleft, hright⟩
      let c : ClosureCombineIndex Nonterminal N rounds := {
        round := round
        lhs := A
        left := B
        right := C
        span := s
        split := k
      }
      refine ⟨.combine c, ?_, ?_⟩
      · simp [parseChildren, combineChildren, c, hrule]
      · exact ⟨hrule, hleft, hright⟩

private theorem closureParserMeaning_eq {N rounds : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate : ClosureParserGate Nonterminal N rounds) (v : Fin N → Bool) :
    closureParserMeaning G gate v ↔
      (closureParserNode G gate).Holds v
        (fun child ↦ closureParserMeaning G child v) := by
  cases gate with
  | truth => simp [closureParserMeaning, closureParserNode, NNFNode.Holds]
  | literal i b =>
      cases b <;> simp [closureParserMeaning, closureParserNode, NNFNode.Holds]
  | combine c =>
      by_cases hrule : (c.lhs, c.left, c.right) ∈ G.binaryRules <;>
        simp [closureParserMeaning, closureParserNode, NNFNode.Holds, hrule]
  | parse round A s =>
      by_cases hround : round.val = 0
      · have hr : round = 0 := Fin.ext hround
        subst round
        change (A, s) ∈ G.parseFactsAt v 0 ↔ False
        simp [parseFactsAt, FiniteClosure.iterate]
      · let previous := previousRound round hround
        have hsucc : previous.succ = round := by
          apply Fin.ext
          simp [previous, previousRound]
          omega
        rw [← hsucc]
        change
          (A, s) ∈ G.parseFactsAt v (previous.val + 1) ↔
            (closureParserNode G (.parse previous.succ A s)).Holds v
              (fun child ↦ closureParserMeaning G child v)
        rw [parseFactsAt, FiniteClosure.iterate_succ, mem_closureStep_iff]
        have hprevious : previous.succ.val ≠ 0 := by simp
        simp only [closureParserNode, hprevious, dite_false, NNFNode.Holds]
        rw [previousRound_succ, parseChildren_meaning_iff]
        rfl

/-- The round-indexed shared parser circuit. -/
noncomputable def closureIntervalCircuit {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) : NNFCircuit (Fin N) :=
  (closureParserDescription
    (rounds := closureRounds Nonterminal N) G).toCircuit

private theorem closureRounds_le (Nonterminal : Type*) [Fintype Nonterminal]
    (N : ℕ) :
    closureRounds Nonterminal N ≤
      Fintype.card Nonterminal * (N + 1) ^ 2 := by
  unfold closureRounds
  rw [Fintype.card_prod]
  gcongr
  exact wordSpan_card_le N

theorem closureIntervalCircuit_size_le {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) :
    (closureIntervalCircuit (N := N) G).nodeCount ≤
      1 + 2 * N +
        (Fintype.card Nonterminal * (N + 1) ^ 2) *
          Fintype.card Nonterminal ^ 3 * (N + 1) ^ 3 +
        (Fintype.card Nonterminal * (N + 1) ^ 2 + 1) *
          Fintype.card Nonterminal * (N + 1) ^ 2 := by
  rw [closureIntervalCircuit, AcyclicNNFDescription.toCircuit_nodeCount]
  apply (closureParserGate_card_le Nonterminal N
    (closureRounds Nonterminal N)).trans
  have hrounds := closureRounds_le Nonterminal N
  gcongr

theorem closureIntervalCircuit_semantics_iff {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate : ClosureParserGate Nonterminal N (closureRounds Nonterminal N))
    (v : Fin N → Bool) :
    G.closureIntervalCircuit.semantics gate v ↔
      closureParserMeaning G gate v := by
  symm
  exact G.closureIntervalCircuit.semantics_unique (closureParserMeaning G)
    (closureParserMeaning_eq G) gate v

theorem closureIntervalCircuit_computes_derivations {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) :
    G.closureIntervalCircuit.Computes
      (fun v ↦ G.DerivesSpan v G.start (WordSpan.full N)) := by
  intro v
  change
    G.closureIntervalCircuit.semantics
        (.parse (Fin.last (closureRounds Nonterminal N)) G.start
          (WordSpan.full N)) v ↔
      G.DerivesSpan v G.start (WordSpan.full N)
  rw [G.closureIntervalCircuit_semantics_iff]
  change
    (G.start, WordSpan.full N) ∈
        G.parseFactsAt v (closureRounds Nonterminal N) ↔ _
  exact G.mem_final_iff_derivesSpan v G.start (WordSpan.full N)

/-- The generated DNNF recognizes the fixed-length slice of the standard
Mathlib context-free language. -/
theorem closureIntervalCircuit_computes_standard_language {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) :
    (G.closureIntervalCircuit (N := N)).Computes
      (fun v : Fin N → Bool ↦
        List.ofFn v ∈ G.toContextFreeGrammar.language) := by
  intro v
  exact (G.closureIntervalCircuit_computes_derivations v).trans
    (G.derivesSpan_full_iff_mem_standard_language v)

private theorem closureIntervalCircuit_support_subset_scope {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal)
    (gate : ClosureParserGate Nonterminal N (closureRounds Nonterminal N)) :
    G.closureIntervalCircuit.support gate ⊆ closureParserScope gate := by
  have key : ∀ r : ℕ,
      ∀ gate : ClosureParserGate Nonterminal N (closureRounds Nonterminal N),
      closureParserRank gate < r →
        G.closureIntervalCircuit.support gate ⊆ closureParserScope gate := by
    intro r
    induction r with
    | zero => intro gate hgate; omega
    | succ r ih =>
        intro gate hgate
        rw [G.closureIntervalCircuit.support_eq gate]
        change
          (closureParserNode G gate).Support G.closureIntervalCircuit.support ⊆
            closureParserScope gate
        apply (nodeSupport_mono (closureParserNode G gate)
          G.closureIntervalCircuit.support closureParserScope ?_).trans
          (closureParserNode_scope_closed G gate)
        intro child hchild
        apply ih child
        have := closureParser_child_rank G gate child hchild
        omega
  exact key (closureParserRank gate + 1) gate (by omega)

theorem closureIntervalCircuit_isDNNF {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) :
    (closureIntervalCircuit (N := N) G).IsDNNF := by
  intro gate left right hnode
  cases gate with
  | truth =>
      change closureParserNode G .truth = .conj left right at hnode
      simp [closureParserNode] at hnode
  | literal i b =>
      change closureParserNode G (.literal i b) = .conj left right at hnode
      cases b <;> simp [closureParserNode] at hnode
  | parse round A s =>
      change closureParserNode G (.parse round A s) = .conj left right at hnode
      by_cases hround : round.val = 0 <;>
        simp [closureParserNode, hround] at hnode
  | combine c =>
      change closureParserNode G (.combine c) = .conj left right at hnode
      by_cases hrule : (c.lhs, c.left, c.right) ∈ G.binaryRules
      · simp only [closureParserNode, hrule, if_pos] at hnode
        injection hnode with hleft hright
        subst left
        subst right
        rw [Finset.disjoint_left]
        intro i hiLeft hiRight
        have hiLeft' :=
          closureIntervalCircuit_support_subset_scope G
            (.parse c.round.castSucc c.left (c.span.left c.split)) hiLeft
        have hiRight' :=
          closureIntervalCircuit_support_subset_scope G
            (.parse c.round.castSucc c.right (c.span.right c.split)) hiRight
        exact (Finset.disjoint_left.mp
          (left_right_positions_disjoint c.span c.split)) hiLeft' hiRight'
      · simp [closureParserNode, hrule] at hnode

end ExtendedBinaryCFG

end DDNNFNegation
