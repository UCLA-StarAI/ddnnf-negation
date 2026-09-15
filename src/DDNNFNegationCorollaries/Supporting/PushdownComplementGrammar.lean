import DDNNFNegationCorollaries.Supporting.PushdownRuns
import DDNNFNegationCorollaries.Supporting.CFGForest
import DDNNFNegationCorollaries.Supporting.CFGBinarization

/-!
# A grammar for the complement of a DPDA

Nonterminals summarize stack runs and rejection conditions. The nullable
summaries are handled separately, so the run-summary nonterminals generate
only nonempty words; the start and unrestricted-word nonterminals may
also generate the empty word. Soundness and completeness identify the
language with the DPDA's complement. The final counting bound is polynomial
in the DPDA's description size.
-/

namespace DDNNFNegation.Pushdown.DPDA

open Classical ContextFreeGrammar CFGBinarization

variable (M : DPDA)

/-! ## Segments -/

/-- The string a transition pushes, if the transition exists. -/
def pushed (t : Fin M.states × Option Bool × Fin M.stack) : Option (List (Fin M.stack)) :=
  (M.step t.1 t.2.1 t.2.2).map Prod.snd

/-- The stack segments: the empty stack, the single symbols, and every suffix
of a pushed string. -/
def segments : Finset (List (Fin M.stack)) :=
  ({[]} ∪ Finset.univ.image fun Z : Fin M.stack => [Z]) ∪
    Finset.univ.biUnion fun t => (M.pushed t).elim ∅ fun δ => δ.tails.toFinset

/-- A segment, as a subtype of the finite set `segments`. -/
abbrev Seg := {γ : List (Fin M.stack) // γ ∈ M.segments}

theorem nil_mem_segments : [] ∈ M.segments := by
  simp [segments]

theorem single_mem_segments (Z : Fin M.stack) : [Z] ∈ M.segments := by
  simp [segments]

theorem pushed_mem_segments {q : Fin M.states} {a : Option Bool} {Z : Fin M.stack}
    {r : Fin M.states} {δ : List (Fin M.stack)} (h : M.step q a Z = some (r, δ)) :
    δ ∈ M.segments := by
  simp only [segments, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  right
  refine ⟨(q, a, Z), ?_⟩
  simp [pushed, h, List.mem_tails]

theorem tail_mem_segments {Z : Fin M.stack} {δ : List (Fin M.stack)}
    (h : Z :: δ ∈ M.segments) : δ ∈ M.segments := by
  simp only [segments, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_image] at h ⊢
  rcases h with (h | ⟨Y, hY⟩) | ⟨t, ht⟩
  · cases h
  · cases hY
    exact Or.inl (Or.inl rfl)
  · right
    refine ⟨t, ?_⟩
    cases hp : M.pushed t with
    | none => rw [hp] at ht; simp at ht
    | some δ₀ =>
      rw [hp] at ht
      simp only [Option.elim, List.mem_toFinset, List.mem_tails] at ht ⊢
      exact (List.suffix_cons Z δ).trans ht

/-- The segment with a given underlying list, defaulting to the empty stack
when the list is not a segment. -/
noncomputable def toSeg (γ : List (Fin M.stack)) : M.Seg :=
  if h : γ ∈ M.segments then ⟨γ, h⟩ else ⟨[], M.nil_mem_segments⟩

theorem toSeg_val {γ : List (Fin M.stack)} (h : γ ∈ M.segments) : (M.toSeg γ).1 = γ := by
  simp [toSeg, h]

/-! ## Nonterminals and their semantics -/

/-- The kind of a nonterminal: pop into a state (and reject on the way if the
flag is set), or reject (and never empty the stack if the flag is set). -/
inductive Kind (M : DPDA)
  | pop (q : Fin M.states) (e : Bool)
  | rej (s : Bool)
  deriving DecidableEq, Fintype

/-- The nonterminals of the complement grammar. -/
inductive NT (M : DPDA)
  | node (p : Fin M.states) (γ : M.Seg) (k : M.Kind)
  | all
  | start
  deriving DecidableEq, Fintype

/-- No prefix of `w` empties the stack from `c`. -/
def NoPop (c : M.Config) (w : List Bool) : Prop := ∀ u q, u <+: w → ¬ M.Pops c u q

/-- The property a kind stands for at configuration `c`, for any word. -/
def KindSem : M.Kind → M.Config → List Bool → Prop
  | .pop q e, c, w => M.Pops c w q ∧ (e = true → ¬ M.Acc c w)
  | .rej s, c, w => ¬ M.Acc c w ∧ (s = true → M.NoPop c w)

/-- The property a nonterminal stands for, before the requirement that the
word be nonempty. -/
def Sem₀ : M.NT → List Bool → Prop
  | .node p γ k, w => M.KindSem k (p, γ.1) w
  | .all, _ => True
  | .start, w => ¬ M.Acc (M.start, [M.bottom]) w

/-- The words a nonterminal stands for. -/
def Sem : M.NT → List Bool → Prop
  | .node p γ k, w => w ≠ [] ∧ M.KindSem k (p, γ.1) w
  | .all, _ => True
  | .start, w => ¬ M.Acc (M.start, [M.bottom]) w

/-- The flag of the popping nonterminal that stands for the part of a run
above the tail of a segment: rejection must be tracked unless the kind is the
plain pop. -/
def Kind.first : M.Kind → Bool
  | .pop _ e => e
  | .rej _ => true

/-- A letter the machine cannot read from `c`. -/
def Dead (c : M.Config) (b : Bool) : Prop := ∀ w c', ¬ Reach M c (b :: w) c'

/-! ## Productions -/

local notation "𝓝" X => Symbol.nonterminal X
local notation "𝓣" b => Symbol.terminal b

/-- A letter the machine cannot read is followed by anything. -/
noncomputable def deadProds (p : Fin M.states) (γ : M.Seg) :
    M.Kind → Finset (List (Symbol Bool M.NT))
  | .pop _ _ => ∅
  | .rej s =>
    (Finset.univ.filter fun b : Bool =>
      M.Dead (p, γ.1) b ∧ (s = true → ∀ q, ¬ M.Pops (p, γ.1) [] q)).image
      fun b => [𝓣 b, 𝓝 (NT.all)]

/-- The moves from a single stack symbol. -/
noncomputable def stepProds (p : Fin M.states) (γ : M.Seg) (k : M.Kind) :
    Finset (List (Symbol Bool M.NT)) :=
  match γ.1 with
  | [Y] =>
    match M.step p none Y with
    | some (r, δ) => {[𝓝 (NT.node r (M.toSeg δ) k)]}
    | none =>
      Finset.univ.biUnion fun b : Bool =>
        match M.step p (some b) Y with
        | some (r, δ) =>
          {[𝓣 b, 𝓝 (NT.node r (M.toSeg δ) k)]} ∪
            (if M.Sem₀ (.node r (M.toSeg δ) k) [] then {[𝓣 b]} else ∅)
        | none => ∅
  | _ => ∅

/-- Splitting a run at the pop of the top symbol of a long segment. -/
noncomputable def splitProds (p : Fin M.states) (γ : M.Seg) (k : M.Kind) :
    Finset (List (Symbol Bool M.NT)) :=
  match γ.1 with
  | Z :: Y :: δ'' =>
    (match k with
      | .rej _ => {[𝓝 (NT.node p (M.toSeg [Z]) (.rej true))]}
      | .pop _ _ => ∅) ∪
    Finset.univ.biUnion fun q' : Fin M.states =>
      (if M.Sem₀ (.node q' (M.toSeg (Y :: δ'')) k) [] then
        {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' k.first))]} else ∅) ∪
      {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' false)), 𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} ∪
      (if M.Pops (p, [Z]) [] q' then {[𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} else ∅)
  | _ => ∅

/-- The right-hand sides of the productions of a nonterminal. -/
noncomputable def prods : M.NT → Finset (List (Symbol Bool M.NT))
  | .node p γ k => M.deadProds p γ k ∪ M.stepProds p γ k ∪ M.splitProds p γ k
  | .all => {[]} ∪ Finset.univ.image fun b : Bool => [𝓣 b, 𝓝 (NT.all)]
  | .start =>
    {[𝓝 (NT.node M.start (M.toSeg [M.bottom]) (.rej false))]} ∪
      (if ¬ M.Acc (M.start, [M.bottom]) [] then {[]} else ∅)

/-- The rules of the complement grammar. -/
noncomputable def rules : Finset (ContextFreeRule Bool M.NT) :=
  Finset.univ.biUnion fun X => (M.prods X).image fun o => ⟨X, o⟩

theorem mem_rules_iff (r : ContextFreeRule Bool M.NT) :
    r ∈ M.rules ↔ r.output ∈ M.prods r.input := by
  simp only [rules, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨X, o, ho, rfl⟩
    exact ho
  · intro h
    exact ⟨r.input, r.output, h, rfl⟩

/-- The complement grammar. -/
noncomputable def complementCFG : ContextFreeGrammar Bool where
  NT := M.NT
  initial := .start
  rules := M.rules

/-! ## Semantic facts about runs -/

section Semantics

variable {M}

theorem acc_def (c : M.Config) (w : List Bool) :
    M.Acc c w ↔ ∃ c', Reach M c w c' ∧ M.accept c'.1 = true := Iff.rfl

/-- After a pop, nothing more is read. -/
theorem eq_nil_of_reach_of_pops {c c' : M.Config} {w1 w2 : List Bool} {q : Fin M.states}
    (h : Reach M c (w1 ++ w2) c') (hp : M.Pops c w1 q) : w2 = [] := by
  rcases reach_linear hp h with h' | ⟨hv, _⟩
  · exact (reach_nil_stack h').1
  · exact hv

theorem pops_unique' {c : M.Config} {w1 w2 : List Bool} {q1 q2 : Fin M.states}
    (h1 : M.Pops c w1 q1) (h2 : M.Pops c w2 q2) (h : w1 <+: w2 ∨ w2 <+: w1) :
    w1 = w2 ∧ q1 = q2 := by
  rcases h with h | h
  · exact pops_unique h1 h2 h
  · obtain ⟨h1', h2'⟩ := pops_unique h2 h1 h
    exact ⟨h1'.symm, h2'.symm⟩

theorem acc_cons_iff (p : Fin M.states) (Z : Fin M.stack) (δ' : List (Fin M.stack))
    (w : List Bool) :
    M.Acc (p, Z :: δ') w ↔
      M.Acc (p, [Z]) w ∨
        ∃ q' w1 w2, w = w1 ++ w2 ∧ M.Pops (p, [Z]) w1 q' ∧ M.Acc (q', δ') w2 := by
  constructor
  · rintro ⟨c', hr, hacc⟩
    rcases reach_append_cases (γ := [Z]) hr with ⟨st', _, h⟩ | ⟨q', w1, w2, rfl, h1, h2⟩
    · exact Or.inl ⟨_, h, hacc⟩
    · exact Or.inr ⟨q', w1, w2, rfl, h1, ⟨c', h2, hacc⟩⟩
  · rintro (⟨c', hr, hacc⟩ | ⟨q', w1, w2, rfl, h1, ⟨c', h2, hacc⟩⟩)
    · exact ⟨(c'.1, c'.2 ++ δ'), hr.lift' δ', hacc⟩
    · exact ⟨c', (reach_append_iff (γ := [Z])).2 (Or.inr ⟨q', w1, w2, rfl, h1, h2⟩), hacc⟩

theorem pops_cons_iff (p : Fin M.states) (Z : Fin M.stack) {δ' : List (Fin M.stack)}
    (hδ : δ' ≠ []) (w : List Bool) (q : Fin M.states) :
    M.Pops (p, Z :: δ') w q ↔
      ∃ q' w1 w2, w = w1 ++ w2 ∧ M.Pops (p, [Z]) w1 q' ∧ M.Pops (q', δ') w2 q := by
  constructor
  · intro h
    rcases reach_append_cases (γ := [Z]) h with ⟨st', hst, _⟩ | ⟨q', w1, w2, rfl, h1, h2⟩
    · exact absurd (List.append_eq_nil_iff.1 hst.symm).2 hδ
    · exact ⟨q', w1, w2, rfl, h1, h2⟩
  · rintro ⟨q', w1, w2, rfl, h1, h2⟩
    exact (reach_append_iff (γ := [Z])).2 (Or.inr ⟨q', w1, w2, rfl, h1, h2⟩)

/-- Splitting a long segment: the part above the tail never empties. -/
theorem kindSem_of_noPop {p : Fin M.states} {Z : Fin M.stack} {δ' : List (Fin M.stack)}
    (hδ : δ' ≠ []) {w : List Bool} (h : M.KindSem (.rej true) (p, [Z]) w) (s : Bool) :
    M.KindSem (.rej s) (p, Z :: δ') w := by
  obtain ⟨hacc, hnp⟩ := h
  have hnp := hnp rfl
  refine ⟨?_, fun _ => ?_⟩
  · rw [acc_cons_iff]
    rintro (h | ⟨q', w1, w2, rfl, h1, _⟩)
    · exact hacc h
    · exact hnp w1 q' (List.prefix_append w1 w2) h1
  · intro u q hu hp
    rw [pops_cons_iff p Z hδ] at hp
    obtain ⟨q', u1, u2, rfl, h1, _⟩ := hp
    exact hnp u1 q' ((List.prefix_append u1 u2).trans hu) h1

/-- Splitting a long segment: the pop of the top symbol ends the word. -/
theorem kindSem_of_pop_of_nil {p q' : Fin M.states} {Z : Fin M.stack} {δ' : List (Fin M.stack)}
    (hδ : δ' ≠ []) {k : M.Kind} {w : List Bool}
    (h1 : M.KindSem (.pop q' k.first) (p, [Z]) w) (h2 : M.KindSem k (q', δ') []) :
    M.KindSem k (p, Z :: δ') w := by
  have key : M.Pops (p, [Z]) w q' → ¬ M.Acc (p, [Z]) w → ¬ M.Acc (q', δ') [] →
      ¬ M.Acc (p, Z :: δ') w := by
    intro hp hacc hacc' h
    rw [acc_cons_iff] at h
    rcases h with h | ⟨q'', w1, w2, hw, h1, h2⟩
    · exact hacc h
    · obtain ⟨rfl, rfl⟩ := pops_unique h1 hp (hw ▸ List.prefix_append w1 w2)
      have : w2 = [] := by
        have := congrArg List.length hw
        simp only [List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact hacc' h2
  cases k with
  | pop q e =>
    obtain ⟨hp, hacc⟩ := h1
    obtain ⟨hp', hacc'⟩ := h2
    refine ⟨?_, fun he => ?_⟩
    · have := (hp.lift δ').trans hp'
      show Reach M _ _ _
      simpa using this
    · subst he
      exact key hp (hacc rfl) (hacc' rfl)
  | rej s =>
    obtain ⟨hp, hacc⟩ := h1
    obtain ⟨hacc', hnp'⟩ := h2
    refine ⟨key hp (hacc rfl) hacc', fun hs => ?_⟩
    intro u q hu hpu
    rw [pops_cons_iff p Z hδ] at hpu
    obtain ⟨q'', u1, u2, rfl, hu1, hu2⟩ := hpu
    obtain ⟨rfl, rfl⟩ := pops_unique hu1 hp ((List.prefix_append u1 u2).trans hu)
    have : u2 = [] := by
      have := hu.length_le
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact hnp' hs [] q (List.nil_prefix) hu2

/-- Splitting a long segment: the run continues below the popped symbol. -/
theorem kindSem_of_pop_append {p q' : Fin M.states} {Z : Fin M.stack} {δ' : List (Fin M.stack)}
    (hδ : δ' ≠ []) {k : M.Kind} {w1 w2 : List Bool}
    (h1 : M.Pops (p, [Z]) w1 q') (h2 : M.KindSem k (q', δ') w2) (hw2 : w2 ≠ []) :
    M.KindSem k (p, Z :: δ') (w1 ++ w2) := by
  have key : ¬ M.Acc (q', δ') w2 → ¬ M.Acc (p, Z :: δ') (w1 ++ w2) := by
    intro hacc h
    rw [acc_cons_iff] at h
    rcases h with ⟨c', hr, _⟩ | ⟨q'', u1, u2, hw, hu1, hu2⟩
    · exact hw2 (eq_nil_of_reach_of_pops hr h1)
    · obtain ⟨rfl, rfl⟩ := pops_unique' hu1 h1
        (List.prefix_or_prefix_of_prefix (hw ▸ List.prefix_append u1 u2)
          (List.prefix_append w1 w2))
      rw [List.append_cancel_left_eq] at hw
      subst hw
      exact hacc hu2
  cases k with
  | pop q e =>
    obtain ⟨hp, hacc⟩ := h2
    exact ⟨(h1.lift δ').trans hp, fun he => key (hacc he)⟩
  | rej s =>
    obtain ⟨hacc, hnp⟩ := h2
    refine ⟨key hacc, fun hs => ?_⟩
    intro u q hu hpu
    rw [pops_cons_iff p Z hδ] at hpu
    obtain ⟨q'', u1, u2, rfl, hu1, hu2⟩ := hpu
    obtain ⟨rfl, rfl⟩ := pops_unique' hu1 h1
      (List.prefix_or_prefix_of_prefix ((List.prefix_append u1 u2).trans hu)
        (List.prefix_append w1 w2))
    rw [List.prefix_append_right_inj] at hu
    exact hnp hs u2 q hu hu2

/-- An epsilon move preserves every kind on nonempty words. -/
theorem kindSem_eps_iff {p r : Fin M.states} {Y : Fin M.stack} {δ : List (Fin M.stack)}
    (hs : M.step p none Y = some (r, δ)) (k : M.Kind) {w : List Bool} (hw : w ≠ []) :
    M.KindSem k (p, [Y]) w ↔ M.KindSem k (r, δ) w := by
  have hreach : ∀ c, Reach M (p, [Y]) w c ↔ Reach M (r, δ) w c := by
    intro c
    rw [reach_single_eps_iff hs]
    exact or_iff_right (fun h => hw h.1)
  have hpops : ∀ u q, M.Pops (p, [Y]) u q ↔ M.Pops (r, δ) u q := by
    intro u q
    show Reach M _ _ _ ↔ Reach M _ _ _
    rw [reach_single_eps_iff hs]
    refine or_iff_right ?_
    rintro ⟨_, h⟩
    cases h
  have hacc : M.Acc (p, [Y]) w ↔ M.Acc (r, δ) w := by
    simp only [acc_def, hreach]
  have hnp : M.NoPop (p, [Y]) w ↔ M.NoPop (r, δ) w := by
    simp only [NoPop, hpops]
  cases k with
  | pop q e => simp only [KindSem, hpops, hacc]
  | rej s => simp only [KindSem, hacc, hnp]

/-- A letter move translates every kind. -/
theorem kindSem_letter_iff {p r : Fin M.states} {Y : Fin M.stack} {b : Bool}
    {δ : List (Fin M.stack)} (hnone : M.step p none Y = none)
    (hs : M.step p (some b) Y = some (r, δ)) (k : M.Kind) (w : List Bool) :
    M.KindSem k (p, [Y]) (b :: w) ↔ M.KindSem k (r, δ) w := by
  have hreach : ∀ c, Reach M (p, [Y]) (b :: w) c ↔ Reach M (r, δ) w c :=
    fun c => reach_single_letter_iff hnone hs
  have hpops : ∀ u q, M.Pops (p, [Y]) (b :: u) q ↔ M.Pops (r, δ) u q :=
    fun u q => reach_single_letter_iff hnone hs
  have hpops0 : ∀ q, ¬ M.Pops (p, [Y]) [] q := by
    intro q h
    have := (reach_single_nil_iff hnone).1 h
    cases this
  have hacc : M.Acc (p, [Y]) (b :: w) ↔ M.Acc (r, δ) w := by
    simp only [acc_def, hreach]
  have hnp : M.NoPop (p, [Y]) (b :: w) ↔ M.NoPop (r, δ) w := by
    constructor
    · intro h u q hu hp
      exact h (b :: u) q (List.cons_prefix_cons.2 ⟨rfl, hu⟩) ((hpops u q).2 hp)
    · intro h u q hu hp
      cases u with
      | nil => exact hpops0 q hp
      | cons b' u =>
        obtain ⟨rfl, hu'⟩ := List.cons_prefix_cons.1 hu
        exact h u q hu' ((hpops u q).1 hp)
  cases k with
  | pop q e => simp only [KindSem, hpops, hacc]
  | rej s => simp only [KindSem, hacc, hnp]

/-- A letter the machine cannot read is rejected together with everything after it. -/
theorem kindSem_rej_of_dead {c : M.Config} {b : Bool} (hd : M.Dead c b) {s : Bool}
    (hs : s = true → ∀ q, ¬ M.Pops c [] q) (w : List Bool) :
    M.KindSem (.rej s) c (b :: w) := by
  refine ⟨?_, fun hs' u q hu hp => ?_⟩
  · rintro ⟨c', hr, _⟩
    exact hd w c' hr
  · cases u with
    | nil => exact hs hs' q hp
    | cons b' u =>
      obtain ⟨rfl, _⟩ := List.cons_prefix_cons.1 hu
      exact hd u (q, []) hp

theorem dead_of_loops {c : M.Config} (hl : M.Loops c) (b : Bool) : M.Dead c b :=
  fun _ _ h => not_reach_cons_of_loops hl h

theorem dead_nil (q : Fin M.states) (b : Bool) : M.Dead (q, []) b := by
  intro w c' h
  exact absurd (reach_nil_stack h).1 (List.cons_ne_nil b w)

theorem dead_of_stuck {p : Fin M.states} {Y : Fin M.stack} {b : Bool}
    (hnone : M.step p none Y = none) (hb : M.step p (some b) Y = none) :
    M.Dead (p, [Y]) b :=
  fun _ _ h => not_reach_single_stuck hnone hb h

end Semantics

/-! ## Soundness: generated words have the property of their nonterminal -/

section Soundness

variable {M}

/-- The property a symbol string stands for: its terminals are read, its
nonterminals stand for words of their kind. -/
def SemList : List (Symbol Bool M.NT) → List Bool → Prop
  | [], w => w = []
  | .terminal b :: o, w => ∃ w', w = b :: w' ∧ SemList o w'
  | .nonterminal X :: o, w => ∃ w1 w2, w = w1 ++ w2 ∧ M.Sem X w1 ∧ SemList o w2

theorem semList_single_nt {X : M.NT} {w : List Bool} (h : SemList [.nonterminal X] w) :
    M.Sem X w := by
  obtain ⟨w1, w2, rfl, h1, h2⟩ := h
  simp only [SemList] at h2
  subst h2
  simpa using h1

theorem semList_letter_nt {b : Bool} {X : M.NT} {w : List Bool}
    (h : SemList [.terminal b, .nonterminal X] w) : ∃ w', w = b :: w' ∧ M.Sem X w' := by
  obtain ⟨w', rfl, h⟩ := h
  exact ⟨w', rfl, semList_single_nt h⟩

theorem semList_letter {b : Bool} {w : List Bool} (h : SemList ([.terminal b] : List (Symbol Bool M.NT)) w) :
    w = [b] := by
  obtain ⟨w', rfl, h⟩ := h
  simp only [SemList] at h
  rw [h]

theorem semList_two_nt {X Y : M.NT} {w : List Bool}
    (h : SemList [.nonterminal X, .nonterminal Y] w) :
    ∃ w1 w2, w = w1 ++ w2 ∧ M.Sem X w1 ∧ M.Sem Y w2 := by
  obtain ⟨w1, w2, rfl, h1, h2⟩ := h
  exact ⟨w1, w2, rfl, h1, semList_single_nt h2⟩

theorem sem_node_iff (p : Fin M.states) (γ : M.Seg) (k : M.Kind) (w : List Bool) :
    M.Sem (.node p γ k) w ↔ w ≠ [] ∧ M.KindSem k (p, γ.1) w := Iff.rfl

theorem sem_of_deadProds (p : Fin M.states) (γ : M.Seg) (k : M.Kind)
    {o : List (Symbol Bool M.NT)} {w : List Bool} (ho : o ∈ M.deadProds p γ k)
    (h : SemList o w) : M.Sem (.node p γ k) w := by
  cases k with
  | pop q e => simp [deadProds] at ho
  | rej s =>
    simp only [deadProds, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    obtain ⟨b, ⟨hd, hnp⟩, rfl⟩ := ho
    obtain ⟨w', rfl, -⟩ := semList_letter_nt h
    exact ⟨List.cons_ne_nil b w', kindSem_rej_of_dead hd hnp w'⟩

theorem sem_of_stepProds (p : Fin M.states) (γ : M.Seg) (k : M.Kind)
    {o : List (Symbol Bool M.NT)} {w : List Bool} (ho : o ∈ M.stepProds p γ k)
    (h : SemList o w) : M.Sem (.node p γ k) w := by
  obtain ⟨γ, hγ⟩ := γ
  rcases γ with _ | ⟨Y, _ | ⟨Y', rest⟩⟩
  · simp [stepProds] at ho
  · simp only [stepProds] at ho
    cases hs : M.step p none Y with
    | some rδ =>
      obtain ⟨r, δ⟩ := rδ
      rw [hs] at ho
      simp only [Finset.mem_singleton] at ho
      subst ho
      obtain ⟨hne, hk⟩ := semList_single_nt h
      rw [M.toSeg_val (M.pushed_mem_segments hs)] at hk
      exact ⟨hne, (kindSem_eps_iff hs k hne).2 hk⟩
    | none =>
      rw [hs] at ho
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ho
      obtain ⟨b, hb⟩ := ho
      cases hsb : M.step p (some b) Y with
      | none => rw [hsb] at hb; simp at hb
      | some rδ =>
        obtain ⟨r, δ⟩ := rδ
        rw [hsb] at hb
        have hval := M.toSeg_val (M.pushed_mem_segments hsb)
        simp only [Finset.mem_union, Finset.mem_singleton] at hb
        rcases hb with rfl | hb
        · obtain ⟨w', rfl, hne, hk⟩ := semList_letter_nt h
          rw [hval] at hk
          exact ⟨List.cons_ne_nil b w', (kindSem_letter_iff hs hsb k w').2 hk⟩
        · split_ifs at hb with hc
          · simp only [Finset.mem_singleton] at hb
            subst hb
            rw [semList_letter h]
            simp only [Sem₀, hval] at hc
            exact ⟨List.cons_ne_nil b [], (kindSem_letter_iff hs hsb k []).2 hc⟩
          · simp at hb
  · simp [stepProds] at ho

theorem sem_of_splitProds (p : Fin M.states) (γ : M.Seg) (k : M.Kind)
    {o : List (Symbol Bool M.NT)} {w : List Bool} (ho : o ∈ M.splitProds p γ k)
    (h : SemList o w) : M.Sem (.node p γ k) w := by
  obtain ⟨γ, hγ⟩ := γ
  rcases γ with _ | ⟨Z, _ | ⟨Y, δ''⟩⟩
  · simp [splitProds] at ho
  · simp [splitProds] at ho
  · simp only [splitProds, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at ho
    have hZ := M.toSeg_val (M.single_mem_segments Z)
    have hδ := M.toSeg_val (M.tail_mem_segments hγ)
    have hne : Y :: δ'' ≠ [] := List.cons_ne_nil Y δ''
    rw [sem_node_iff]
    rcases ho with ho | ⟨q', (ho | ho) | ho⟩
    · cases k with
      | pop q e => simp at ho
      | rej s =>
        simp only [Finset.mem_singleton] at ho
        subst ho
        obtain ⟨hw, hk⟩ := semList_single_nt h
        rw [hZ] at hk
        exact ⟨hw, kindSem_of_noPop hne hk s⟩
    · split_ifs at ho with hc
      · simp only [Finset.mem_singleton] at ho
        subst ho
        obtain ⟨hw, hk⟩ := semList_single_nt h
        rw [hZ] at hk
        simp only [Sem₀, hδ] at hc
        exact ⟨hw, kindSem_of_pop_of_nil hne hk hc⟩
      · simp at ho
    · simp only [Finset.mem_singleton] at ho
      subst ho
      obtain ⟨w1, w2, rfl, ⟨hw1, hk1⟩, hw2, hk2⟩ := semList_two_nt h
      rw [hZ] at hk1
      rw [hδ] at hk2
      refine ⟨fun h0 => hw1 (List.append_eq_nil_iff.1 h0).1, ?_⟩
      exact kindSem_of_pop_append hne hk1.1 hk2 hw2
    · split_ifs at ho with hc
      · simp only [Finset.mem_singleton] at ho
        subst ho
        obtain ⟨hw, hk⟩ := semList_single_nt h
        rw [hδ] at hk
        refine ⟨hw, ?_⟩
        simpa using kindSem_of_pop_append hne (w1 := []) hc hk hw
      · simp at ho

/-- Local soundness: every production preserves the semantics. -/
theorem sem_of_rule {r : ContextFreeRule Bool M.NT} (hr : r ∈ M.rules) {w : List Bool}
    (h : SemList r.output w) : M.Sem r.input w := by
  rw [mem_rules_iff] at hr
  obtain ⟨X, o⟩ := r
  simp only at hr h ⊢
  cases X with
  | all => trivial
  | start =>
    simp only [prods, Finset.mem_union, Finset.mem_singleton] at hr
    rcases hr with rfl | hr
    · obtain ⟨-, hk⟩ := semList_single_nt h
      rw [M.toSeg_val (M.single_mem_segments _)] at hk
      exact hk.1
    · by_cases hc : M.Acc (M.start, [M.bottom]) []
      · rw [if_neg (not_not.2 hc)] at hr
        simp at hr
      · rw [if_pos hc] at hr
        have hr' : o = [] := Finset.mem_singleton.1 hr
        subst hr'
        simp only [SemList] at h
        subst h
        exact hc
  | node p γ k =>
    simp only [prods, Finset.mem_union] at hr
    rcases hr with (hr | hr) | hr
    · exact sem_of_deadProds p γ k hr h
    · exact sem_of_stepProds p γ k hr h
    · exact sem_of_splitProds p γ k hr h

theorem semList_of_forest {o : List (Symbol Bool M.complementCFG.NT)} {w : List Bool}
    (h : M.complementCFG.Forest o w) : SemList (M := M) o w := by
  induction h with
  | nil => rfl
  | terminal _ ih => exact ⟨_, rfl, ih⟩
  | nonterminal hr _ _ ih₁ ih₂ => exact ⟨_, _, rfl, sem_of_rule hr ih₁, ih₂⟩

theorem sem_of_gen {X : M.NT} {w : List Bool} (h : M.complementCFG.Gen X w) : M.Sem X w :=
  semList_single_nt (semList_of_forest h)

end Soundness

/-! ## Completeness: words with the property of a nonterminal are generated -/

section Completeness

variable {M}

theorem gen_of_prod {X : M.NT} {o : List (Symbol Bool M.NT)} {w : List Bool}
    (ho : o ∈ M.prods X) (hf : M.complementCFG.Forest o w) : M.complementCFG.Gen X w :=
  (gen_iff _).2 ⟨⟨X, o⟩, (M.mem_rules_iff _).2 ho, rfl, hf⟩

theorem forest_letter_nt {b : Bool} {X : M.NT} {w : List Bool} (h : M.complementCFG.Gen X w) :
    M.complementCFG.Forest [𝓣 b, 𝓝 X] (b :: w) :=
  Forest.terminal h

theorem forest_letter (b : Bool) : M.complementCFG.Forest [𝓣 b] [b] :=
  Forest.terminal Forest.nil

theorem forest_two_nt {X Y : M.NT} {w1 w2 : List Bool} (h1 : M.complementCFG.Gen X w1)
    (h2 : M.complementCFG.Gen Y w2) : M.complementCFG.Forest [𝓝 X, 𝓝 Y] (w1 ++ w2) :=
  (forest_nonterminal_cons_iff _).2 ⟨w1, w2, rfl, h1, h2⟩

theorem gen_all (w : List Bool) : M.complementCFG.Gen .all w := by
  induction w with
  | nil =>
    exact gen_of_prod (X := .all) (Finset.mem_union_left _ (Finset.mem_singleton_self _)) Forest.nil
  | cons b w ih =>
    exact gen_of_prod (X := .all)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ b)))
      (forest_letter_nt ih)

/-! ### Membership of the productions -/

theorem mem_deadProds {p : Fin M.states} {γ : M.Seg} {b : Bool} {s : Bool}
    (hd : M.Dead (p, γ.1) b) (hs : s = true → ∀ q, ¬ M.Pops (p, γ.1) [] q) :
    [𝓣 b, 𝓝 (NT.all)] ∈ M.prods (.node p γ (.rej s)) := by
  simp only [prods, Finset.mem_union]
  left; left
  simp only [deadProds, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b, ⟨hd, hs⟩, rfl⟩

theorem mem_stepProds_eps {p r : Fin M.states} {γ : M.Seg} {Y : Fin M.stack}
    {δ : List (Fin M.stack)} (hγ : γ.1 = [Y]) (hs : M.step p none Y = some (r, δ)) (k : M.Kind) :
    [𝓝 (NT.node r (M.toSeg δ) k)] ∈ M.prods (.node p γ k) := by
  simp only [prods, Finset.mem_union]
  left; right
  simp [stepProds, hγ, hs]

theorem mem_stepProds_letter {p r : Fin M.states} {γ : M.Seg} {Y : Fin M.stack} {b : Bool}
    {δ : List (Fin M.stack)} (hγ : γ.1 = [Y]) (hnone : M.step p none Y = none)
    (hsb : M.step p (some b) Y = some (r, δ)) (k : M.Kind) :
    [𝓣 b, 𝓝 (NT.node r (M.toSeg δ) k)] ∈ M.prods (.node p γ k) := by
  simp only [prods, Finset.mem_union]
  left; right
  simp only [stepProds, hγ, hnone, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨b, by simp [hsb]⟩

theorem mem_stepProds_letter_nil {p r : Fin M.states} {γ : M.Seg} {Y : Fin M.stack} {b : Bool}
    {δ : List (Fin M.stack)} (hγ : γ.1 = [Y]) (hnone : M.step p none Y = none)
    (hsb : M.step p (some b) Y = some (r, δ)) {k : M.Kind}
    (h0 : M.Sem₀ (.node r (M.toSeg δ) k) []) :
    [𝓣 b] ∈ M.prods (.node p γ k) := by
  simp only [prods, Finset.mem_union]
  left; right
  simp only [stepProds, hγ, hnone, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨b, by simp [hsb, h0]⟩

theorem mem_splitProds_noPop {p : Fin M.states} {γ : M.Seg} {Z Y : Fin M.stack}
    {δ'' : List (Fin M.stack)} (hγ : γ.1 = Z :: Y :: δ'') (s : Bool) :
    [𝓝 (NT.node p (M.toSeg [Z]) (.rej true))] ∈ M.prods (.node p γ (.rej s)) := by
  simp only [prods, Finset.mem_union]
  right
  simp [splitProds, hγ]

theorem mem_splitProds_first {p q' : Fin M.states} {γ : M.Seg} {Z Y : Fin M.stack}
    {δ'' : List (Fin M.stack)} (hγ : γ.1 = Z :: Y :: δ'') {k : M.Kind}
    (h0 : M.Sem₀ (.node q' (M.toSeg (Y :: δ'')) k) []) :
    [𝓝 (NT.node p (M.toSeg [Z]) (.pop q' k.first))] ∈ M.prods (.node p γ k) := by
  simp only [prods, Finset.mem_union]
  right
  simp only [splitProds, hγ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  right
  exact ⟨q', Or.inl (Or.inl (by simp [h0]))⟩

theorem mem_splitProds_two {p q' : Fin M.states} {γ : M.Seg} {Z Y : Fin M.stack}
    {δ'' : List (Fin M.stack)} (hγ : γ.1 = Z :: Y :: δ'') (k : M.Kind) :
    [𝓝 (NT.node p (M.toSeg [Z]) (.pop q' false)), 𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)] ∈
      M.prods (.node p γ k) := by
  simp only [prods, Finset.mem_union]
  right
  simp only [splitProds, hγ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  right
  exact ⟨q', Or.inl (Or.inr (by simp))⟩

theorem mem_splitProds_tail {p q' : Fin M.states} {γ : M.Seg} {Z Y : Fin M.stack}
    {δ'' : List (Fin M.stack)} (hγ : γ.1 = Z :: Y :: δ'') (k : M.Kind)
    (h : M.Pops (p, [Z]) [] q') :
    [𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)] ∈ M.prods (.node p γ k) := by
  simp only [prods, Finset.mem_union]
  right
  simp only [splitProds, hγ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  right
  exact ⟨q', Or.inr (by simp [h])⟩

/-! ### The semantics after a pop -/

/-- After the pop of the top symbol, the rest of the word has the kind's
property from the tail. -/
theorem kindSem_tail_of_pop {p q' : Fin M.states} {Z : Fin M.stack} {δ' : List (Fin M.stack)}
    (hδ : δ' ≠ []) {k : M.Kind} {u v : List Bool} (hp : M.Pops (p, [Z]) u q')
    (hk : M.KindSem k (p, Z :: δ') (u ++ v)) : M.KindSem k (q', δ') v := by
  have hacc : ¬ M.Acc (p, Z :: δ') (u ++ v) → ¬ M.Acc (q', δ') v := fun hacc h =>
    hacc ((acc_cons_iff p Z δ' _).2 (Or.inr ⟨q', u, v, rfl, hp, h⟩))
  cases k with
  | pop q e =>
    obtain ⟨hpz, he⟩ := hk
    rw [pops_cons_iff p Z hδ] at hpz
    obtain ⟨q'', w1, w2, hw, h1, h2⟩ := hpz
    obtain ⟨rfl, rfl⟩ := pops_unique' h1 hp
      (List.prefix_or_prefix_of_prefix (hw ▸ List.prefix_append w1 w2) (List.prefix_append u v))
    rw [List.append_cancel_left_eq] at hw
    subst hw
    exact ⟨h2, fun he' => hacc (he he')⟩
  | rej s =>
    obtain ⟨hacc', hnp⟩ := hk
    refine ⟨hacc hacc', fun hs u' q hu' hp' => ?_⟩
    exact hnp hs (u ++ u') q ((List.prefix_append_right_inj u).2 hu')
      ((pops_cons_iff p Z hδ _ _).2 ⟨q', u, u', rfl, hp, hp'⟩)

/-- When the word ends exactly at the pop of the top symbol, the part above
has the popping property and the empty word has the kind's property from the
tail. -/
theorem kindSem_split_of_pop_full {p q' : Fin M.states} {Z : Fin M.stack}
    {δ' : List (Fin M.stack)} (hδ : δ' ≠ []) {k : M.Kind} {w : List Bool}
    (hp : M.Pops (p, [Z]) w q') (hk : M.KindSem k (p, Z :: δ') w) :
    M.KindSem (.pop q' k.first) (p, [Z]) w ∧ M.KindSem k (q', δ') [] := by
  have hacc1 : ¬ M.Acc (p, Z :: δ') w → ¬ M.Acc (p, [Z]) w := fun hacc h =>
    hacc ((acc_cons_iff p Z δ' _).2 (Or.inl h))
  have hacc2 : ¬ M.Acc (p, Z :: δ') w → ¬ M.Acc (q', δ') [] := fun hacc h =>
    hacc ((acc_cons_iff p Z δ' _).2 (Or.inr ⟨q', w, [], (List.append_nil w).symm, hp, h⟩))
  cases k with
  | pop q e =>
    obtain ⟨hpz, he⟩ := hk
    rw [pops_cons_iff p Z hδ] at hpz
    obtain ⟨q'', w1, w2, hw, h1, h2⟩ := hpz
    obtain ⟨rfl, rfl⟩ := pops_unique h1 hp (hw ▸ List.prefix_append w1 w2)
    have : w2 = [] := by
      have := congrArg List.length hw
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨⟨hp, fun he' => hacc1 (he he')⟩, ⟨h2, fun he' => hacc2 (he he')⟩⟩
  | rej s =>
    obtain ⟨hacc, hnp⟩ := hk
    refine ⟨⟨hp, fun _ => hacc1 hacc⟩, ⟨hacc2 hacc, fun hs u' q hu' hp' => ?_⟩⟩
    rw [List.prefix_nil] at hu'
    subst hu'
    exact hnp hs w q (List.prefix_refl w)
      ((pops_cons_iff p Z hδ _ _).2 ⟨q', w, [], (List.append_nil w).symm, hp, hp'⟩)

/-! ### The epsilon chain along the productions -/

theorem epsIter_none_of_eps {p r : Fin M.states} {Y : Fin M.stack} {δ : List (Fin M.stack)}
    (hs : M.step p none Y = some (r, δ)) {j : ℕ} (h : M.epsIter (j + 1) (p, [Y]) = none) :
    M.epsIter j (r, δ) = none := by
  rw [epsIter_succ] at h
  simpa [epsStep, hs] using h

theorem epsIter_none_cons_of_pop_nil {p q' : Fin M.states} {Z : Fin M.stack}
    {δ' : List (Fin M.stack)} (hp : M.Pops (p, [Z]) [] q') {k₀ : ℕ}
    (h : M.epsIter k₀ (p, Z :: δ') = none) : ∃ j, j < k₀ ∧ M.epsIter j (q', δ') = none := by
  obtain ⟨j, hj⟩ := reach_nil_iff.1 hp
  have hj' : M.epsIter j (p, Z :: δ') = some (q', δ') := by
    have := epsIter_lift hj δ'
    simpa using this
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hj
  have hjk : j ≤ k₀ := by
    by_contra hlt
    obtain ⟨c'', hc''⟩ := epsIter_some_of_le hj' (le_of_lt (not_le.1 hlt))
    rw [hc''] at h
    cases h
  refine ⟨k₀ - j, by omega, ?_⟩
  have := epsIter_add j (k₀ - j) (p, Z :: δ')
  rw [Nat.add_sub_cancel' hjk, h, hj'] at this
  exact this.symm

theorem epsIter_none_single_of_cons {p : Fin M.states} {Z : Fin M.stack}
    {δ' : List (Fin M.stack)} {k₀ : ℕ} (h : M.epsIter k₀ (p, Z :: δ') = none) :
    M.epsIter k₀ (p, [Z]) = none :=
  epsIter_none_of_lift (c := (p, [Z])) (rest := δ') h

/-! ### The main induction -/

/-- Completeness at a fixed word, by induction on the epsilon chain and on the
segment, given completeness for shorter words. -/
theorem gen_node_of_sem_aux (w : List Bool)
    (ih : ∀ w' : List Bool, w'.length < w.length → ∀ X : M.NT, M.Sem X w' → M.complementCFG.Gen X w')
    (k₀ : ℕ) : ∀ (m : ℕ) (p : Fin M.states) (γ : M.Seg) (k : M.Kind),
      M.epsIter k₀ (p, γ.1) = none → γ.1.length ≤ m → M.Sem (.node p γ k) w →
      M.complementCFG.Gen (.node p γ k) w := by
  induction k₀ using Nat.strong_induction_on with
  | _ k₀ ihk =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro p γ k hk₀ hm hsem
  obtain ⟨hne, hk⟩ := hsem
  obtain ⟨γ, hγmem⟩ := γ
  simp only at hk hk₀ hm
  rcases γ with _ | ⟨Z, _ | ⟨Y, δ''⟩⟩
  · -- the empty stack: nothing is read
    cases k with
    | pop q e => exact absurd (reach_nil_stack hk.1).1 hne
    | rej s =>
      obtain ⟨b, w'⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨w', rfl⟩ := w'
      refine gen_of_prod (mem_deadProds (γ := ⟨[], hγmem⟩) (dead_nil p b) ?_) (forest_letter_nt (gen_all w'))
      intro hs q
      exact hk.2 hs [] q List.nil_prefix
  · -- a single symbol: follow the unique move
    cases hs : M.step p none Z with
    | some rδ =>
      obtain ⟨r, δ⟩ := rδ
      have hval := M.toSeg_val (M.pushed_mem_segments hs)
      refine gen_of_prod (mem_stepProds_eps (γ := ⟨[Z], hγmem⟩) rfl hs k) ?_
      show M.complementCFG.Gen _ _
      cases k₀ with
      | zero => cases hk₀
      | succ j =>
        refine ihk j (Nat.lt_succ_self j) δ.length r (M.toSeg δ) k ?_ (by rw [hval]) ?_
        · rw [hval]
          exact epsIter_none_of_eps hs hk₀
        · refine ⟨hne, ?_⟩
          rw [hval]
          exact (kindSem_eps_iff hs k hne).1 hk
    | none =>
      obtain ⟨b, w'⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨w', rfl⟩ := w'
      cases hsb : M.step p (some b) Z with
      | some rδ =>
        obtain ⟨r, δ⟩ := rδ
        have hval := M.toSeg_val (M.pushed_mem_segments hsb)
        have hk' : M.KindSem k (r, δ) w' := (kindSem_letter_iff hs hsb k w').1 hk
        cases w' with
        | nil =>
          refine gen_of_prod (mem_stepProds_letter_nil (γ := ⟨[Z], hγmem⟩) rfl hs hsb ?_)
            (forest_letter b)
          show M.KindSem k (r, (M.toSeg δ).1) []
          rw [hval]
          exact hk'
        | cons b' w'' =>
          refine gen_of_prod (mem_stepProds_letter (γ := ⟨[Z], hγmem⟩) rfl hs hsb k)
            (forest_letter_nt ?_)
          refine ih (b' :: w'') (by simp) _ ⟨List.cons_ne_nil b' w'', ?_⟩
          show M.KindSem k (r, (M.toSeg δ).1) _
          rw [hval]
          exact hk'
      | none =>
        cases k with
        | pop q e => exact absurd hk.1 (not_reach_single_stuck hs hsb)
        | rej s =>
          refine gen_of_prod (mem_deadProds (γ := ⟨[Z], hγmem⟩) (dead_of_stuck hs hsb) ?_)
            (forest_letter_nt (gen_all w'))
          intro hs' q
          exact hk.2 hs' [] q List.nil_prefix
  · -- a long segment: split at the pop of the top symbol
    have hδ : Y :: δ'' ≠ [] := List.cons_ne_nil Y δ''
    have hZ := M.toSeg_val (M.single_mem_segments Z)
    have hT := M.toSeg_val (M.tail_mem_segments hγmem)
    have hm2 : 1 < m := by simp at hm; omega
    by_cases hpop : ∃ u q', u <+: w ∧ M.Pops (p, [Z]) u q'
    · obtain ⟨u, q', ⟨v, rfl⟩, hp⟩ := hpop
      by_cases hv : v = []
      · -- the word ends at the pop
        subst hv
        rw [List.append_nil] at hk hne ih ihk ihm ⊢
        obtain ⟨h1, h2⟩ := kindSem_split_of_pop_full hδ hp hk
        refine gen_of_prod (mem_splitProds_first (γ := ⟨Z :: Y :: δ'', hγmem⟩) (q' := q') rfl ?_) ?_
        · show M.KindSem k (q', (M.toSeg (Y :: δ'')).1) []
          rw [hT]
          exact h2
        · show M.complementCFG.Gen _ _
          refine ihm 1 hm2 p (M.toSeg [Z]) _ ?_ (by rw [hZ]; exact le_rfl) ⟨hne, ?_⟩
          · rw [hZ]
            exact epsIter_none_single_of_cons hk₀
          · rw [hZ]
            exact h1
      · have hk2 : M.KindSem k (q', Y :: δ'') v := kindSem_tail_of_pop hδ hp hk
        by_cases hu : u = []
        · -- the pop is by epsilon moves
          subst hu
          rw [List.nil_append] at hk hne ih ihk ihm ⊢
          refine gen_of_prod (mem_splitProds_tail (γ := ⟨Z :: Y :: δ'', hγmem⟩) rfl k hp) ?_
          show M.complementCFG.Gen _ _
          obtain ⟨j, hj, hj'⟩ := epsIter_none_cons_of_pop_nil hp hk₀
          refine ihk j hj (Y :: δ'').length q' (M.toSeg (Y :: δ'')) k ?_ (by rw [hT]) ⟨hne, ?_⟩
          · rw [hT]
            exact hj'
          · rw [hT]
            exact hk2
        · -- both parts are nonempty
          refine gen_of_prod (mem_splitProds_two (γ := ⟨Z :: Y :: δ'', hγmem⟩) (q' := q') rfl k)
            (forest_two_nt ?_ ?_)
          · refine ih u ?_ _ ⟨hu, ?_⟩
            · have := List.length_pos_of_ne_nil hv
              simp only [List.length_append]
              omega
            · show M.KindSem (.pop q' false) (p, (M.toSeg [Z]).1) u
              rw [hZ]
              exact ⟨hp, fun h => absurd h Bool.false_ne_true⟩
          · refine ih v ?_ _ ⟨hv, ?_⟩
            · have := List.length_pos_of_ne_nil hu
              simp only [List.length_append]
              omega
            · show M.KindSem k (q', (M.toSeg (Y :: δ'')).1) v
              rw [hT]
              exact hk2
    · -- the top symbol is never popped
      cases k with
      | pop q e =>
        obtain ⟨hpz, _⟩ := hk
        rw [pops_cons_iff p Z hδ] at hpz
        obtain ⟨q', w1, w2, rfl, h1, _⟩ := hpz
        exact absurd ⟨w1, q', List.prefix_append w1 w2, h1⟩ hpop
      | rej s =>
        obtain ⟨hacc, _⟩ := hk
        refine gen_of_prod (mem_splitProds_noPop (γ := ⟨Z :: Y :: δ'', hγmem⟩) rfl s) ?_
        show M.complementCFG.Gen _ _
        refine ihm 1 hm2 p (M.toSeg [Z]) (.rej true) ?_ (by rw [hZ]; exact le_rfl) ⟨hne, ?_⟩
        · rw [hZ]
          exact epsIter_none_single_of_cons hk₀
        · rw [hZ]
          refine ⟨fun h => hacc ((acc_cons_iff p Z _ w).2 (Or.inl h)), fun _ u q hu hp => ?_⟩
          exact hpop ⟨u, q, hu, hp⟩

/-- Completeness for every nonterminal. -/
theorem gen_of_sem : ∀ (w : List Bool) (X : M.NT), M.Sem X w → M.complementCFG.Gen X w := by
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  intro X hsem
  have ih' : ∀ w' : List Bool, w'.length < w.length → ∀ X : M.NT, M.Sem X w' →
      M.complementCFG.Gen X w' := fun w' hw' X h => ih w'.length (hn ▸ hw') w' rfl X h
  cases X with
  | all => exact gen_all w
  | start =>
    cases w with
    | nil =>
      refine gen_of_prod (X := .start) (o := []) ?_ Forest.nil
      refine Finset.mem_union_right _ ?_
      have hsem' : ¬ M.Acc (M.start, [M.bottom]) [] := hsem
      rw [if_pos hsem']
      exact Finset.mem_singleton_self _
    | cons b w' =>
      refine gen_of_prod (X := .start) (o := [𝓝 (NT.node M.start (M.toSeg [M.bottom]) (.rej false))])
        (Finset.mem_union_left _ (Finset.mem_singleton_self _)) ?_
      show M.complementCFG.Gen _ _
      have hval := M.toSeg_val (M.single_mem_segments M.bottom)
      have hsem' : M.Sem (.node M.start (M.toSeg [M.bottom]) (.rej false)) (b :: w') := by
        refine ⟨List.cons_ne_nil b w', ?_⟩
        rw [hval]
        exact ⟨hsem, fun h => absurd h Bool.false_ne_true⟩
      by_cases hl : M.Loops (M.start, (M.toSeg [M.bottom]).1)
      · refine gen_of_prod (mem_deadProds (dead_of_loops hl b) fun h => absurd h Bool.false_ne_true)
          (forest_letter_nt (gen_all w'))
      · obtain ⟨k₀, hk₀⟩ := not_loops_iff.1 hl
        exact gen_node_of_sem_aux (b :: w') ih' k₀ _ _ _ _ hk₀ le_rfl hsem'
  | node p γ k =>
    by_cases hl : M.Loops (p, γ.1)
    · obtain ⟨hne, hk⟩ := hsem
      obtain ⟨b, w'⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨w', rfl⟩ := w'
      cases k with
      | pop q e => exact absurd hk.1 (not_reach_nil_stack_of_loops hl)
      | rej s =>
        exact gen_of_prod (mem_deadProds (dead_of_loops hl b)
          fun _ q h => not_reach_nil_stack_of_loops hl h) (forest_letter_nt (gen_all w'))
    · obtain ⟨k₀, hk₀⟩ := not_loops_iff.1 hl
      exact gen_node_of_sem_aux w ih' k₀ _ _ _ _ hk₀ le_rfl hsem

end Completeness

/-! ## The language -/

theorem gen_iff_sem (X : M.NT) (w : List Bool) : M.complementCFG.Gen X w ↔ M.Sem X w :=
  ⟨sem_of_gen, gen_of_sem w X⟩

/-- The complement grammar generates exactly the words the automaton rejects. -/
theorem complementCFG_language (w : List Bool) :
    w ∈ M.complementCFG.language ↔ w ∉ M.language := by
  rw [mem_language_iff_gen]
  exact gen_iff_sem M .start w

/-! ## Size -/

section Size

instance : Fintype M.complementCFG.NT := inferInstanceAs (Fintype M.NT)
instance : DecidableEq M.complementCFG.NT := inferInstanceAs (DecidableEq M.NT)

variable {M}

/-- Every right-hand side has at most two symbols. -/
theorem prods_length_le (X : M.NT) {o : List (Symbol Bool M.NT)} (ho : o ∈ M.prods X) :
    o.length ≤ 2 := by
  cases X with
  | all =>
    simp only [prods, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
      true_and] at ho
    rcases ho with rfl | ⟨b, rfl⟩ <;> simp
  | start =>
    simp only [prods, Finset.mem_union, Finset.mem_singleton] at ho
    rcases ho with rfl | ho
    · simp
    · split_ifs at ho with hc
      · simp at ho
      · simp only [Finset.mem_singleton] at ho
        subst ho
        simp
  | node p γ k =>
    simp only [prods, Finset.mem_union] at ho
    rcases ho with (ho | ho) | ho
    · cases k with
      | pop q e => simp [deadProds] at ho
      | rej s =>
        simp only [deadProds, Finset.mem_image] at ho
        obtain ⟨b, -, rfl⟩ := ho
        simp
    · obtain ⟨γ, hγ⟩ := γ
      rcases γ with _ | ⟨Y, _ | ⟨Y', rest⟩⟩
      · simp [stepProds] at ho
      · simp only [stepProds] at ho
        cases hs : M.step p none Y with
        | some rδ =>
          obtain ⟨r, δ⟩ := rδ
          rw [hs] at ho
          simp only [Finset.mem_singleton] at ho
          subst ho
          simp
        | none =>
          rw [hs] at ho
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ho
          obtain ⟨b, hb⟩ := ho
          cases hsb : M.step p (some b) Y with
          | none => rw [hsb] at hb; simp at hb
          | some rδ =>
            obtain ⟨r, δ⟩ := rδ
            rw [hsb] at hb
            simp only [Finset.mem_union, Finset.mem_singleton] at hb
            rcases hb with rfl | hb
            · simp
            · split_ifs at hb with hc
              · simp only [Finset.mem_singleton] at hb
                subst hb
                simp
              · simp at hb
      · simp [stepProds] at ho
    · obtain ⟨γ, hγ⟩ := γ
      rcases γ with _ | ⟨Z, _ | ⟨Y, δ''⟩⟩
      · simp [splitProds] at ho
      · simp [splitProds] at ho
      · simp only [splitProds, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
          true_and] at ho
        rcases ho with ho | ⟨q', (ho | ho) | ho⟩
        · cases k with
          | pop q e => simp at ho
          | rej s =>
            simp only [Finset.mem_singleton] at ho
            subst ho
            simp
        · split_ifs at ho with hc
          · simp only [Finset.mem_singleton] at ho
            subst ho
            simp
          · simp at ho
        · simp only [Finset.mem_singleton] at ho
          subst ho
          simp
        · split_ifs at ho with hc
          · simp only [Finset.mem_singleton] at ho
            subst ho
            simp
          · simp at ho

theorem card_deadProds_le (p : Fin M.states) (γ : M.Seg) (k : M.Kind) :
    (M.deadProds p γ k).card ≤ 2 := by
  cases k with
  | pop q e => simp [deadProds]
  | rej s =>
    simp only [deadProds]
    refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    simp

theorem card_stepProds_le (p : Fin M.states) (γ : M.Seg) (k : M.Kind) :
    (M.stepProds p γ k).card ≤ 4 := by
  obtain ⟨γ, hγ⟩ := γ
  rcases γ with _ | ⟨Y, _ | ⟨Y', rest⟩⟩
  · simp [stepProds]
  · simp only [stepProds]
    cases hs : M.step p none Y with
    | some rδ =>
      obtain ⟨r, δ⟩ := rδ
      simp
    | none =>
      refine Finset.card_biUnion_le.trans ?_
      have hb : ∀ b : Bool, (match M.step p (some b) Y with
          | some (r, δ) =>
            {[𝓣 b, 𝓝 (NT.node r (M.toSeg δ) k)]} ∪
              (if M.Sem₀ (.node r (M.toSeg δ) k) [] then {[𝓣 b]} else ∅)
          | none => (∅ : Finset (List (Symbol Bool M.NT)))).card ≤ 2 := by
        intro b
        cases hsb : M.step p (some b) Y with
        | none => simp
        | some rδ =>
          obtain ⟨r, δ⟩ := rδ
          refine (Finset.card_union_le _ _).trans ?_
          split_ifs <;> simp
      calc ∑ b : Bool, _ ≤ ∑ _b : Bool, 2 := Finset.sum_le_sum fun b _ => hb b
        _ = 4 := by simp
  · simp [stepProds]

theorem card_splitProds_le (p : Fin M.states) (γ : M.Seg) (k : M.Kind) :
    (M.splitProds p γ k).card ≤ 1 + 3 * M.states := by
  obtain ⟨γ, hγ⟩ := γ
  rcases γ with _ | ⟨Z, _ | ⟨Y, δ''⟩⟩
  · simp [splitProds]
  · simp [splitProds]
  · simp only [splitProds]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · cases k <;> simp
    · refine Finset.card_biUnion_le.trans ?_
      have hq : ∀ q' : Fin M.states,
          ((if M.Sem₀ (.node q' (M.toSeg (Y :: δ'')) k) [] then
            {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' k.first))]} else ∅) ∪
          {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' false)), 𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} ∪
          (if M.Pops (p, [Z]) [] q' then {[𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} else ∅) :
            Finset (List (Symbol Bool M.NT))).card ≤ 3 := by
        intro q'
        have h1 : (if M.Sem₀ (.node q' (M.toSeg (Y :: δ'')) k) [] then
            {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' k.first))]} else ∅ :
            Finset (List (Symbol Bool M.NT))).card ≤ 1 := by
          split_ifs <;> simp
        have h2 : ({[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' false)),
            𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} :
            Finset (List (Symbol Bool M.NT))).card ≤ 1 := by simp
        have h3 : (if M.Pops (p, [Z]) [] q' then {[𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} else ∅ :
            Finset (List (Symbol Bool M.NT))).card ≤ 1 := by
          split_ifs <;> simp
        have hu1 := Finset.card_union_le
          (if M.Sem₀ (.node q' (M.toSeg (Y :: δ'')) k) [] then
            {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' k.first))]} else ∅ :
            Finset (List (Symbol Bool M.NT)))
          ({[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' false)),
            𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} :
            Finset (List (Symbol Bool M.NT)))
        have hu2 := Finset.card_union_le
          ((if M.Sem₀ (.node q' (M.toSeg (Y :: δ'')) k) [] then
            {[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' k.first))]} else ∅ :
            Finset (List (Symbol Bool M.NT))) ∪
          ({[𝓝 (NT.node p (M.toSeg [Z]) (.pop q' false)),
            𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} :
            Finset (List (Symbol Bool M.NT))))
          (if M.Pops (p, [Z]) [] q' then {[𝓝 (NT.node q' (M.toSeg (Y :: δ'')) k)]} else ∅ :
            Finset (List (Symbol Bool M.NT)))
        omega
      calc ∑ q' : Fin M.states, _ ≤ ∑ _q' : Fin M.states, 3 := Finset.sum_le_sum fun q' _ => hq q'
        _ = 3 * M.states := by simp [mul_comm]

theorem card_prods_le (X : M.NT) : (M.prods X).card ≤ 7 + 3 * M.states := by
  cases X with
  | all =>
    simp only [prods]
    refine (Finset.card_union_le _ _).trans ?_
    have := Finset.card_image_le (s := (Finset.univ : Finset Bool))
      (f := fun b : Bool => ([𝓣 b, 𝓝 (NT.all)] : List (Symbol Bool M.NT)))
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_bool] at this ⊢
    omega
  | start =>
    simp only [prods]
    refine (Finset.card_union_le _ _).trans ?_
    split_ifs <;> simp <;> omega
  | node p γ k =>
    simp only [prods]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_deadProds_le p γ k) (card_stepProds_le p γ k)))
      (card_splitProds_le p γ k)) |>.trans ?_
    omega

theorem card_rules_le : M.rules.card ≤ Fintype.card M.NT * (7 + 3 * M.states) := by
  simp only [rules]
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ X : M.NT, ((M.prods X).image fun o => (⟨X, o⟩ : ContextFreeRule Bool M.NT)).card
      ≤ ∑ _X : M.NT, (7 + 3 * M.states) :=
        Finset.sum_le_sum fun X _ => Finset.card_image_le.trans (card_prods_le X)
    _ = Fintype.card M.NT * (7 + 3 * M.states) := by simp

/-- Injecting the kinds into a product-sum type. -/
def Kind.toSum : M.Kind → (Fin M.states × Bool) ⊕ Bool
  | .pop q e => Sum.inl (q, e)
  | .rej s => Sum.inr s

theorem Kind.toSum_injective : Function.Injective (Kind.toSum (M := M)) := by
  intro k₁ k₂ h
  cases k₁ <;> cases k₂ <;> simp [Kind.toSum] at h <;> simp_all

theorem card_kind_le : Fintype.card M.Kind ≤ 2 * M.states + 2 := by
  have := Fintype.card_le_of_injective _ (Kind.toSum_injective (M := M))
  simpa [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, mul_comm]
    using this

/-- Injecting the nonterminals into an option type. -/
def NT.toOption : M.NT → Option (Option (Fin M.states × M.Seg × M.Kind))
  | .node p γ k => some (some (p, γ, k))
  | .all => some none
  | .start => none

theorem NT.toOption_injective : Function.Injective (NT.toOption (M := M)) := by
  intro X₁ X₂ h
  cases X₁ <;> cases X₂ <;> simp [NT.toOption] at h <;> simp_all

theorem card_segments_le : M.segments.card ≤ 1 + M.stack + (M.transitionCount + M.pushLength) := by
  simp only [segments]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
    (Nat.add_le_add le_rfl (Finset.card_image_le.trans ?_))) ?_)
  · simp
  · refine Finset.card_biUnion_le.trans ?_
    have ht : ∀ t : Fin M.states × Option Bool × Fin M.stack,
        ((M.pushed t).elim ∅ fun δ => δ.tails.toFinset).card ≤
          (if (M.step t.1 t.2.1 t.2.2).isSome = true then 1 else 0) +
            ((M.step t.1 t.2.1 t.2.2).map fun r => r.2.length).getD 0 := by
      intro t
      simp only [pushed]
      cases M.step t.1 t.2.1 t.2.2 with
      | none => simp
      | some r =>
        simp only [Option.map_some, Option.elim, Option.isSome_some, if_true, Option.getD_some]
        refine (List.toFinset_card_le _).trans ?_
        rw [List.length_tails]
        omega
    refine (Finset.sum_le_sum fun t _ => ht t).trans ?_
    rw [Finset.sum_add_distrib, transitionCount, pushLength]
    simp only [Fintype.sum_prod_type]
    exact le_rfl

theorem card_segments_le_size : M.segments.card ≤ M.size := by
  have := card_segments_le (M := M)
  unfold size
  omega

theorem card_nt_le : Fintype.card M.NT ≤ M.states * M.segments.card * (2 * M.states + 2) + 2 := by
  have h := Fintype.card_le_of_injective _ (NT.toOption_injective (M := M))
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at h
  have hk := card_kind_le (M := M)
  calc Fintype.card M.NT ≤ M.states * (M.segments.card * Fintype.card M.Kind) + 1 + 1 := h
    _ ≤ M.states * (M.segments.card * (2 * M.states + 2)) + 1 + 1 := by
        gcongr
    _ = M.states * M.segments.card * (2 * M.states + 2) + 2 := by ring

theorem states_pos : 0 < M.states := M.start.pos

theorem card_nt_le_size : Fintype.card M.NT ≤ 6 * M.size ^ 3 := by
  have h1 := card_nt_le (M := M)
  have h2 := card_segments_le_size (M := M)
  have h3 := M.states_le_size
  have h4 : 1 ≤ M.size := (states_pos (M := M)).trans_le h3
  calc Fintype.card M.NT ≤ M.states * M.segments.card * (2 * M.states + 2) + 2 := h1
    _ ≤ M.size * M.size * (2 * M.size + 2) + 2 := by gcongr
    _ ≤ 6 * M.size ^ 3 := by nlinarith

/-- The complement grammar has size at most the ninth power of the automaton's size. -/
theorem sourceParameter_complementCFG_le : sourceParameter M.complementCFG ≤ M.size ^ 9 := by
  have hsum : ∑ rule : RuleRef M.complementCFG, rule.1.output.length ≤
      M.rules.card * 2 := by
    calc ∑ rule : RuleRef M.complementCFG, rule.1.output.length
        ≤ (Finset.univ : Finset (RuleRef M.complementCFG)).card • 2 :=
          Finset.sum_le_card_nsmul _ _ _ fun rule _ =>
            prods_length_le rule.1.input ((M.mem_rules_iff rule.1).1 rule.2)
      _ = M.rules.card * 2 := by
          rw [smul_eq_mul, Finset.card_univ]
          congr 1
          exact Fintype.card_coe M.rules
  have hnt := card_nt_le_size (M := M)
  have hrules := card_rules_le (M := M)
  have hs := M.states_le_size
  have h3 : 3 ≤ M.size := by
    have := states_pos (M := M)
    unfold size
    omega
  have hcard : Fintype.card M.complementCFG.NT = Fintype.card M.NT := rfl
  have htotal : sourceParameter M.complementCFG ≤ 6 * M.size ^ 3 * (21 * M.size) := by
    unfold sourceParameter
    rw [hcard]
    calc Fintype.card M.NT + ∑ rule : RuleRef M.complementCFG, rule.1.output.length
        ≤ Fintype.card M.NT + M.rules.card * 2 := Nat.add_le_add le_rfl hsum
      _ ≤ Fintype.card M.NT + Fintype.card M.NT * (7 + 3 * M.states) * 2 := by gcongr
      _ = Fintype.card M.NT * (15 + 6 * M.states) := by ring
      _ ≤ 6 * M.size ^ 3 * (15 + 6 * M.size) := by gcongr
      _ ≤ 6 * M.size ^ 3 * (21 * M.size) := by gcongr; omega
  have hpow : 6 * M.size ^ 3 * (21 * M.size) ≤ M.size ^ 9 := by
    have h5 : 243 ≤ M.size ^ 5 := by
      calc 243 = 3 ^ 5 := by norm_num
        _ ≤ M.size ^ 5 := Nat.pow_le_pow_left h3 5
    calc 6 * M.size ^ 3 * (21 * M.size) = 126 * M.size ^ 4 := by ring
      _ ≤ M.size ^ 5 * M.size ^ 4 := by
          exact Nat.mul_le_mul_right _ (by omega)
      _ = M.size ^ 9 := by ring
  exact htotal.trans hpow

end Size

end DDNNFNegation.Pushdown.DPDA
