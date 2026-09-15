import DDNNFNegationCorollaries.Supporting.FiniteClosure

/-!
# Fixed-length parsing with epsilon and unit rules

The grammar in this file permits epsilon, terminal, unit, and binary rules.
Parsing is the least fixed point over facts saying that a nonterminal derives a
possibly empty interval.  Finite closure shows that one round per possible fact
is enough, even when unit rules contain cycles.
-/

namespace DDNNFNegation

/-- A grammar whose right-hand sides have length at most two. -/
structure ExtendedBinaryCFG (Nonterminal : Type*) where
  start : Nonterminal
  epsilonRules : Finset Nonterminal
  terminalRules : Finset (Nonterminal × Bool)
  unitRules : Finset (Nonterminal × Nonterminal)
  binaryRules : Finset (Nonterminal × Nonterminal × Nonterminal)

/-- A possibly empty half-open interval `[start, stop)` in a length-`N` word. -/
abbrev WordSpan (N : ℕ) :=
  { endpoints : Fin (N + 1) × Fin (N + 1) // endpoints.1 ≤ endpoints.2 }

namespace WordSpan

def start {N : ℕ} (s : WordSpan N) : ℕ := s.1.1.val

def stop {N : ℕ} (s : WordSpan N) : ℕ := s.1.2.val

def length {N : ℕ} (s : WordSpan N) : ℕ := s.stop - s.start

theorem start_le_stop {N : ℕ} (s : WordSpan N) : s.start ≤ s.stop :=
  by simpa [start, stop] using s.2

theorem stop_le {N : ℕ} (s : WordSpan N) : s.stop ≤ N := by
  change s.1.2.val ≤ N
  exact Nat.lt_succ_iff.mp (by simpa [Nat.add_comm] using s.1.2.isLt)

/-- Any boundary in the span, including either endpoint. -/
abbrev Split {N : ℕ} (s : WordSpan N) :=
  { k : Fin (N + 1) // s.1.1 ≤ k ∧ k ≤ s.1.2 }

def left {N : ℕ} (s : WordSpan N) (k : s.Split) : WordSpan N :=
  ⟨(s.1.1, k.1), k.2.1⟩

def right {N : ℕ} (s : WordSpan N) (k : s.Split) : WordSpan N :=
  ⟨(k.1, s.1.2), k.2.2⟩

def full (N : ℕ) : WordSpan N :=
  ⟨(⟨0, by omega⟩, ⟨N, by omega⟩), by simp⟩

end WordSpan

namespace ExtendedBinaryCFG

variable {Nonterminal : Type*} [Fintype Nonterminal]
  [DecidableEq Nonterminal]

/-- The ordinary finite derivation-tree semantics on a fixed word span. -/
inductive DerivesSpan {N : ℕ} (G : ExtendedBinaryCFG Nonterminal)
    (v : Fin N → Bool) : Nonterminal → WordSpan N → Prop where
  | epsilon {A : Nonterminal} {s : WordSpan N}
      (length_eq : s.length = 0) (rule_mem : A ∈ G.epsilonRules) :
      G.DerivesSpan v A s
  | terminal {A : Nonterminal} {s : WordSpan N} (i : Fin N)
      (start_eq : s.start = i.val) (stop_eq : s.stop = i.val + 1)
      (rule_mem : (A, v i) ∈ G.terminalRules) : G.DerivesSpan v A s
  | unit {A B : Nonterminal} {s : WordSpan N}
      (rule_mem : (A, B) ∈ G.unitRules)
      (child : G.DerivesSpan v B s) : G.DerivesSpan v A s
  | binary {A B C : Nonterminal} {s : WordSpan N}
      (rule_mem : (A, B, C) ∈ G.binaryRules) (k : s.Split)
      (left : G.DerivesSpan v B (s.left k))
      (right : G.DerivesSpan v C (s.right k)) : G.DerivesSpan v A s

def CanDeriveFrom {N : ℕ} (G : ExtendedBinaryCFG Nonterminal)
    (v : Fin N → Bool) (known : Finset (Nonterminal × WordSpan N))
    (fact : Nonterminal × WordSpan N) : Prop :=
  fact ∈ known ∨
  (fact.2.length = 0 ∧ fact.1 ∈ G.epsilonRules) ∨
  (∃ i : Fin N, fact.2.start = i.val ∧ fact.2.stop = i.val + 1 ∧
    (fact.1, v i) ∈ G.terminalRules) ∨
  (∃ B, (fact.1, B) ∈ G.unitRules ∧ (B, fact.2) ∈ known) ∨
  (∃ B C, (fact.1, B, C) ∈ G.binaryRules ∧
    ∃ k : fact.2.Split,
      (B, fact.2.left k) ∈ known ∧ (C, fact.2.right k) ∈ known)

noncomputable def closureStep {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    (known : Finset (Nonterminal × WordSpan N)) :
    Finset (Nonterminal × WordSpan N) := by
  classical
  exact Finset.univ.filter (CanDeriveFrom G v known)

omit [DecidableEq Nonterminal] in
theorem mem_closureStep_iff {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    (known : Finset (Nonterminal × WordSpan N))
    (fact : Nonterminal × WordSpan N) :
    fact ∈ closureStep G v known ↔ CanDeriveFrom G v known fact := by
  simp [closureStep]

omit [DecidableEq Nonterminal] in
private theorem closureStep_inflationary {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool) :
    ∀ known, known ⊆ closureStep G v known := by
  intro known fact hfact
  rw [mem_closureStep_iff]
  exact Or.inl hfact

omit [DecidableEq Nonterminal] in
private theorem closureStep_monotone {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool) :
    Monotone (closureStep G v) := by
  intro smaller larger hsubset fact hfact
  rw [mem_closureStep_iff] at hfact ⊢
  rcases hfact with hknown | hepsilon | hterminal | hunit | hbinary
  · exact Or.inl (hsubset hknown)
  · exact Or.inr (Or.inl hepsilon)
  · exact Or.inr (Or.inr (Or.inl hterminal))
  · rcases hunit with ⟨B, hrule, hchild⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨B, hrule, hsubset hchild⟩)))
  · rcases hbinary with ⟨B, C, hrule, k, hleft, hright⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨B, C, hrule, k, hsubset hleft, hsubset hright⟩)))

/-- Facts known after a fixed number of simultaneous closure rounds. -/
noncomputable def parseFactsAt {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool) (round : ℕ) :
    Finset (Nonterminal × WordSpan N) :=
  FiniteClosure.iterate (closureStep G v) round

/-- One round per possible fact suffices. -/
def closureRounds (Nonterminal : Type*) [Fintype Nonterminal] (N : ℕ) : ℕ :=
  Fintype.card (Nonterminal × WordSpan N)

omit [DecidableEq Nonterminal] in
private theorem parseFactsAt_sound {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool) :
    ∀ round fact, fact ∈ G.parseFactsAt v round →
      G.DerivesSpan v fact.1 fact.2 := by
  intro round
  induction round with
  | zero => simp [parseFactsAt, FiniteClosure.iterate]
  | succ round ih =>
      intro fact hfact
      rw [parseFactsAt, FiniteClosure.iterate_succ,
        mem_closureStep_iff] at hfact
      rcases hfact with hknown | hepsilon | hterminal | hunit | hbinary
      · exact ih fact hknown
      · exact .epsilon hepsilon.1 hepsilon.2
      · rcases hterminal with ⟨i, hstart, hstop, hrule⟩
        exact .terminal i hstart hstop hrule
      · rcases hunit with ⟨B, hrule, hchild⟩
        exact .unit hrule (ih (B, fact.2) hchild)
      · rcases hbinary with ⟨B, C, hrule, k, hleft, hright⟩
        exact .binary hrule k (ih (B, fact.2.left k) hleft)
          (ih (C, fact.2.right k) hright)

private theorem derivesSpan_mem_final {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    {A : Nonterminal} {s : WordSpan N} (h : G.DerivesSpan v A s) :
    (A, s) ∈ G.parseFactsAt v (closureRounds Nonterminal N) := by
  let final := G.parseFactsAt v (closureRounds Nonterminal N)
  have hfixed : closureStep G v final = final := by
    exact FiniteClosure.fixed_at_card (closureStep G v)
      (closureStep_inflationary G v)
  have addFact (fact : Nonterminal × WordSpan N)
      (hcan : CanDeriveFrom G v final fact) : fact ∈ final := by
    rw [← hfixed, mem_closureStep_iff]
    exact hcan
  induction h with
  | epsilon hlength hrule =>
      exact addFact _ (Or.inr (Or.inl ⟨hlength, hrule⟩))
  | terminal i hstart hstop hrule =>
      exact addFact _ (Or.inr (Or.inr (Or.inl
        ⟨i, hstart, hstop, hrule⟩)))
  | unit hrule _ ih =>
      exact addFact _ (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨_, hrule, ih⟩))))
  | binary hrule k _ _ ihLeft ihRight =>
      exact addFact _ (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨_, _, hrule, k, ihLeft, ihRight⟩))))

theorem mem_final_iff_derivesSpan {N : ℕ}
    (G : ExtendedBinaryCFG Nonterminal) (v : Fin N → Bool)
    (A : Nonterminal) (s : WordSpan N) :
    (A, s) ∈ G.parseFactsAt v (closureRounds Nonterminal N) ↔
      G.DerivesSpan v A s :=
  ⟨fun h ↦ parseFactsAt_sound G v _ _ h, derivesSpan_mem_final G v⟩

end ExtendedBinaryCFG

end DDNNFNegation
