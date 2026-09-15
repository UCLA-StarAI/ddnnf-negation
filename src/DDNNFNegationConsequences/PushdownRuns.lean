import DDNNFNegationConsequences.DeterministicPushdown

/-!
# Runs of a deterministic pushdown automaton

Run lemmas track consumed words and stack changes, including epsilon
moves. For runs from the same configuration on prefix-comparable input
words, determinism orders the runs by continuation, allowing an epsilon
extension in the reverse direction when they consumed the same word.
The popping lemmas provide the stack summaries used by the complement
grammar.
-/

namespace DDNNFNegation.Pushdown.DPDA

variable {M : DPDA}

/-- Runs compose. -/
theorem Reach.trans {c c' c'' : M.Config} {w w' : List Bool}
    (h : Reach M c w c') (h' : Reach M c' w' c'') : Reach M c (w ++ w') c'' := by
  induction h with
  | refl _ => simpa using h'
  | eps hs _ ih => exact Reach.eps hs (ih h')
  | letter hs _ ih => exact Reach.letter hs (ih h')

/-- The machine halts on an empty stack. -/
theorem reach_nil_stack {q : Fin M.states} {w : List Bool} {c : M.Config}
    (h : Reach M (q, []) w c) : w = [] ∧ c = (q, []) := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩

/-- A run on stack `γ` is a run on stack `γ ++ rest`. -/
theorem Reach.lift' {c c' : M.Config} {w : List Bool}
    (h : Reach M c w c') (rest : List (Fin M.stack)) :
    Reach M (c.1, c.2 ++ rest) w (c'.1, c'.2 ++ rest) := by
  induction h with
  | refl c => exact Reach.refl _
  | @eps q' p' Z rest' γ' w' c hs _ ih =>
    exact Reach.eps hs (by simpa using ih)
  | @letter q' p' a Z rest' γ' w' c hs _ ih =>
    exact Reach.letter hs (by simpa using ih)

theorem Reach.lift {p q : Fin M.states} {γ st : List (Fin M.stack)} {w : List Bool}
    (h : Reach M (p, γ) w (q, st)) (rest : List (Fin M.stack)) :
    Reach M (p, γ ++ rest) w (q, st ++ rest) :=
  h.lift' rest

/-- A run from stack `γ ++ rest` either stays above `rest` or first empties
`γ` and continues from `rest`. -/
theorem reach_append_cases {p : Fin M.states} {γ rest : List (Fin M.stack)} {w : List Bool}
    {c : M.Config} (h : Reach M (p, γ ++ rest) w c) :
    (∃ st', c.2 = st' ++ rest ∧ Reach M (p, γ) w (c.1, st')) ∨
    (∃ q' w1 w2, w = w1 ++ w2 ∧ Reach M (p, γ) w1 (q', []) ∧ Reach M (q', rest) w2 c) := by
  generalize hc0 : (p, γ ++ rest) = c0 at h
  induction h generalizing γ p with
  | refl _ =>
    subst hc0
    exact Or.inl ⟨γ, rfl, Reach.refl _⟩
  | @eps q r Z rest' δ w' c hs hrest ih =>
    cases γ with
    | nil =>
      simp only [List.nil_append, Prod.mk.injEq] at hc0
      obtain ⟨rfl, rfl⟩ := hc0
      exact Or.inr ⟨_, [], w', rfl, Reach.refl _, Reach.eps hs hrest⟩
    | cons Y γ'' =>
      simp only [List.cons_append, Prod.mk.injEq, List.cons.injEq] at hc0
      obtain ⟨rfl, rfl, rfl⟩ := hc0
      rcases ih (γ := δ ++ γ'') (p := r) (by rw [List.append_assoc]) with
        ⟨st', hst, hr⟩ | ⟨q', w1, w2, hw, h1, h2⟩
      · exact Or.inl ⟨st', hst, Reach.eps hs hr⟩
      · exact Or.inr ⟨q', w1, w2, hw, Reach.eps hs h1, h2⟩
  | @letter q r a Z rest' δ w' c hs hrest ih =>
    cases γ with
    | nil =>
      simp only [List.nil_append, Prod.mk.injEq] at hc0
      obtain ⟨rfl, rfl⟩ := hc0
      exact Or.inr ⟨_, [], a :: w', rfl, Reach.refl _, Reach.letter hs hrest⟩
    | cons Y γ'' =>
      simp only [List.cons_append, Prod.mk.injEq, List.cons.injEq] at hc0
      obtain ⟨rfl, rfl, rfl⟩ := hc0
      rcases ih (γ := δ ++ γ'') (p := r) (by rw [List.append_assoc]) with
        ⟨st', hst, hr⟩ | ⟨q', w1, w2, hw, h1, h2⟩
      · exact Or.inl ⟨st', hst, Reach.letter hs hr⟩
      · exact Or.inr ⟨q', a :: w1, w2, by rw [hw]; rfl, Reach.letter hs h1, h2⟩

/-! ## Determinism -/

/-- A letter move excludes an epsilon move at the same state and top symbol. -/
theorem step_none_eq_none_of_letter {q : Fin M.states} {a : Bool} {Z : Fin M.stack}
    {r : Fin M.states × List (Fin M.stack)} (h : M.step q (some a) Z = some r) :
    M.step q none Z = none := by
  by_contra hne
  have hsome : (M.step q none Z).isSome = true := by
    cases hZ : M.step q none Z with
    | none => exact absurd hZ hne
    | some _ => rfl
  have := M.det q Z hsome a
  rw [this] at h
  cases h

/-- Runs from the same configuration on prefix-comparable input words
are ordered by continuation, with a possible epsilon extension in the
reverse direction when the consumed words coincide. -/
theorem reach_linear {c c1 c2 : M.Config} {w1 v : List Bool}
    (h1 : Reach M c w1 c1) (h2 : Reach M c (w1 ++ v) c2) :
    Reach M c1 v c2 ∨ (v = [] ∧ Reach M c2 [] c1) := by
  induction h1 generalizing c2 with
  | refl _ => left; simpa using h2
  | @eps q p Z rest γ w c' hs hrest ih =>
    generalize hu : w ++ v = u at h2
    cases h2 with
    | refl _ =>
      right
      obtain ⟨hw, hv⟩ := List.append_eq_nil_iff.1 hu
      subst hw hv
      exact ⟨rfl, Reach.eps hs hrest⟩
    | eps hs' hrest' =>
      subst hu
      rw [hs] at hs'
      cases hs'
      exact ih hrest'
    | letter hs' _ =>
      rw [step_none_eq_none_of_letter hs'] at hs
      cases hs
  | @letter q p a Z rest γ w c' hs _ ih =>
    cases h2 with
    | eps hs' _ =>
      rw [step_none_eq_none_of_letter hs] at hs'
      cases hs'
    | letter hs' hrest =>
      rw [hs] at hs'
      cases hs'
      exact ih hrest

/-! ## The epsilon chain -/

/-- The unique epsilon move from a configuration, if any. -/
def epsStep (M : DPDA) : M.Config → Option M.Config
  | (_, []) => none
  | (q, Z :: rest) => (M.step q none Z).map fun r => (r.1, r.2 ++ rest)

/-- The `k`-th configuration of the epsilon chain. -/
def epsIter (M : DPDA) : ℕ → M.Config → Option M.Config
  | 0, c => some c
  | k + 1, c => (M.epsStep c).bind (M.epsIter k)

@[simp] theorem epsIter_zero (c : M.Config) : M.epsIter 0 c = some c := rfl

theorem epsIter_succ (k : ℕ) (c : M.Config) :
    M.epsIter (k + 1) c = (M.epsStep c).bind (M.epsIter k) := rfl

theorem epsIter_succ' (k : ℕ) (c : M.Config) :
    M.epsIter (k + 1) c = (M.epsIter k c).bind M.epsStep := by
  induction k generalizing c with
  | zero =>
    show (M.epsStep c).bind (M.epsIter 0) = M.epsStep c
    cases M.epsStep c <;> rfl
  | succ k ih =>
    rw [epsIter_succ, epsIter_succ]
    cases M.epsStep c with
    | none => rfl
    | some c' => exact ih c'

theorem epsStep_eq_some_iff {c c' : M.Config} :
    M.epsStep c = some c' ↔
      ∃ q Z rest r γ, c = (q, Z :: rest) ∧ M.step q none Z = some (r, γ) ∧ c' = (r, γ ++ rest) := by
  obtain ⟨q, st⟩ := c
  cases st with
  | nil => simp [epsStep]
  | cons Z rest =>
    simp only [epsStep, Option.map_eq_some_iff, Prod.mk.injEq, List.cons.injEq]
    constructor
    · rintro ⟨⟨r, γ⟩, hs, rfl⟩
      exact ⟨q, Z, rest, r, γ, ⟨rfl, rfl, rfl⟩, hs, rfl⟩
    · rintro ⟨q', Z', rest', r, γ, ⟨rfl, rfl, rfl⟩, hs, rfl⟩
      exact ⟨(r, γ), hs, rfl⟩

/-- Epsilon-only runs follow the epsilon chain. -/
theorem reach_nil_iff {c c' : M.Config} :
    Reach M c [] c' ↔ ∃ k, M.epsIter k c = some c' := by
  constructor
  · intro h
    generalize hw : ([] : List Bool) = w at h
    induction h with
    | refl _ => exact ⟨0, rfl⟩
    | @eps q p Z rest γ w c hs _ ih =>
      obtain ⟨k, hk⟩ := ih hw
      refine ⟨k + 1, ?_⟩
      rw [epsIter_succ]
      simp [epsStep, hs, hk]
    | letter _ _ _ => cases hw
  · rintro ⟨k, hk⟩
    induction k generalizing c with
    | zero => cases hk; exact Reach.refl _
    | succ k ih =>
      rw [epsIter_succ] at hk
      cases hc : M.epsStep c with
      | none => rw [hc] at hk; cases hk
      | some c'' =>
        rw [hc] at hk
        obtain ⟨q, Z, rest, r, γ, rfl, hs, rfl⟩ := epsStep_eq_some_iff.1 hc
        exact Reach.eps hs (ih hk)

theorem epsIter_add (j k : ℕ) (c : M.Config) :
    M.epsIter (j + k) c = (M.epsIter j c).bind (M.epsIter k) := by
  induction k with
  | zero => cases M.epsIter j c <;> rfl
  | succ k ih =>
    rw [← Nat.add_assoc, epsIter_succ', ih]
    cases M.epsIter j c with
    | none => rfl
    | some c' => exact (epsIter_succ' k c').symm

theorem epsIter_none_of_le {j k : ℕ} {c : M.Config} (h : M.epsIter j c = none) (hjk : j ≤ k) :
    M.epsIter k c = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [epsIter_add, h]
  rfl

theorem epsIter_some_of_le {j k : ℕ} {c c' : M.Config} (h : M.epsIter k c = some c')
    (hjk : j ≤ k) : ∃ c'', M.epsIter j c = some c'' := by
  cases hj : M.epsIter j c with
  | none => rw [epsIter_none_of_le hj hjk] at h; cases h
  | some c'' => exact ⟨c'', rfl⟩

/-- An epsilon move lifts to a longer stack. -/
theorem epsStep_lift {c c' : M.Config} (h : M.epsStep c = some c') (rest : List (Fin M.stack)) :
    M.epsStep (c.1, c.2 ++ rest) = some (c'.1, c'.2 ++ rest) := by
  obtain ⟨q, Z, rest', r, γ, rfl, hs, rfl⟩ := epsStep_eq_some_iff.1 h
  simp [epsStep, hs, List.append_assoc]

/-- The epsilon chain lifts to a longer stack as long as it runs. -/
theorem epsIter_lift {k : ℕ} {c c' : M.Config} (h : M.epsIter k c = some c')
    (rest : List (Fin M.stack)) :
    M.epsIter k (c.1, c.2 ++ rest) = some (c'.1, c'.2 ++ rest) := by
  induction k generalizing c' with
  | zero => cases h; rfl
  | succ k ih =>
    rw [epsIter_succ'] at h ⊢
    cases hk : M.epsIter k c with
    | none => rw [hk] at h; cases h
    | some c'' =>
      rw [hk] at h
      rw [ih hk]
      exact epsStep_lift h rest

theorem epsIter_none_of_lift {k : ℕ} {c : M.Config} {rest : List (Fin M.stack)}
    (h : M.epsIter k (c.1, c.2 ++ rest) = none) : M.epsIter k c = none := by
  cases hk : M.epsIter k c with
  | none => rfl
  | some c' => rw [epsIter_lift hk rest] at h; cases h

/-- The epsilon chain from `c` never ends. -/
def Loops (M : DPDA) (c : M.Config) : Prop := ∀ k, (M.epsIter k c).isSome = true

theorem not_loops_iff {c : M.Config} : ¬ M.Loops c ↔ ∃ k, M.epsIter k c = none := by
  simp only [Loops, not_forall, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]

/-- The letter move from a configuration on letter `b`, if any. -/
def letterStep (M : DPDA) (b : Bool) : M.Config → Option M.Config
  | (_, []) => none
  | (q, Z :: rest) => (M.step q (some b) Z).map fun r => (r.1, r.2 ++ rest)

theorem letterStep_eq_some_iff {b : Bool} {c c' : M.Config} :
    M.letterStep b c = some c' ↔
      ∃ q Z rest r γ, c = (q, Z :: rest) ∧ M.step q (some b) Z = some (r, γ) ∧
        c' = (r, γ ++ rest) := by
  obtain ⟨q, st⟩ := c
  cases st with
  | nil => simp [letterStep]
  | cons Z rest =>
    simp only [letterStep, Option.map_eq_some_iff, Prod.mk.injEq, List.cons.injEq]
    constructor
    · rintro ⟨⟨r, γ⟩, hs, rfl⟩
      exact ⟨q, Z, rest, r, γ, ⟨rfl, rfl, rfl⟩, hs, rfl⟩
    · rintro ⟨q', Z', rest', r, γ, ⟨rfl, rfl, rfl⟩, hs, rfl⟩
      exact ⟨(r, γ), hs, rfl⟩

/-- A letter move is only available where the epsilon chain ends. -/
theorem epsStep_eq_none_of_letterStep {b : Bool} {c c' : M.Config}
    (h : M.letterStep b c = some c') : M.epsStep c = none := by
  obtain ⟨q, Z, rest, r, γ, rfl, hs, rfl⟩ := letterStep_eq_some_iff.1 h
  simp [epsStep, step_none_eq_none_of_letter hs]

/-- A run consuming `b :: w` follows the epsilon chain to its end, takes the
letter move, and continues. -/
theorem reach_cons_iff {c c' : M.Config} {b : Bool} {w : List Bool} :
    Reach M c (b :: w) c' ↔
      ∃ k c₁ c₂, M.epsIter k c = some c₁ ∧ M.letterStep b c₁ = some c₂ ∧ Reach M c₂ w c' := by
  constructor
  · intro h
    generalize hw : b :: w = w' at h
    induction h with
    | refl _ => cases hw
    | @eps q p Z rest γ w'' c hs _ ih =>
      obtain ⟨k, c₁, c₂, hk, hl, hr⟩ := ih hw
      refine ⟨k + 1, c₁, c₂, ?_, hl, hr⟩
      rw [epsIter_succ]
      simp [epsStep, hs, hk]
    | @letter q p a Z rest γ w'' c hs hrest _ =>
      cases hw
      exact ⟨0, (q, Z :: rest), (p, γ ++ rest), rfl, by simp [letterStep, hs], hrest⟩
  · rintro ⟨k, c₁, c₂, hk, hl, hr⟩
    have h1 : Reach M c [] c₁ := reach_nil_iff.2 ⟨k, hk⟩
    obtain ⟨q, Z, rest, r, γ, rfl, hs, rfl⟩ := letterStep_eq_some_iff.1 hl
    have h2 : Reach M (q, Z :: rest) (b :: w) c' := Reach.letter hs hr
    simpa using h1.trans h2

/-! ## Acceptance and popping -/

/-- Acceptance from configuration `c` on the word `w`. -/
def Acc (M : DPDA) (c : M.Config) (w : List Bool) : Prop :=
  ∃ c', Reach M c w c' ∧ M.accept c'.1 = true

/-- A run from `c` that consumes `w` and ends in state `q` with an empty stack. -/
def Pops (M : DPDA) (c : M.Config) (w : List Bool) (q : Fin M.states) : Prop :=
  Reach M c w (q, [])

theorem mem_language_iff_acc (w : List Bool) :
    w ∈ M.language ↔ M.Acc (M.start, [M.bottom]) w := Iff.rfl

/-- Two popping runs on prefix-comparable words consume the same word
and end in the same state. -/
theorem pops_unique {c : M.Config} {w1 w2 : List Bool} {q1 q2 : Fin M.states}
    (h1 : M.Pops c w1 q1) (h2 : M.Pops c w2 q2) (hpre : w1 <+: w2) : w1 = w2 ∧ q1 = q2 := by
  obtain ⟨v, rfl⟩ := hpre
  rcases reach_linear h1 h2 with h | ⟨hv, h⟩
  · obtain ⟨hv, hc⟩ := reach_nil_stack h
    subst hv
    simp only [List.append_nil, true_and]
    exact (Prod.mk.injEq _ _ _ _ ▸ hc).1.symm
  · subst hv
    obtain ⟨-, hc⟩ := reach_nil_stack h
    simp only [List.append_nil, true_and]
    exact (Prod.mk.injEq _ _ _ _ ▸ hc).1

/-! ## Runs from one stack symbol -/

/-- With an epsilon move available at `(p, Y)`, the runs from `(p, [Y])` are
the trivial run and the runs from the successor. -/
theorem reach_single_eps_iff {p r : Fin M.states} {Y : Fin M.stack} {δ : List (Fin M.stack)}
    (hs : M.step p none Y = some (r, δ)) {w : List Bool} {c : M.Config} :
    Reach M (p, [Y]) w c ↔ (w = [] ∧ c = (p, [Y])) ∨ Reach M (r, δ) w c := by
  constructor
  · intro h
    cases h with
    | refl _ => exact Or.inl ⟨rfl, rfl⟩
    | eps hs' hrest =>
      rw [hs] at hs'
      cases hs'
      exact Or.inr (by simpa using hrest)
    | letter hs' _ =>
      rw [step_none_eq_none_of_letter hs'] at hs
      cases hs
  · rintro (⟨rfl, rfl⟩ | h)
    · exact Reach.refl _
    · exact Reach.eps (rest := []) hs (by simpa using h)

/-- Without an epsilon move, the only run on the empty word is trivial. -/
theorem reach_single_nil_iff {p : Fin M.states} {Y : Fin M.stack}
    (hnone : M.step p none Y = none) {c : M.Config} :
    Reach M (p, [Y]) [] c ↔ c = (p, [Y]) := by
  constructor
  · intro h
    cases h with
    | refl _ => rfl
    | eps hs _ => rw [hnone] at hs; cases hs
  · rintro rfl
    exact Reach.refl _

/-- Without an epsilon move, a run on `b :: w` takes the letter move on `b`. -/
theorem reach_single_letter_iff {p r : Fin M.states} {Y : Fin M.stack} {b : Bool}
    {δ : List (Fin M.stack)} (hnone : M.step p none Y = none)
    (hs : M.step p (some b) Y = some (r, δ)) {w : List Bool} {c : M.Config} :
    Reach M (p, [Y]) (b :: w) c ↔ Reach M (r, δ) w c := by
  constructor
  · intro h
    cases h with
    | eps hs' _ => rw [hnone] at hs'; cases hs'
    | letter hs' hrest =>
      rw [hs] at hs'
      cases hs'
      simpa using hrest
  · intro h
    exact Reach.letter (rest := []) hs (by simpa using h)

/-- Without an epsilon move and without a letter move on `b`, no run reads `b`. -/
theorem not_reach_single_stuck {p : Fin M.states} {Y : Fin M.stack} {b : Bool}
    (hnone : M.step p none Y = none) (hb : M.step p (some b) Y = none) {w : List Bool}
    {c : M.Config} : ¬ Reach M (p, [Y]) (b :: w) c := by
  intro h
  cases h with
  | eps hs _ => rw [hnone] at hs; cases hs
  | letter hs _ => rw [hb] at hs; cases hs

/-- The converse of `reach_append_cases`. -/
theorem reach_append_iff {p : Fin M.states} {γ rest : List (Fin M.stack)} {w : List Bool}
    {c : M.Config} :
    Reach M (p, γ ++ rest) w c ↔
      (∃ st', c.2 = st' ++ rest ∧ Reach M (p, γ) w (c.1, st')) ∨
      (∃ q' w1 w2, w = w1 ++ w2 ∧ Reach M (p, γ) w1 (q', []) ∧ Reach M (q', rest) w2 c) := by
  constructor
  · exact reach_append_cases
  · rintro (⟨st', hst, h⟩ | ⟨q', w1, w2, rfl, h1, h2⟩)
    · have := h.lift rest
      rw [← hst] at this
      exact this
    · exact (h1.lift rest).trans h2

/-- A configuration that loops on epsilon moves never reads a letter. -/
theorem not_reach_cons_of_loops {c : M.Config} (hl : M.Loops c) {b : Bool} {w : List Bool}
    {c' : M.Config} : ¬ Reach M c (b :: w) c' := by
  intro h
  obtain ⟨k, c₁, c₂, hk, hl', _⟩ := reach_cons_iff.1 h
  have h1 : M.epsIter (k + 1) c = none := by
    rw [epsIter_succ', hk]
    simpa using epsStep_eq_none_of_letterStep hl'
  have := hl (k + 1)
  rw [h1] at this
  cases this

/-- A configuration that loops on epsilon moves never empties its stack. -/
theorem not_reach_nil_stack_of_loops {c : M.Config} (hl : M.Loops c) {w : List Bool}
    {q : Fin M.states} : ¬ Reach M c w (q, []) := by
  intro h
  cases w with
  | cons b w => exact not_reach_cons_of_loops hl h
  | nil =>
    obtain ⟨k, hk⟩ := reach_nil_iff.1 h
    have h1 : M.epsIter (k + 1) c = none := by
      rw [epsIter_succ', hk]
      rfl
    have := hl (k + 1)
    rw [h1] at this
    cases this

end DDNNFNegation.Pushdown.DPDA
