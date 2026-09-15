import DDNNFNegationConsequences.FiniteLanguageSeparation

/-!
# One-way deterministic pushdown automata

The model has input-consuming and epsilon transitions and accepts by final
state. Determinism excludes competing transitions and excludes an input
transition when an epsilon transition is available. Description size counts
states, input and stack alphabets, transitions, and pushed symbols, following
the convention used in the paper's comparison with Schmidt's question.

`PushdownRuns.lean` develops the run semantics.
`PushdownComplementGrammar.lean` constructs a grammar for the complement.
The finite-automaton embedding gives concrete examples of the model.
-/

namespace DDNNFNegation

open Filter
open CFGBinarization

namespace Pushdown

/-- A deterministic pushdown automaton over the alphabet `Bool`.

`step q a Z = some (p, γ)` means: in state `q`, with `Z` the top stack symbol,
reading the letter `a` (or making an epsilon move, when `a = none`), go to
state `p` and replace `Z` by the string `γ`, whose head becomes the new top
symbol.  `step q a Z = none` means the move is undefined.  A configuration
with an empty stack has no moves, so the machine halts there. -/
structure DPDA where
  /-- Number of states. -/
  states : ℕ
  /-- Number of stack symbols. -/
  stack : ℕ
  /-- The partial transition function. -/
  step : Fin states → Option Bool → Fin stack →
    Option (Fin states × List (Fin stack))
  /-- Initial state. -/
  start : Fin states
  /-- Initial (bottom) stack symbol. -/
  bottom : Fin stack
  /-- Final states. -/
  accept : Fin states → Bool
  /-- Determinism: at a pair carrying an epsilon move there is no letter move. -/
  det : ∀ (q : Fin states) (Z : Fin stack),
    (step q none Z).isSome = true → ∀ a : Bool, step q (some a) Z = none

namespace DPDA

/-- A configuration: the current state and the stack, top symbol first. -/
abbrev Config (M : DPDA) : Type := Fin M.states × List (Fin M.stack)

/-- `Reach M c w c'` holds when the machine can pass from configuration `c`
to configuration `c'` consuming exactly the word `w`.  Epsilon moves consume
no letter, and the relation is reflexive, so a run may be stopped at any
configuration it passes through. -/
inductive Reach (M : DPDA) : M.Config → List Bool → M.Config → Prop
  | refl (c : M.Config) : Reach M c [] c
  | eps {q p : Fin M.states} {Z : Fin M.stack}
      {rest γ : List (Fin M.stack)} {w : List Bool} {c : M.Config} :
      M.step q none Z = some (p, γ) →
      Reach M (p, γ ++ rest) w c →
      Reach M (q, Z :: rest) w c
  | letter {q p : Fin M.states} {a : Bool} {Z : Fin M.stack}
      {rest γ : List (Fin M.stack)} {w : List Bool} {c : M.Config} :
      M.step q (some a) Z = some (p, γ) →
      Reach M (p, γ ++ rest) w c →
      Reach M (q, Z :: rest) (a :: w) c

/-- Acceptance by final state after consuming the entire input.
Epsilon moves after the last letter are allowed. -/
def language (M : DPDA) : Set (List Bool) :=
  {w | ∃ c : M.Config, Reach M (M.start, [M.bottom]) w c ∧ M.accept c.1 = true}

@[simp] theorem mem_language {M : DPDA} {w : List Bool} :
    w ∈ M.language ↔
      ∃ c : M.Config, Reach M (M.start, [M.bottom]) w c ∧ M.accept c.1 = true :=
  Iff.rfl

/-- The number of defined transitions. -/
def transitionCount (M : DPDA) : ℕ :=
  ∑ q : Fin M.states, ∑ a : Option Bool, ∑ Z : Fin M.stack,
    if (M.step q a Z).isSome = true then 1 else 0

/-- The total length of the strings the transitions push. -/
def pushLength (M : DPDA) : ℕ :=
  ∑ q : Fin M.states, ∑ a : Option Bool, ∑ Z : Fin M.stack,
    ((M.step q a Z).map fun r => r.2.length).getD 0

/-- Description size: states, two input letters, stack symbols, transitions, and the total pushed length. -/
def size (M : DPDA) : ℕ :=
  M.states + 2 + M.stack + M.transitionCount + M.pushLength

theorem states_le_size (M : DPDA) : M.states ≤ M.size := by
  unfold size; omega

end DPDA

/-! ## The DPDA lower-bound scale -/

/-- The ninth root of the grammar bound, halved: the explicit
`exp (Omega (n ^ 2))` function that bounds the size of a deterministic
pushdown automaton itself rather than its ninth power. -/
noncomputable def dpdaSizeExponentialLower (n : ℕ) : ℝ :=
  Real.exp ((Real.log (gateQuasipolynomialPrefactor / 6) +
    gateSeparationRate * (n : ℝ) ^ 2) / 81) / 2

theorem dpdaSizeExponentialLower_pos (n : ℕ) :
    0 < dpdaSizeExponentialLower n := by
  unfold dpdaSizeExponentialLower
  positivity

theorem dpdaSizeExponentialLower_pow_nine (n : ℕ) :
    dpdaSizeExponentialLower n ^ 9 =
      cfgDescriptionExponentialLower n / 512 := by
  unfold dpdaSizeExponentialLower cfgDescriptionExponentialLower
  rw [div_pow, ← Real.exp_nat_mul]
  have hexp : ((9 : ℕ) : ℝ) *
      ((Real.log (gateQuasipolynomialPrefactor / 6) +
        gateSeparationRate * (n : ℝ) ^ 2) / 81) =
      (Real.log (gateQuasipolynomialPrefactor / 6) +
        gateSeparationRate * (n : ℝ) ^ 2) / 9 := by
    push_cast
    ring
  rw [hexp]
  norm_num

/-- Taking the ninth root of the bound the chain produces. -/
theorem dpdaSizeExponentialLower_le_of_ninth_power (n s : ℕ)
    (h : cfgDescriptionExponentialLower n / 2 ≤ ((s ^ 9 : ℕ) : ℝ)) :
    dpdaSizeExponentialLower n ≤ (s : ℝ) := by
  have hcast : ((s ^ 9 : ℕ) : ℝ) = (s : ℝ) ^ 9 := by push_cast; ring
  have hpos := cfgDescriptionExponentialLower_pos n
  have hle : dpdaSizeExponentialLower n ^ 9 ≤ (s : ℝ) ^ 9 := by
    rw [dpdaSizeExponentialLower_pow_nine, ← hcast]
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hle

/-! ## Finite automata as examples -/

namespace DPDA

/-- The state a deterministic finite automaton is in after reading a word. -/
def dfaRun {n : ℕ} (tr : Fin n → Bool → Fin n) : Fin n → List Bool → Fin n
  | q, [] => q
  | q, a :: w => dfaRun tr (tr q a) w

@[simp] theorem dfaRun_nil {n : ℕ} (tr : Fin n → Bool → Fin n) (q : Fin n) :
    dfaRun tr q [] = q := rfl

@[simp] theorem dfaRun_cons {n : ℕ} (tr : Fin n → Bool → Fin n) (q : Fin n)
    (a : Bool) (w : List Bool) :
    dfaRun tr q (a :: w) = dfaRun tr (tr q a) w := rfl

/-- A machine that never touches its stack: no epsilon move anywhere, and
every letter move replaces the top symbol by itself.  Such a machine reaches
exactly one configuration per word, the one its finite control reaches. -/
theorem reach_stackless {M : DPDA} (tr : Fin M.states → Bool → Fin M.states)
    (hstep : ∀ q a Z, M.step q (some a) Z = some (tr q a, [Z]))
    (heps : ∀ q Z, M.step q none Z = none)
    (q : Fin M.states) (Z : Fin M.stack) (w : List Bool) (c : M.Config) :
    Reach M (q, [Z]) w c ↔ c = (dfaRun tr q w, [Z]) := by
  induction w generalizing q c with
  | nil =>
    constructor
    · intro h
      cases h with
      | refl _ => rfl
      | eps hs _ =>
        rw [heps q Z] at hs
        exact absurd hs (by simp)
    · rintro rfl
      exact Reach.refl _
  | cons a w ih =>
    constructor
    · intro h
      cases h with
      | eps hs _ =>
        rw [heps q Z] at hs
        exact absurd hs (by simp)
      | letter hs hrest =>
        rw [hstep q a Z] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hp, hg⟩ := hs
        subst hp; subst hg
        rw [List.append_nil] at hrest
        exact (ih (tr q a) c).1 hrest
    · rintro rfl
      refine Reach.letter (Z := Z) (rest := []) (γ := [Z]) (hstep q a Z) ?_
      rw [List.append_nil]
      exact (ih (tr q a) _).2 rfl

/-- The language of a stackless machine is the language of its finite
control.  Every language decided by a deterministic finite automaton is
therefore the language of some `DPDA`. -/
theorem language_stackless {M : DPDA} (tr : Fin M.states → Bool → Fin M.states)
    (hstep : ∀ q a Z, M.step q (some a) Z = some (tr q a, [Z]))
    (heps : ∀ q Z, M.step q none Z = none) :
    M.language = {w : List Bool | M.accept (dfaRun tr M.start w) = true} := by
  ext w
  constructor
  · rintro ⟨c, hc, hacc⟩
    rw [reach_stackless tr hstep heps M.start M.bottom w c] at hc
    subst hc
    exact hacc
  · intro h
    exact ⟨(dfaRun tr M.start w, [M.bottom]),
      (reach_stackless tr hstep heps M.start M.bottom w _).2 rfl, h⟩

/-- A deterministic finite automaton seen as a pushdown automaton: one stack
symbol, no epsilon moves, every move replacing the top symbol by itself. -/
def ofDFA (n : ℕ) (tr : Fin n → Bool → Fin n) (s : Fin n)
    (acc : Fin n → Bool) : DPDA where
  states := n
  stack := 1
  step q a Z := a.map fun b => (tr q b, [Z])
  start := s
  bottom := 0
  accept := acc
  det := by intro q Z hq a; simp at hq

/-- A concrete two-state machine, accepting exactly the words whose last
letter is `true`. -/
def endsInTrue : DPDA :=
  ofDFA 2 (fun _ b => if b then 1 else 0) 0 (fun q => q == 1)

/-- Its finite control, at the state type of the machine. -/
def endsInTrueTr : Fin endsInTrue.states → Bool → Fin endsInTrue.states :=
  fun _ b => if b then (1 : Fin 2) else (0 : Fin 2)

/-- Its language, computed. -/
theorem language_endsInTrue :
    endsInTrue.language =
      {w : List Bool |
        endsInTrue.accept (dfaRun endsInTrueTr endsInTrue.start w) = true} :=
  language_stackless (M := endsInTrue) endsInTrueTr
    (fun _ _ _ => rfl) (fun _ _ => rfl)

/-- The empty word is rejected. -/
theorem nil_not_mem_endsInTrue : [] ∉ endsInTrue.language := by
  rw [language_endsInTrue]; decide

/-- A one-letter word is accepted, so the language is not empty. -/
theorem true_mem_endsInTrue : [true] ∈ endsInTrue.language := by
  rw [language_endsInTrue]; decide

/-- The example rejects the one-letter word `false`. -/
theorem false_not_mem_endsInTrue : [false] ∉ endsInTrue.language := by
  rw [language_endsInTrue]; decide

end DPDA

end Pushdown

end DDNNFNegation
