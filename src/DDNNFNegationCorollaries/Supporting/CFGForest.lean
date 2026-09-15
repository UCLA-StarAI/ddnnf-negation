import Mathlib

/-!
# Forest semantics for context-free grammars

A derivation forest generates a terminal word from a list of grammar
symbols. The inductive definition combines terminal steps and production
expansions. The equivalence with the grammar's ordinary derivation
relation supports the fixed-length parsing construction in later modules.
-/

namespace ContextFreeGrammar

variable {T : Type} (g : ContextFreeGrammar T)

/-- Bottom-up derivation of a terminal word from a symbol string. -/
inductive Forest : List (Symbol T g.NT) → List T → Prop
  | nil : Forest [] []
  | terminal {t : T} {s : List (Symbol T g.NT)} {w : List T} (h : Forest s w) :
      Forest (.terminal t :: s) (t :: w)
  | nonterminal {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
      {s : List (Symbol T g.NT)} {w₁ w₂ : List T}
      (h₁ : Forest r.output w₁) (h₂ : Forest s w₂) :
      Forest (.nonterminal r.input :: s) (w₁ ++ w₂)

/-- The words one nonterminal generates. -/
def Gen (X : g.NT) (w : List T) : Prop :=
  g.Forest [.nonterminal X] w

theorem forest_nil_iff {w : List T} : g.Forest [] w ↔ w = [] := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Forest.nil

theorem forest_terminal_cons_iff {t : T} {s : List (Symbol T g.NT)} {w : List T} :
    g.Forest (.terminal t :: s) w ↔ ∃ w', w = t :: w' ∧ g.Forest s w' := by
  constructor
  · intro h
    cases h with
    | terminal h => exact ⟨_, rfl, h⟩
  · rintro ⟨w', rfl, h⟩
    exact Forest.terminal h

theorem gen_iff {X : g.NT} {w : List T} :
    g.Gen X w ↔ ∃ r ∈ g.rules, r.input = X ∧ g.Forest r.output w := by
  constructor
  · intro h
    cases h with
    | nonterminal hr h₁ h₂ =>
      cases h₂
      exact ⟨_, hr, rfl, by simpa using h₁⟩
  · rintro ⟨r, hr, rfl, h⟩
    show g.Forest _ _
    simpa using Forest.nonterminal hr h Forest.nil

theorem forest_nonterminal_cons_iff {X : g.NT} {s : List (Symbol T g.NT)} {w : List T} :
    g.Forest (.nonterminal X :: s) w ↔
      ∃ w₁ w₂, w = w₁ ++ w₂ ∧ g.Gen X w₁ ∧ g.Forest s w₂ := by
  constructor
  · intro h
    cases h with
    | nonterminal hr h₁ h₂ =>
      exact ⟨_, _, rfl, (gen_iff g).2 ⟨_, hr, rfl, h₁⟩, h₂⟩
  · rintro ⟨w₁, w₂, rfl, h₁, h₂⟩
    obtain ⟨r, hr, rfl, h₁'⟩ := (gen_iff g).1 h₁
    exact Forest.nonterminal hr h₁' h₂

theorem forest_append_iff {s₁ s₂ : List (Symbol T g.NT)} {w : List T} :
    g.Forest (s₁ ++ s₂) w ↔
      ∃ w₁ w₂, w = w₁ ++ w₂ ∧ g.Forest s₁ w₁ ∧ g.Forest s₂ w₂ := by
  induction s₁ generalizing w with
  | nil =>
    constructor
    · intro h
      exact ⟨[], w, rfl, Forest.nil, h⟩
    · rintro ⟨w₁, w₂, rfl, h₁, h₂⟩
      rw [forest_nil_iff] at h₁
      subst h₁
      simpa using h₂
  | cons x s₁ ih =>
    cases x with
    | terminal t =>
      simp only [List.cons_append, forest_terminal_cons_iff, ih]
      constructor
      · rintro ⟨w', rfl, w₁, w₂, rfl, h₁, h₂⟩
        exact ⟨t :: w₁, w₂, rfl, ⟨w₁, rfl, h₁⟩, h₂⟩
      · rintro ⟨w₁, w₂, rfl, ⟨w₁', rfl, h₁⟩, h₂⟩
        exact ⟨w₁' ++ w₂, rfl, w₁', w₂, rfl, h₁, h₂⟩
    | nonterminal X =>
      simp only [List.cons_append, forest_nonterminal_cons_iff, ih]
      constructor
      · rintro ⟨u, w', rfl, hu, w₁, w₂, rfl, h₁, h₂⟩
        exact ⟨u ++ w₁, w₂, by rw [List.append_assoc], ⟨u, w₁, rfl, hu, h₁⟩, h₂⟩
      · rintro ⟨w₁, w₂, rfl, ⟨u, w₁', rfl, hu, h₁⟩, h₂⟩
        exact ⟨u, w₁' ++ w₂, by rw [List.append_assoc], hu, w₁', w₂, rfl, h₁, h₂⟩

/-! ## Forests are derivations -/

theorem derives_of_forest {s : List (Symbol T g.NT)} {w : List T} (h : g.Forest s w) :
    g.Derives s (w.map Symbol.terminal) := by
  induction h with
  | nil => exact Derives.refl _
  | terminal _ ih =>
    simpa using ih.append_left [Symbol.terminal _]
  | @nonterminal r hr s w₁ w₂ _ _ ih₁ ih₂ =>
    have hstep : g.Produces (.nonterminal r.input :: s) (r.output ++ s) :=
      ⟨r, hr, ContextFreeRule.Rewrites.head s⟩
    refine hstep.trans_derives ?_
    rw [List.map_append]
    exact (ih₁.append_right s).trans (ih₂.append_left _)

private theorem terminals_forest (w : List T) : g.Forest (w.map Symbol.terminal) w := by
  induction w with
  | nil => exact Forest.nil
  | cons t w ih => exact Forest.terminal ih

private theorem forest_of_rule_head {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
    (s : List (Symbol T g.NT)) {w : List T} (h : g.Forest (r.output ++ s) w) :
    g.Forest (.nonterminal r.input :: s) w := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := (forest_append_iff g).1 h
  exact Forest.nonterminal hr h₁ h₂

private theorem forest_of_rewrites {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
    {u v : List (Symbol T g.NT)} (hrw : r.Rewrites u v) {w : List T} (h : g.Forest v w) :
    g.Forest u w := by
  induction hrw generalizing w with
  | head s => exact forest_of_rule_head g hr s h
  | cons x _ ih =>
    cases x with
    | terminal t =>
      obtain ⟨w', rfl, h'⟩ := (forest_terminal_cons_iff g).1 h
      exact Forest.terminal (ih h')
    | nonterminal X =>
      obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := (forest_nonterminal_cons_iff g).1 h
      exact (forest_nonterminal_cons_iff g).2 ⟨w₁, w₂, rfl, h₁, ih h₂⟩

theorem forest_of_derives {s : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives s (w.map Symbol.terminal)) : g.Forest s w := by
  refine Relation.ReflTransGen.head_induction_on h (terminals_forest g w) ?_
  intro u v hstep _ ih
  obtain ⟨r, hr, hrw⟩ := hstep
  exact forest_of_rewrites g hr hrw ih

theorem derives_iff_forest {s : List (Symbol T g.NT)} {w : List T} :
    g.Derives s (w.map Symbol.terminal) ↔ g.Forest s w :=
  ⟨forest_of_derives g, derives_of_forest g⟩

theorem mem_language_iff_gen (w : List T) : w ∈ g.language ↔ g.Gen g.initial w := by
  rw [mem_language_iff, derives_iff_forest]
  rfl

end ContextFreeGrammar
