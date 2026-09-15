import DDNNFNegation.Circuit

/-!
# Tests for the proof-side circuit model

Concrete examples test semantics, sharing, decomposability, and determinism
in `Circuit.lean`. General lemmas check acyclicity and uniqueness of the
computed function. A canonical DNF construction shows that the model can
represent every Boolean function; an automaton construction exercises
sharing on larger examples. The concrete array-indexed trust boundary is
tested separately in `TrustBoundaryTests.lean`.
-/

namespace DDNNFNegation

namespace CircuitTests

open NNFCircuit

/-! ## 1. Small circuits on two variables -/

/-- `x₀ ∧ x₁`, a tree with three gates. -/
def andCircuit : NNFCircuit (Fin 2) where
  Gate := Fin 3
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := 2
  node := fun g ↦ if g = 0 then .pos 0 else if g = 1 then .pos 1 else .conj 0 1
  rank := fun g ↦ if g = 2 then 1 else 0
  child_rank := by
    intro gate child h
    fin_cases gate <;> fin_cases child <;> simp_all [NNFNode.IsChild]
  semantics := fun g v ↦
    if g = 0 then v 0 = true else if g = 1 then v 1 = true
    else v 0 = true ∧ v 1 = true
  semantics_eq := by
    intro gate v
    fin_cases gate <;> simp [NNFNode.Holds]
  support := fun g ↦ if g = 0 then {0} else if g = 1 then {1} else {0, 1}
  support_eq := by
    intro gate
    fin_cases gate <;> simp [NNFNode.Support]

example : andCircuit.size = 3 := rfl

example : andCircuit.Computes (fun v ↦ v 0 = true ∧ v 1 = true) :=
  fun _ ↦ Iff.rfl

/-- The two conjuncts mention different variables, so the conjunction is
decomposable, and with no disjunction it is vacuously deterministic. -/
example : andCircuit.IsDeterministicDNNF := by
  constructor
  · intro gate left right h
    fin_cases gate
    · simp [andCircuit] at h
    · simp [andCircuit] at h
    · simp [andCircuit] at h
      injection h with hl hr
      subst hl hr
      simp [andCircuit]
  · intro gate children h
    fin_cases gate <;> simp_all [andCircuit]

/-- `x₀ ∧ ¬x₀`: both conjuncts mention `x₀`, so decomposability fails. -/
def clashCircuit : NNFCircuit (Fin 2) where
  Gate := Fin 3
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := 2
  node := fun g ↦ if g = 0 then .pos 0 else if g = 1 then .neg 0 else .conj 0 1
  rank := fun g ↦ if g = 2 then 1 else 0
  child_rank := by
    intro gate child h
    fin_cases gate <;> fin_cases child <;> simp_all [NNFNode.IsChild]
  semantics := fun g v ↦
    if g = 0 then v 0 = true else if g = 1 then v 0 = false
    else v 0 = true ∧ v 0 = false
  semantics_eq := by
    intro gate v
    fin_cases gate <;> simp [NNFNode.Holds]
  support := fun _ ↦ {0}
  support_eq := by
    intro gate
    fin_cases gate <;> simp [NNFNode.Support]

/-- Rejected: the conjunction is not decomposable, so this is not a DNNF
even though it is a perfectly good NNF circuit computing `False`. -/
example : ¬ clashCircuit.IsDNNF := by
  intro h
  have := h (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) rfl
  simp [clashCircuit] at this

example : clashCircuit.Computes (fun _ ↦ False) := by
  intro v
  simp [clashCircuit]

/-- `x₀ ∨ ¬x₀`, a deterministic disjunction of two literals. -/
def tautologyCircuit : NNFCircuit (Fin 2) where
  Gate := Fin 3
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := 2
  node := fun g ↦ if g = 0 then .pos 0 else if g = 1 then .neg 0 else .disj [0, 1]
  rank := fun g ↦ if g = 2 then 1 else 0
  child_rank := by
    intro gate child h
    fin_cases gate <;> fin_cases child <;> simp_all [NNFNode.IsChild]
  semantics := fun g v ↦
    if g = 0 then v 0 = true else if g = 1 then v 0 = false else True
  semantics_eq := by
    intro gate v
    fin_cases gate <;> simp [NNFNode.Holds]
  support := fun _ ↦ {0}
  support_eq := by
    intro gate
    fin_cases gate <;> simp [NNFNode.Support]

example : tautologyCircuit.Computes (fun _ ↦ True) := fun _ ↦ Iff.rfl

/-- Accepted: the two disjuncts are never true together. -/
example : tautologyCircuit.IsDeterministicDNNF := by
  constructor
  · intro gate left right h
    fin_cases gate <;> simp_all [tautologyCircuit]
  · intro gate children h left hleft right hright hne v
    fin_cases gate
    · simp [tautologyCircuit] at h
    · simp [tautologyCircuit] at h
    · simp only [tautologyCircuit] at h
      cases h
      fin_cases hleft <;> fin_cases hright <;>
        simp_all [tautologyCircuit]

/-- `x₀ ∨ x₁`, a disjunction whose disjuncts overlap. -/
def orCircuit : NNFCircuit (Fin 2) where
  Gate := Fin 3
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := 2
  node := fun g ↦ if g = 0 then .pos 0 else if g = 1 then .pos 1 else .disj [0, 1]
  rank := fun g ↦ if g = 2 then 1 else 0
  child_rank := by
    intro gate child h
    fin_cases gate <;> fin_cases child <;> simp_all [NNFNode.IsChild]
  semantics := fun g v ↦
    if g = 0 then v 0 = true else if g = 1 then v 1 = true
    else v 0 = true ∨ v 1 = true
  semantics_eq := by
    intro gate v
    fin_cases gate <;> simp [NNFNode.Holds]
  support := fun g ↦ if g = 0 then {0} else if g = 1 then {1} else {0, 1}
  support_eq := by
    intro gate
    fin_cases gate <;> simp [NNFNode.Support]

/-- Accepted as a DNNF: there is no conjunction to check. -/
example : orCircuit.IsDNNF := by
  intro gate left right h
  fin_cases gate <;> simp_all [orCircuit]

/-- Rejected as deterministic: the assignment setting both variables true
satisfies both disjuncts. -/
example : ¬ orCircuit.IsDeterministic := by
  intro h
  exact h (2 : Fin 3) ([0, 1] : List (Fin 3)) rfl (0 : Fin 3)
    (List.mem_cons_self ..) (1 : Fin 3)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (by decide : (0 : Fin 3) ≠ 1) (fun _ ↦ true) ⟨rfl, rfl⟩

/-- `(x₀ ∧ x₁) ∨ (x₀ ∧ ¬x₁)`, which computes `x₀`.  The literal `x₀` is
one gate with two parents, so the circuit has six gates where the
formula tree has seven. -/
def sharedCircuit : NNFCircuit (Fin 2) where
  Gate := Fin 6
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := 5
  node := fun g ↦
    if g = 0 then .pos 0 else if g = 1 then .pos 1 else if g = 2 then .neg 1
    else if g = 3 then .conj 0 1 else if g = 4 then .conj 0 2 else .disj [3, 4]
  rank := fun g ↦ if g = 5 then 2 else if g = 3 ∨ g = 4 then 1 else 0
  child_rank := by
    intro gate child h
    fin_cases gate <;> fin_cases child <;> simp_all [NNFNode.IsChild]
  semantics := fun g v ↦
    if g = 0 then v 0 = true else if g = 1 then v 1 = true
    else if g = 2 then v 1 = false
    else if g = 3 then v 0 = true ∧ v 1 = true
    else if g = 4 then v 0 = true ∧ v 1 = false
    else (v 0 = true ∧ v 1 = true) ∨ (v 0 = true ∧ v 1 = false)
  semantics_eq := by
    intro gate v
    fin_cases gate <;> simp [NNFNode.Holds]
  support := fun g ↦ if g = 0 then {0} else if g = 1 ∨ g = 2 then {1} else {0, 1}
  support_eq := by
    intro gate
    fin_cases gate <;> simp [NNFNode.Support]

/-- The shared literal is counted once. -/
example : sharedCircuit.size = 6 := rfl

example : sharedCircuit.Computes (fun v ↦ v 0 = true) := by
  intro v
  simp only [sharedCircuit]
  cases v 1 <;> simp

/-- Accepted: every conjunction splits `{x₀}` from `{x₁}`, and the two
disjuncts disagree on `x₁`. -/
example : sharedCircuit.IsDeterministicDNNF := by
  constructor
  · intro gate left right h
    fin_cases gate
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
      injection h with hl hr
      subst hl hr
      simp [sharedCircuit]
    · simp [sharedCircuit] at h
      injection h with hl hr
      subst hl hr
      simp [sharedCircuit]
    · simp [sharedCircuit] at h
  · intro gate children h left hleft right hright hne v
    fin_cases gate
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
    · simp [sharedCircuit] at h
    · simp only [sharedCircuit] at h
      cases h
      fin_cases hleft <;> fin_cases hright <;>
        simp_all [sharedCircuit]

/-- The claim in `Circuit.lean` quantifies circuits over the
countable variable supply `ℕ`.  The model is unchanged there: a circuit
still has finitely many gates and mentions finitely many variables.  The
literal `x₇` as a one-gate circuit over `ℕ`: -/
def natLiteralCircuit : NNFCircuit ℕ where
  Gate := Fin 1
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := 0
  node := fun _ ↦ .pos 7
  rank := fun _ ↦ 0
  child_rank := by
    intro gate child h
    simp [NNFNode.IsChild] at h
  semantics := fun _ v ↦ v 7 = true
  semantics_eq := by
    intro gate v
    simp [NNFNode.Holds]
  support := fun _ ↦ {7}
  support_eq := by
    intro gate
    simp [NNFNode.Support]

example : natLiteralCircuit.IsDeterministicDNNF := by
  constructor
  · intro gate left right h
    simp [natLiteralCircuit] at h
  · intro gate children h
    simp [natLiteralCircuit] at h

example : natLiteralCircuit.Computes fun v ↦ v 7 = true := fun _ ↦ Iff.rfl

example : natLiteralCircuit.size = 1 := rfl

/-! ## 2. General properties of the model -/

/-- No gate is its own child: the rank condition excludes the self-loop
`node g = disj [g]` and every other cycle. -/
theorem not_isChild_self {Var : Type*} [DecidableEq Var]
    (C : NNFCircuit Var) (gate : C.Gate) : ¬ (C.node gate).IsChild gate :=
  fun h ↦ lt_irrefl _ (C.child_rank gate gate h)

/-- A circuit has at least its output gate. -/
theorem one_le_size {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var) :
    1 ≤ C.size :=
  Fintype.card_pos_iff.mpr ⟨C.output⟩

/-- A circuit computes one function, up to pointwise equivalence. -/
theorem computes_unique {Var : Type*} [DecidableEq Var] (C : NNFCircuit Var)
    {f g : (Var → Bool) → Prop} (hf : C.Computes f) (hg : C.Computes g) :
    ∀ v, f v ↔ g v :=
  fun v ↦ (hf v).symm.trans (hg v)

/-- A deterministic DNNF is a DNNF, so the lower bound in the claim applies
to deterministic circuits for the complement in particular. -/
theorem isDNNF_of_isDeterministicDNNF {Var : Type*} [DecidableEq Var]
    (C : NNFCircuit Var) (h : C.IsDeterministicDNNF) : C.IsDNNF :=
  h.1

/-! ## 3. Completeness: every function has a deterministic DNNF

The circuit is the canonical DNF.  For each satisfying assignment `a`
there is a chain of gates `term a k`, one per position `k ≤ m`, where
`term a k` is the conjunction of the literal for variable `k` with
`term a (k + 1)`, and `term a m` is `top`.  The root is the disjunction
of the `term a 0` over all satisfying `a`.  Distinct assignments disagree
somewhere, so the disjunction is deterministic, and each conjunction
splits variable `k` from the variables after it, so it is decomposable. -/

section Completeness

variable {m : ℕ}

/-- Gates of the canonical DNF circuit. -/
inductive DNFGate (m : ℕ) where
  | root
  | term (a : Fin m → Bool) (k : Fin (m + 1))
  | lit (a : Fin m → Bool) (j : Fin m)
  deriving DecidableEq, Fintype

open Classical in
/-- The satisfying assignments of `f`, as a list. -/
noncomputable def satisfying (f : (Fin m → Bool) → Prop) : List (Fin m → Bool) :=
  (Finset.univ.filter f).toList

open Classical in
theorem mem_satisfying (f : (Fin m → Bool) → Prop) (a : Fin m → Bool) :
    a ∈ satisfying f ↔ f a := by
  simp [satisfying]

/-- The variables at positions `k` and later. -/
def tailVars (k : Fin (m + 1)) : Finset (Fin m) :=
  Finset.univ.filter fun j ↦ (k : ℕ) ≤ j

noncomputable def dnfNode (f : (Fin m → Bool) → Prop) :
    DNFGate m → NNFNode (Fin m) (DNFGate m)
  | .root => .disj ((satisfying f).map fun a ↦ .term a 0)
  | .term a k =>
      if h : (k : ℕ) < m then
        .conj (.lit a ⟨k, h⟩) (.term a ⟨k + 1, by omega⟩)
      else .top
  | .lit a j => if a j then .pos j else .neg j

def dnfRank : DNFGate m → ℕ
  | .root => m + 2
  | .term _ k => m - k + 1
  | .lit _ _ => 0

def dnfSemantics (f : (Fin m → Bool) → Prop) :
    DNFGate m → (Fin m → Bool) → Prop
  | .root, v => f v
  | .term a k, v => ∀ j : Fin m, (k : ℕ) ≤ j → v j = a j
  | .lit a j, v => v j = a j

noncomputable def dnfSupport (f : (Fin m → Bool) → Prop) :
    DNFGate m → Finset (Fin m)
  | .root =>
      ((satisfying f).map fun a ↦ DNFGate.term a 0).foldl
        (fun result gate ↦ result ∪
          match gate with
          | .term _ k => tailVars k
          | _ => ∅) ∅
  | .term _ k => tailVars k
  | .lit _ j => {j}

theorem dnf_child_rank (f : (Fin m → Bool) → Prop)
    (gate child : DNFGate m) (h : (dnfNode f gate).IsChild child) :
    dnfRank child < dnfRank gate := by
  cases gate with
  | root =>
      simp only [dnfNode, NNFNode.IsChild] at h
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      simp [dnfRank]
  | term a k =>
      simp only [dnfNode] at h
      split at h
      · rcases h with rfl | rfl
        · simp [dnfRank]
        · simp [dnfRank]
          omega
      · simp [NNFNode.IsChild] at h
  | lit a j =>
      simp only [dnfNode] at h
      split at h <;> simp [NNFNode.IsChild] at h

theorem dnf_semantics_eq (f : (Fin m → Bool) → Prop)
    (gate : DNFGate m) (v : Fin m → Bool) :
    dnfSemantics f gate v ↔
      (dnfNode f gate).Holds v (fun child ↦ dnfSemantics f child v) := by
  cases gate with
  | root =>
      simp only [dnfNode, dnfSemantics, NNFNode.Holds, List.mem_map]
      constructor
      · intro hf
        exact ⟨.term v 0, ⟨v, (mem_satisfying f v).mpr hf, rfl⟩,
          fun _ _ ↦ rfl⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, hva⟩
        have : v = a := funext fun j ↦ hva j (Nat.zero_le _)
        subst this
        exact (mem_satisfying f v).mp ha
  | term a k =>
      simp only [dnfNode, dnfSemantics]
      split
      · rename_i h
        simp only [NNFNode.Holds]
        constructor
        · intro H
          exact ⟨H ⟨k, h⟩ le_rfl, fun j hj ↦ H j (by simp at hj; omega)⟩
        · rintro ⟨H0, H⟩ j hj
          rcases Nat.eq_or_lt_of_le hj with heq | hlt
          · have : j = ⟨k, h⟩ := Fin.ext heq.symm
            subst this
            exact H0
          · exact H j (by simp; omega)
      · rename_i h
        simp only [NNFNode.Holds, iff_true]
        intro j hj
        exact absurd (lt_of_le_of_lt hj j.isLt) h
  | lit a j =>
      simp only [dnfNode, dnfSemantics]
      cases ha : a j <;> simp [NNFNode.Holds]

theorem dnf_support_eq (f : (Fin m → Bool) → Prop) (gate : DNFGate m) :
    dnfSupport f gate = (dnfNode f gate).Support (dnfSupport f) := by
  cases gate with
  | root =>
      simp only [dnfNode, dnfSupport, NNFNode.Support, List.foldl_map]
  | term a k =>
      simp only [dnfNode, dnfSupport]
      split
      · rename_i h
        simp only [NNFNode.Support, dnfSupport]
        ext j
        simp only [tailVars, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_singleton, Fin.ext_iff]
        omega
      · rename_i h
        simp only [NNFNode.Support]
        ext j
        simp only [tailVars, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        intro hj
        exact h (lt_of_le_of_lt hj j.isLt)
  | lit a j =>
      simp only [dnfNode, dnfSupport]
      cases a j <;> simp [NNFNode.Support]

/-- The canonical DNF circuit for `f`. -/
noncomputable def dnfCircuit (f : (Fin m → Bool) → Prop) : NNFCircuit (Fin m) where
  Gate := DNFGate m
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := .root
  node := dnfNode f
  rank := dnfRank
  child_rank := dnf_child_rank f
  semantics := dnfSemantics f
  semantics_eq := dnf_semantics_eq f
  support := dnfSupport f
  support_eq := dnf_support_eq f

theorem dnfCircuit_computes (f : (Fin m → Bool) → Prop) :
    (dnfCircuit f).Computes f :=
  fun _ ↦ Iff.rfl

theorem dnfCircuit_decomposable (f : (Fin m → Bool) → Prop) :
    (dnfCircuit f).IsDecomposable := by
  intro gate left right hnode
  cases gate with
  | root => simp [dnfCircuit, dnfNode] at hnode
  | term a k =>
      simp only [dnfCircuit, dnfNode] at hnode
      split at hnode
      · rename_i h
        injection hnode with hleft hright
        subst hleft hright
        rw [Finset.disjoint_left]
        intro j hj hj'
        simp only [dnfCircuit, dnfSupport, tailVars, Finset.mem_singleton,
          Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff] at hj hj'
        omega
      · simp at hnode
  | lit a j =>
      simp only [dnfCircuit, dnfNode] at hnode
      split at hnode <;> simp at hnode

theorem dnfCircuit_deterministic (f : (Fin m → Bool) → Prop) :
    (dnfCircuit f).IsDeterministic := by
  intro gate children hnode left hleft right hright hne v
  cases gate with
  | root =>
      simp only [dnfCircuit, dnfNode] at hnode
      injection hnode with hchildren
      subst hchildren
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hleft
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hright
      have hab : a ≠ b := fun h ↦ hne (by rw [h])
      rintro ⟨ha, hb⟩
      apply hab
      funext j
      rw [← ha j (Nat.zero_le _), hb j (Nat.zero_le _)]
  | term a k =>
      simp only [dnfCircuit, dnfNode] at hnode
      split at hnode <;> simp at hnode
  | lit a j =>
      simp only [dnfCircuit, dnfNode] at hnode
      split at hnode <;> simp at hnode

/-- Every Boolean function on `Fin m` is represented by a deterministic DNNF in the proof-side model. -/
theorem exists_deterministicDNNF (f : (Fin m → Bool) → Prop) :
    ∃ C : NNFCircuit.{0, 0} (Fin m), C.IsDeterministicDNNF ∧ C.Computes f :=
  ⟨dnfCircuit f, ⟨dnfCircuit_decomposable f, dnfCircuit_deterministic f⟩,
    dnfCircuit_computes f⟩

end Completeness

/-! ## 4. A larger structure with sharing: circuits from finite automata

A deterministic finite automaton over the alphabet `Bool`, reading `n`
input bits, compiles into a layered circuit.  The gate `state s k` says
"after `k` bits the automaton is in state `s`"; `lit b k` is the literal
"bit `k` is `b`"; `conj s b k` is the conjunction of `state s k` and
`lit b k`.  The gate `state s (k + 1)` is the disjunction of `conj s' b k`
over all transitions `step s' b = s`, and the root is the disjunction of
`state s n` over the accepting states `s`.

Sharing is what makes this small.  Each `state s k` gate is a child of
both `conj s false k` and `conj s true k`, and each literal gate `lit b k`
is a child of `conj s b k` for every state `s`.  The circuit has
`1 + |S| (n + 1) + 2n + 2|S| n` gates, linear in `n`; unfolding it into a
formula tree, or writing its language as the canonical DNF,
can cost exponentially many.  The automaton is in exactly one state after
reading `k` bits, and that is what makes every disjunction deterministic.

The construction is the classical compilation of an automaton, or of an
OBDD, into a d-DNNF; it is written here directly against the proof-side model,
with no other project file involved. -/

section Automaton

variable {S : Type} [Fintype S] [DecidableEq S] {n : ℕ}

/-- A deterministic finite automaton reading bits. -/
structure BoolAutomaton (S : Type) where
  start : S
  step : S → Bool → S
  accept : Finset S

namespace BoolAutomaton

/-- The state after reading the first `k` bits of `x`. -/
def run (A : BoolAutomaton S) (x : Fin n → Bool) : ℕ → S
  | 0 => A.start
  | k + 1 => if h : k < n then A.step (A.run x k) (x ⟨k, h⟩) else A.run x k

/-- The language: `x` is accepted when the final state is accepting. -/
def Accepts (A : BoolAutomaton S) (x : Fin n → Bool) : Prop :=
  A.run x n ∈ A.accept

instance (A : BoolAutomaton S) (x : Fin n → Bool) : Decidable (A.Accepts x) :=
  inferInstanceAs (Decidable (A.run x n ∈ A.accept))

/-- The transitions into `s`. -/
noncomputable def preds (A : BoolAutomaton S) (s : S) : List (S × Bool) :=
  (Finset.univ.filter fun p : S × Bool ↦ A.step p.1 p.2 = s).toList

theorem mem_preds (A : BoolAutomaton S) (s : S) (p : S × Bool) :
    p ∈ A.preds s ↔ A.step p.1 p.2 = s := by
  simp [preds]

end BoolAutomaton

/-- Gates of the automaton circuit. -/
inductive AutGate (S : Type) (n : ℕ) where
  | root
  | state (s : S) (k : Fin (n + 1))
  | lit (b : Bool) (k : Fin n)
  | conj (s : S) (b : Bool) (k : Fin n)
  deriving DecidableEq

/-- The gate type, counted. -/
def autGateEquiv (S : Type) (n : ℕ) :
    AutGate S n ≃ Unit ⊕ (S × Fin (n + 1)) ⊕ (Bool × Fin n) ⊕ (S × Bool × Fin n) where
  toFun
    | .root => .inl ()
    | .state s k => .inr (.inl (s, k))
    | .lit b k => .inr (.inr (.inl (b, k)))
    | .conj s b k => .inr (.inr (.inr (s, b, k)))
  invFun
    | .inl () => .root
    | .inr (.inl (s, k)) => .state s k
    | .inr (.inr (.inl (b, k))) => .lit b k
    | .inr (.inr (.inr (s, b, k))) => .conj s b k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟩ | ⟨s, k⟩ | ⟨b, k⟩ | ⟨s, b, k⟩ <;> rfl

instance : Fintype (AutGate S n) := Fintype.ofEquiv _ (autGateEquiv S n).symm

open BoolAutomaton in
noncomputable def autNode (A : BoolAutomaton S) :
    AutGate S n → NNFNode (Fin n) (AutGate S n)
  | .root => .disj (A.accept.toList.map fun s ↦ .state s (Fin.last n))
  | .state s ⟨0, _⟩ => if s = A.start then .top else .bot
  | .state s ⟨j + 1, hj⟩ =>
      .disj ((A.preds s).map fun p ↦ .conj p.1 p.2 ⟨j, by omega⟩)
  | .lit b k => if b then .pos k else .neg k
  | .conj s b k => .conj (.state s k.castSucc) (.lit b k)

def autRank : AutGate S n → ℕ
  | .root => 2 * n + 1
  | .state _ k => 2 * k
  | .lit _ _ => 0
  | .conj _ _ k => 2 * k + 1

def autSemantics (A : BoolAutomaton S) : AutGate S n → (Fin n → Bool) → Prop
  | .root, x => A.Accepts x
  | .state s k, x => A.run x k = s
  | .lit b k, x => x k = b
  | .conj s b k, x => A.run x k = s ∧ x k = b

/-- Bit `k` as a set of variables, empty past the end of the input. -/
def bitVar (k : ℕ) : Finset (Fin n) := if h : k < n then {⟨k, h⟩} else ∅

/-- Syntactic support of `state s k`, by recursion on the layer. -/
noncomputable def stateSupport (A : BoolAutomaton S) : ℕ → S → Finset (Fin n)
  | 0, _ => ∅
  | k + 1, s =>
      (A.preds s).foldl (fun r p ↦ r ∪ (stateSupport A k p.1 ∪ bitVar k)) ∅

noncomputable def autSupport (A : BoolAutomaton S) : AutGate S n → Finset (Fin n)
  | .root => A.accept.toList.foldl (fun r s ↦ r ∪ stateSupport A n s) ∅
  | .state s k => stateSupport A k s
  | .lit _ k => {k}
  | .conj s _ k => stateSupport A k s ∪ {k}

private theorem foldl_union_subset {α : Type*} (g : α → Finset (Fin n))
    (T : Finset (Fin n)) :
    ∀ (l : List α) (init : Finset (Fin n)), init ⊆ T → (∀ p ∈ l, g p ⊆ T) →
      l.foldl (fun r p ↦ r ∪ g p) init ⊆ T
  | [], _, hinit, _ => hinit
  | p :: l, init, hinit, hl => by
      simp only [List.foldl_cons]
      exact foldl_union_subset g T l _
        (Finset.union_subset hinit (hl p (List.mem_cons_self ..)))
        (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))

/-- The support of `state s k` lies among the first `k` bits. -/
theorem stateSupport_subset (A : BoolAutomaton S) :
    ∀ (k : ℕ) (s : S),
      stateSupport A k s ⊆ Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < k
  | 0, s => by simp [stateSupport]
  | k + 1, s => by
      simp only [stateSupport]
      apply foldl_union_subset
      · exact Finset.empty_subset _
      · intro p _
        apply Finset.union_subset
        · refine (stateSupport_subset A k p.1).trans ?_
          intro j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro j hj
          simp only [bitVar] at hj
          split at hj
          · simp only [Finset.mem_singleton] at hj
            subst hj
            simp
          · simp at hj

theorem aut_child_rank (A : BoolAutomaton S) (gate child : AutGate S n)
    (h : (autNode A gate).IsChild child) : autRank child < autRank gate := by
  cases gate with
  | root =>
      simp only [autNode, NNFNode.IsChild] at h
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
      simp only [autRank, Fin.val_last]
      omega
  | state s k =>
      rcases k with ⟨_ | j, hk⟩
      · simp only [autNode] at h
        split at h <;> simp [NNFNode.IsChild] at h
      · simp only [autNode, NNFNode.IsChild] at h
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
        simp only [autRank]
        omega
  | lit b k =>
      simp only [autNode] at h
      split at h <;> simp [NNFNode.IsChild] at h
  | conj s b k =>
      simp only [autNode, NNFNode.IsChild] at h
      rcases h with rfl | rfl
      · simp only [autRank, Fin.val_castSucc]
        omega
      · simp only [autRank]
        omega

theorem aut_semantics_eq (A : BoolAutomaton S) (gate : AutGate S n)
    (x : Fin n → Bool) :
    autSemantics A gate x ↔
      (autNode A gate).Holds x (fun child ↦ autSemantics A child x) := by
  cases gate with
  | root =>
      simp only [autNode, autSemantics, NNFNode.Holds, List.mem_map,
        BoolAutomaton.Accepts]
      constructor
      · intro hacc
        exact ⟨.state (A.run x n) (Fin.last n),
          ⟨_, Finset.mem_toList.mpr hacc, rfl⟩, by simp⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, hrun⟩
        simp only [Fin.val_last] at hrun
        rw [hrun]
        exact Finset.mem_toList.mp hs
  | state s k =>
      rcases k with ⟨_ | j, hk⟩
      · simp only [autNode, autSemantics, BoolAutomaton.run]
        split
        · rename_i heq
          subst heq
          simp [NNFNode.Holds]
        · rename_i hne
          simp only [NNFNode.Holds, iff_false]
          exact fun h ↦ hne h.symm
      · have hjn : j < n := by omega
        simp only [autNode, autSemantics, NNFNode.Holds, List.mem_map,
          BoolAutomaton.run, dif_pos hjn]
        constructor
        · intro hstep
          exact ⟨.conj (A.run x j) (x ⟨j, hjn⟩) ⟨j, hjn⟩,
            ⟨(A.run x j, x ⟨j, hjn⟩), (A.mem_preds s _).mpr hstep, rfl⟩,
            ⟨rfl, rfl⟩⟩
        · rintro ⟨_, ⟨⟨s', b⟩, hp, rfl⟩, hrun, hbit⟩
          rw [hrun, hbit]
          exact (A.mem_preds s (s', b)).mp hp
  | lit b k =>
      cases b <;> simp [autNode, autSemantics, NNFNode.Holds]
  | conj s b k =>
      simp [autNode, autSemantics, NNFNode.Holds]

theorem aut_support_eq (A : BoolAutomaton S) (gate : AutGate S n) :
    autSupport A gate = (autNode A gate).Support (autSupport A) := by
  cases gate with
  | root =>
      simp only [autNode, autSupport, NNFNode.Support, List.foldl_map,
        Fin.val_last]
  | state s k =>
      rcases k with ⟨_ | j, hk⟩
      · simp only [autNode, autSupport, stateSupport]
        split <;> simp [NNFNode.Support]
      · have hjn : j < n := by omega
        simp only [autNode, autSupport, NNFNode.Support, List.foldl_map,
          stateSupport, bitVar, dif_pos hjn]
  | lit b k =>
      cases b <;> simp [autNode, autSupport, NNFNode.Support]
  | conj s b k =>
      simp [autNode, autSupport, NNFNode.Support]

/-- The circuit compiled from an automaton reading `n` bits. -/
noncomputable def autCircuit (A : BoolAutomaton S) (n : ℕ) : NNFCircuit (Fin n) where
  Gate := AutGate S n
  gateFintype := inferInstance
  gateDecidableEq := inferInstance
  output := .root
  node := autNode A
  rank := autRank
  child_rank := aut_child_rank A
  semantics := autSemantics A
  semantics_eq := aut_semantics_eq A
  support := autSupport A
  support_eq := aut_support_eq A

theorem autCircuit_computes (A : BoolAutomaton S) (n : ℕ) :
    (autCircuit A n).Computes (fun x ↦ A.Accepts x) :=
  fun _ ↦ Iff.rfl

theorem autCircuit_decomposable (A : BoolAutomaton S) (n : ℕ) :
    (autCircuit A n).IsDecomposable := by
  intro gate left right hnode
  cases gate with
  | root => simp [autCircuit, autNode] at hnode
  | state s k =>
      rcases k with ⟨_ | j, hk⟩
      · simp only [autCircuit, autNode] at hnode
        split at hnode <;> simp at hnode
      · simp [autCircuit, autNode] at hnode
  | lit b k =>
      simp only [autCircuit, autNode] at hnode
      split at hnode <;> simp at hnode
  | conj s b k =>
      simp only [autCircuit, autNode] at hnode
      injection hnode with hl hr
      subst hl hr
      simp only [autCircuit, autSupport]
      rw [Finset.disjoint_singleton_right]
      intro hmem
      have := stateSupport_subset A _ s hmem
      simp at this

theorem autCircuit_deterministic (A : BoolAutomaton S) (n : ℕ) :
    (autCircuit A n).IsDeterministic := by
  intro gate children hnode left hleft right hright hne x
  cases gate with
  | root =>
      simp only [autCircuit, autNode] at hnode
      injection hnode with hchildren
      subst hchildren
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hleft
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hright
      simp only [autCircuit, autSemantics]
      rintro ⟨hs, ht⟩
      exact hne (by rw [← hs, ← ht])
  | state s k =>
      rcases k with ⟨_ | j, hk⟩
      · simp only [autCircuit, autNode] at hnode
        split at hnode <;> simp at hnode
      · simp only [autCircuit, autNode] at hnode
        injection hnode with hchildren
        subst hchildren
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp hleft
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp hright
        simp only [autCircuit, autSemantics]
        rintro ⟨⟨hp1, hp2⟩, hq1, hq2⟩
        apply hne
        have : p = q := Prod.ext (hp1.symm.trans hq1) (hp2.symm.trans hq2)
        rw [this]
  | lit b k =>
      simp only [autCircuit, autNode] at hnode
      split at hnode <;> simp at hnode
  | conj s b k =>
      simp [autCircuit, autNode] at hnode

/-- **Every automaton compiles to a deterministic DNNF for its language.** -/
theorem autCircuit_isDeterministicDNNF (A : BoolAutomaton S) (n : ℕ) :
    (autCircuit A n).IsDeterministicDNNF ∧
      (autCircuit A n).Computes (fun x ↦ A.Accepts x) :=
  ⟨⟨autCircuit_decomposable A n, autCircuit_deterministic A n⟩,
    autCircuit_computes A n⟩

/-- The exact gate count, linear in `n`. -/
theorem autCircuit_size (A : BoolAutomaton S) (n : ℕ) :
    (autCircuit A n).size =
      1 + Fintype.card S * (n + 1) + 2 * n + 2 * Fintype.card S * n := by
  rw [NNFCircuit.size]
  change Fintype.card (AutGate S n) = _
  rw [Fintype.card_congr (autGateEquiv S n)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
    Fintype.card_fin, Fintype.card_bool]
  ring

/-- Sharing, stated on the gate graph: `lit b k` is a child of `conj s b k`
for every state `s`, so a literal gate has `Fintype.card S` parents. -/
theorem lit_isChild (A : BoolAutomaton S) (n : ℕ) (s : S) (b : Bool) (k : Fin n) :
    ((autCircuit A n).node (.conj s b k)).IsChild (.lit b k) := by
  simp [autCircuit, autNode, NNFNode.IsChild]

/-- And `state s k` is a child of `conj s b k` for both bits `b`, so a state
gate has two parents. -/
theorem state_isChild (A : BoolAutomaton S) (n : ℕ) (s : S) (b : Bool) (k : Fin n) :
    ((autCircuit A n).node (.conj s b k)).IsChild (.state s k.castSucc) := by
  simp [autCircuit, autNode, NNFNode.IsChild]

/-- Parity: the state is the parity of the bits read so far. -/
def parityAutomaton : BoolAutomaton Bool := ⟨false, fun s b ↦ xor s b, {true}⟩

theorem parity_isDeterministicDNNF (n : ℕ) :
    (autCircuit parityAutomaton n).IsDeterministicDNNF :=
  (autCircuit_isDeterministicDNNF parityAutomaton n).1

/-- Parity of `n` bits in `8n + 3` shared gates; any DNF needs `2 ^ (n - 1)`
terms. -/
theorem parity_size (n : ℕ) : (autCircuit parityAutomaton n).size = 8 * n + 3 := by
  rw [autCircuit_size, Fintype.card_bool]
  ring

/-- The parity circuit computes exclusive or, checked on all eight inputs of
length three. -/
example : ∀ x : Fin 3 → Bool,
    parityAutomaton.Accepts x ↔ xor (xor (x 0) (x 1)) (x 2) = true := by
  decide

/-- And the check is not vacuous: the same procedure rejects a wrong
specification. -/
example : ¬ ∀ x : Fin 3 → Bool,
    parityAutomaton.Accepts x ↔ (x 0 && x 1 && x 2) = true := by
  decide

/-- Counting ones modulo three, with three states. -/
def modThreeAutomaton : BoolAutomaton (Fin 3) :=
  ⟨0, fun s b ↦ if b then s + 1 else s, {0}⟩

theorem modThree_isDeterministicDNNF (n : ℕ) :
    (autCircuit modThreeAutomaton n).IsDeterministicDNNF :=
  (autCircuit_isDeterministicDNNF modThreeAutomaton n).1

theorem modThree_size (n : ℕ) :
    (autCircuit modThreeAutomaton n).size = 11 * n + 4 := by
  rw [autCircuit_size, Fintype.card_fin]
  ring

/-- Checked on all sixteen inputs of length four. -/
example : ∀ x : Fin 4 → Bool,
    modThreeAutomaton.Accepts x ↔
      (Finset.univ.filter fun j ↦ x j = true).card % 3 = 0 := by
  decide

end Automaton

end CircuitTests

end DDNNFNegation
