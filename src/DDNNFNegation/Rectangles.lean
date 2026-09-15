import Mathlib
import TutorialBox

/-!
# Rectangles across partitions of Boolean variables

A rectangle is closed under recombining assignments across its partition.
This file gives restriction, product, and cardinality facts and defines
balanced partitions. `GateElimination.lean` constructs covers from circuits;
`ZeroFiber.lean` bounds each rectangle's intersection with the zero fiber,
and `FinalCover.lean` combines the bounds.
-/

namespace DDNNFNegation

open Finset

noncomputable section

/-- A cut is balanced when both of its sides contain at least one third of
the positions. -/
@[tutorial_box "def:tutorial-rectangles"]
def IsBalanced {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) : Prop :=
  Fintype.card ι ≤ 3 * S.card ∧ Fintype.card ι ≤ 3 * Sᶜ.card

/-- A balanced cut leaves at least one third of the variables on its selected side. -/
theorem IsBalanced.left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Finset ι} (hS : IsBalanced S) :
    Fintype.card ι ≤ 3 * S.card := hS.1

/-- A balanced cut also leaves at least one third of the variables on its complementary
side. -/
theorem IsBalanced.right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Finset ι} (hS : IsBalanced S) :
    Fintype.card ι ≤ 3 * Sᶜ.card := hS.2

/-- Split a Boolean assignment at an arbitrary set of individual indices. -/
noncomputable def assignmentPartitionEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    (ι → Bool) ≃ ((S → Bool) × (↥(Sᶜ) → Bool)) where
  toFun x := (fun i => x i, fun i => x i)
  invFun p i := if hi : i ∈ S then p.1 ⟨i, hi⟩ else p.2 ⟨i, by simp [hi]⟩
  left_inv x := by
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp [i.property]
    · funext i
      have hi : (i : ι) ∉ S := by
        simpa only [Finset.mem_compl] using i.property
      simp [hi]

/-- The ordinary set of full Boolean assignments represented by `A × C`
at the partition `S`. -/
def assignmentRectangle
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (S : Finset iota) (A : Finset (S → Bool))
    (C : Finset (↑(Sᶜ) → Bool)) : Finset (iota → Bool) :=
  univ.filter fun x ↦
    (assignmentPartitionEquiv S x).1 ∈ A ∧
      (assignmentPartitionEquiv S x).2 ∈ C

@[simp] theorem mem_assignmentRectangle
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (S : Finset iota) (A : Finset (S → Bool))
    (C : Finset (↑(Sᶜ) → Bool)) (x : iota → Bool) :
    x ∈ assignmentRectangle S A C ↔
      (assignmentPartitionEquiv S x).1 ∈ A ∧
        (assignmentPartitionEquiv S x).2 ∈ C := by
  simp [assignmentRectangle]

/-- A rectangle `A × C` of Boolean assignments for a cut `S`: the
assignments whose restriction to `S` lies in `A` and whose restriction to
the complement lies in `C` (`assignments`).  The cut is stored with the
two sides, and the rectangle is balanced (`IsBalanced`) when the
cut is. -/
@[tutorial_box "def:tutorial-rectangles"]
structure BooleanRectangle (iota : Type*) [Fintype iota] [DecidableEq iota]
    where
  cut : Finset iota
  left : Finset (cut → Bool)
  right : Finset (↑(cutᶜ) → Bool)

namespace BooleanRectangle

/-- Full assignments represented by the two sides of a rectangle. -/
def assignments
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (R : BooleanRectangle iota) : Finset (iota → Bool) :=
  assignmentRectangle R.cut R.left R.right

/-- Both sides of the stored cut contain at least one third of the
variables. -/
def IsBalanced
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (R : BooleanRectangle iota) : Prop :=
  DDNNFNegation.IsBalanced R.cut

end BooleanRectangle

/-- Exact output interface of the published balanced rectangle extraction.
The function `f` is the satisfying set being covered. -/
structure BalancedRectangleCover
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (f : (iota → Bool) → Prop) (J : Type*) [Fintype J] where
  rectangle : J → BooleanRectangle iota
  balanced : ∀ j, (rectangle j).IsBalanced
  sound : ∀ j x, x ∈ (rectangle j).assignments → f x
  complete : ∀ x, f x → ∃ j, x ∈ (rectangle j).assignments

end

end DDNNFNegation
