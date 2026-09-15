import DDNNFNegation.ZeroSquares

/-!
# Common partial sums in a zero rectangle

On the zero fiber of the encoder, the two partial sums across a partition
are equal. For a rectangle on which the encoded function vanishes, any two
such common values can be recombined within the rectangle. Their sums are
zeros of the outer function, hence the common values index a zero square
of the matrix. The spectral bound controls the number of these values;
fiber counts then control the number of assignments mapping to them.
-/

namespace DDNNFNegation

open Finset

noncomputable section

section SetLevel

variable {X Y G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The pairs of the rectangle `A × C` whose two partial sums add to zero. -/
def rectangleZeroPairs (L : X → G) (R : Y → G) (A : Finset X) (C : Finset Y) :
    Finset (X × Y) :=
  (A ×ˢ C).filter fun xy => L xy.1 + R xy.2 = 0

/-- The values that occur both as a left partial sum on `𝒜` and as a right
partial sum on `𝒞`. On a zero rectangle, their Cartesian square is a zero
square of the outer matrix. -/
def commonPartialSums (L : X → G) (R : Y → G) (A : Finset X) (C : Finset Y) : Finset G :=
  A.image L ∩ C.image R

omit [AddCommGroup G] in
/-- A common partial sum is attained by an assignment on each side of the rectangle. -/
theorem mem_commonPartialSums (L : X → G) (R : Y → G) (A : Finset X) (C : Finset Y) (σ : G) :
    σ ∈ commonPartialSums L R A C ↔ (∃ x ∈ A, L x = σ) ∧ ∃ y ∈ C, R y = σ := by
  simp [commonPartialSums]

omit [DecidableEq G] in
/-- In a group in which every element is its own negative, `a + b = 0`
exactly when `a = b`. -/
theorem add_eq_zero_iff_eq (hexp : ∀ g : G, g + g = 0) (a b : G) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [hexp, add_zero]
      _ = (a + b) + b := by rw [add_assoc]
      _ = b := by rw [h, zero_add]
  · intro h
    rw [h]
    exact hexp b

/-- The zero pairs with common value `σ` are the product of the two fibers
over `σ`. -/
theorem rectangleZeroPairs_filter (hexp : ∀ g : G, g + g = 0)
    (L : X → G) (R : Y → G) (A : Finset X) (C : Finset Y) (σ : G) :
    (rectangleZeroPairs L R A C).filter (fun xy => R xy.2 = σ) =
      (A.filter fun x => L x = σ) ×ˢ (C.filter fun y => R y = σ) := by
  ext ⟨x, y⟩
  simp only [rectangleZeroPairs, mem_filter, mem_product, add_eq_zero_iff_eq hexp]
  constructor
  · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, hR⟩
    exact ⟨⟨hx, hxy.trans hR⟩, hy, hR⟩
  · rintro ⟨⟨hx, hL⟩, hy, hR⟩
    exact ⟨⟨⟨hx, hy⟩, hL.trans hR.symm⟩, hR⟩

variable [Fintype G]

/-- The zero pairs of the rectangle, counted by their common value
`σ ∈ I`: outside `I` one of the two fibers is empty. -/
theorem rectangleZeroPairs_card_eq_sum (hexp : ∀ g : G, g + g = 0)
    (L : X → G) (R : Y → G) (A : Finset X) (C : Finset Y) :
    (rectangleZeroPairs L R A C).card =
      ∑ σ ∈ commonPartialSums L R A C,
        (A.filter fun x => L x = σ).card * (C.filter fun y => R y = σ).card := by
  let Z := rectangleZeroPairs L R A C
  have hmap : Set.MapsTo (fun xy : X × Y => R xy.2) ↑Z ↑(univ : Finset G) := by simp
  calc
    Z.card = ∑ σ ∈ (univ : Finset G), (Z.filter fun xy => R xy.2 = σ).card :=
      card_eq_sum_card_fiberwise hmap
    _ = ∑ σ ∈ (univ : Finset G),
        (A.filter fun x => L x = σ).card * (C.filter fun y => R y = σ).card := by
      apply sum_congr rfl
      intro σ _
      rw [rectangleZeroPairs_filter hexp, card_product]
    _ = ∑ σ ∈ commonPartialSums L R A C,
        (A.filter fun x => L x = σ).card * (C.filter fun y => R y = σ).card := by
      symm
      apply sum_subset (subset_univ _)
      intro σ _ hσ
      rw [mem_commonPartialSums, not_and_or] at hσ
      rcases hσ with hleft | hright
      · rw [filter_eq_empty_iff.mpr fun x hx h => hleft ⟨x, hx, h⟩, card_empty, zero_mul]
      · rw [filter_eq_empty_iff.mpr fun y hy h => hright ⟨y, hy, h⟩, card_empty, mul_zero]

/-- Uniform caps on the complete fibers of the two partial-sum maps bound
the zero pairs by `|I|` times the product of the caps: each intersection
of a fiber with a side of the rectangle is at most the whole fiber. -/
theorem rectangleZeroPairs_card_le [Fintype X] [Fintype Y] (hexp : ∀ g : G, g + g = 0)
    (L : X → G) (R : Y → G) (A : Finset X) (C : Finset Y)
    (leftCap rightCap : ℝ) (hleftCap : 0 ≤ leftCap)
    (hleft : ∀ σ, (((univ : Finset X).filter fun x => L x = σ).card : ℝ) ≤ leftCap)
    (hright : ∀ σ, (((univ : Finset Y).filter fun y => R y = σ).card : ℝ) ≤ rightCap) :
    ((rectangleZeroPairs L R A C).card : ℝ) ≤
      (commonPartialSums L R A C).card * leftCap * rightCap := by
  rw [rectangleZeroPairs_card_eq_sum hexp]
  push_cast
  calc
    ∑ σ ∈ commonPartialSums L R A C,
        ((A.filter fun x => L x = σ).card : ℝ) * (C.filter fun y => R y = σ).card ≤
        ∑ _σ ∈ commonPartialSums L R A C, leftCap * rightCap := by
      refine sum_le_sum fun σ _ => mul_le_mul ?_ ?_ (by positivity) hleftCap
      · exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ (subset_univ A)))).trans
          (hleft σ)
      · exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ (subset_univ C)))).trans
          (hright σ)
    _ = (commonPartialSums L R A C).card * leftCap * rightCap := by
      rw [sum_const, nsmul_eq_mul, mul_assoc]

end SetLevel

section OuterFunction

variable {n : ℕ} {X Y : Type*}
  (L : X → ((Fin n × Fin n) → GadgetVector)) (R : Y → ((Fin n × Fin n) → GadgetVector))
  (A : Finset X) (C : Finset Y)

/-- On a zero rectangle, the outer function vanishes at the sum of any two common partial sums. -/
theorem commonPartialSums_sums_zero (ranks : LabelOrders n) (hn : 0 < n)
    (hzero : ∀ x ∈ A, ∀ y ∈ C, ¬ outerFunction ranks hn (L x + R y)) :
    ∀ σ ∈ commonPartialSums L R A C, ∀ τ ∈ commonPartialSums L R A C,
      ¬ outerFunction ranks hn (σ + τ) := by
  intro σ hσ τ hτ
  obtain ⟨⟨x, hx, rfl⟩, _⟩ := (mem_commonPartialSums L R A C σ).mp hσ
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := (mem_commonPartialSums L R A C τ).mp hτ
  exact hzero x hx y hy

/-- The common values of a zero rectangle number at most `ε * |G|`, by the zero-square bound. -/
theorem commonPartialSums_card_le (ranks : LabelOrders n) (hn : 0 < n)
    (hzero : ∀ x ∈ A, ∀ y ∈ C, ¬ outerFunction ranks hn (L x + R y)) :
    ((commonPartialSums L R A C).card : ℝ) ≤
      spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) :=
  small_zero_squares ranks hn _ (commonPartialSums_sums_zero L R A C ranks hn hzero)

/-- Combine the bound on common values with uniform caps on the two partial-sum fibers. -/
theorem zeroRectangle_zeroPairs_card_le [Fintype X] [Fintype Y]
    (ranks : LabelOrders n) (hn : 0 < n)
    (leftCap rightCap : ℝ) (hleftCap : 0 ≤ leftCap) (hrightCap : 0 ≤ rightCap)
    (hleft : ∀ σ, (((univ : Finset X).filter fun x => L x = σ).card : ℝ) ≤ leftCap)
    (hright : ∀ σ, (((univ : Finset Y).filter fun y => R y = σ).card : ℝ) ≤ rightCap)
    (hzero : ∀ x ∈ A, ∀ y ∈ C, ¬ outerFunction ranks hn (L x + R y)) :
    ((rectangleZeroPairs L R A C).card : ℝ) ≤
      spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) *
        leftCap * rightCap :=
  calc
    ((rectangleZeroPairs L R A C).card : ℝ) ≤
        (commonPartialSums L R A C).card * leftCap * rightCap :=
      rectangleZeroPairs_card_le gridVector_add_self L R A C leftCap rightCap hleftCap
        hleft hright
    _ ≤ spectralEpsilon n * Fintype.card ((Fin n × Fin n) → GadgetVector) *
          leftCap * rightCap :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (commonPartialSums_card_le L R A C ranks hn hzero) hleftCap)
        hrightCap

end OuterFunction

end

end DDNNFNegation
