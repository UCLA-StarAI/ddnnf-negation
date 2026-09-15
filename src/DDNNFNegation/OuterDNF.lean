import DDNNFNegation.RankOrders
import DDNNFNegation.LabelSets
import TutorialBox

/-!
# The outer unambiguous DNF

A term fixes the selected labels to one and all other labels to zero
in its own bucket. It also requires a rank prefix in each other bucket
to be zero. The cutoffs are determined by permutations of the labels.
Distinct terms conflict, and a moment bound selects permutations for
which every eligible term has few literals. The outer DNF is the
disjunction of the terms for eligible label sets.
-/

namespace DDNNFNegation

open Finset

noncomputable section

/-! ## Terms -/

/-- An outer term index `(i,S)`, with no eligibility threshold.
Nonemptiness is needed to take the least rank of a selected label. -/
@[ext, tutorial_box "def:tutorial-outer-terms"]
structure OuterTerm (n : ℕ) where
  bucket : Fin n
  chosen : Finset (Fin n)
  nonempty : chosen.Nonempty

/-- The terms retained in `f_n`: an outer term with at least `n/3` labels.
The conflict argument below uses only the underlying `OuterTerm`. -/
@[ext]
structure ThresholdTerm (n : ℕ) extends OuterTerm n where
  third : n ≤ 3 * chosen.card

instance {n : ℕ} : Coe (ThresholdTerm n) (OuterTerm n) := ⟨ThresholdTerm.toOuterTerm⟩

/-- Selecting labels from `[n]` gives at most `n` positive literals. -/
theorem OuterTerm.card_chosen_le {n : ℕ} (T : OuterTerm n) :
    T.chosen.card ≤ n := by
  simpa using card_le_univ T.chosen

/-- The cutoff `M_{π_j}(S)` of the term toward bucket `j`: the least
`π_j`-rank of a chosen label, which is `permutationMin (π_j) S` of
`RankOrders.lean` (where the rank orders are sampled), here as a rank in
`Fin n`.  Its prefix has `M_{π_j}(S) + 1` elements. -/
@[tutorial_box "def:tutorial-outer-terms"]
def termCutoff {n : ℕ} (ranks : LabelOrders n) (_hn : 0 < n)
    (T : OuterTerm n) (j : Fin n) : Fin n :=
  ⟨permutationMin (ranks j) T.chosen,
    permutationMin_lt_card (ranks j) T.chosen T.nonempty⟩

/-- For rewriting calculations, the cutoff is the least permutation rank of the chosen
labels. -/
theorem termCutoff_val {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : OuterTerm n) (j : Fin n) :
    (termCutoff ranks hn T j : ℕ) = permutationMin (ranks j) T.chosen :=
  rfl

/-- The cutoff is attained: some chosen label has exactly that rank. -/
theorem exists_chosen_rank_eq_termCutoff {n : ℕ} (ranks : LabelOrders n)
    (hn : 0 < n) (T : OuterTerm n) (j : Fin n) :
    ∃ x ∈ T.chosen, ranks j x = termCutoff ranks hn T j := by
  have hne := T.nonempty
  obtain ⟨x, hx, hxmin⟩ := mem_image.mp
    (min'_mem (T.chosen.image (ranks j)) (hne.image _))
  refine ⟨x, hx, Fin.ext ?_⟩
  rw [hxmin, termCutoff_val, permutationMin_of_nonempty (ranks j) T.chosen hne]

/-- The positive literals: the coordinate set `P_{i,S} = {i} × S` of the
term, the chosen labels embedded into their bucket. -/
@[tutorial_box "def:tutorial-outer-terms"]
def termPositive {n : ℕ} (T : OuterTerm n) : Finset (Fin n × Fin n) :=
  termCoordinates T.bucket T.chosen

/-- The labels of bucket `j` whose rank under the term's own permutation
`π_i` is at most the cutoff `M_{π_j}(S)`. -/
@[tutorial_box "def:tutorial-outer-terms"]
def termCrossPrefix {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : OuterTerm n) (j : Fin n) : Finset (Fin n × Fin n) :=
  (univ.filter fun y : Fin n =>
      ranks T.bucket y ≤ termCutoff ranks hn T j).image fun y => (j, y)

/-- Negative literals in the term's own bucket. -/
def termOwnNegative {n : ℕ} (T : OuterTerm n) : Finset (Fin n × Fin n) :=
  (univ \ T.chosen).image fun x => (T.bucket, x)

/-- All negative literals: the complement inside the own bucket together
with one prefix in every other bucket. -/
@[tutorial_box "def:tutorial-outer-terms"]
def termNegative {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : OuterTerm n) : Finset (Fin n × Fin n) :=
  termOwnNegative T ∪
    (univ.filter fun j : Fin n => j ≠ T.bucket).biUnion
      (termCrossPrefix ranks hn T)

/-- The signed term of the outer construction. -/
@[tutorial_box "def:tutorial-outer-terms"]
def termSigned {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : OuterTerm n) : SignedTerm (Fin n × Fin n) where
  positive := termPositive T
  negative := termNegative ranks hn T

/-- The disjunction of the outer terms indexed by eligible label sets. -/
@[tutorial_box "def:tutorial-outer-function"]
def outerDNF {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (v : Fin n × Fin n → Prop) : Prop :=
  ∃ T : ThresholdTerm n, (termSigned ranks hn T).Satisfied v

/-- Positive coordinates have the term bucket and a selected label. -/
theorem mem_termPositive {n : ℕ} {T : OuterTerm n} {i x : Fin n} :
    (i, x) ∈ termPositive T ↔ i = T.bucket ∧ x ∈ T.chosen :=
  mem_termCoordinates

/-- Negative coordinates in the own bucket have an unselected label. -/
theorem mem_termOwnNegative {n : ℕ} {T : OuterTerm n} {i x : Fin n} :
    (i, x) ∈ termOwnNegative T ↔ i = T.bucket ∧ x ∉ T.chosen := by
  simp [termOwnNegative, and_comm, eq_comm]

/-- A cross-bucket prefix consists of labels below the term cutoff in the term bucket's
order. -/
theorem mem_termCrossPrefix {n : ℕ} {ranks : LabelOrders n} {hn : 0 < n}
    {T : OuterTerm n} {j i y : Fin n} :
    (i, y) ∈ termCrossPrefix ranks hn T j ↔
      i = j ∧ ranks T.bucket y ≤ termCutoff ranks hn T j := by
  simp [termCrossPrefix, and_comm, eq_comm]

/-- An unselected label in the own bucket is a negative literal. -/
theorem mem_termNegative_of_own {n : ℕ} {ranks : LabelOrders n} {hn : 0 < n}
    {T : OuterTerm n} {x : Fin n} (hx : x ∉ T.chosen) :
    (T.bucket, x) ∈ termNegative ranks hn T :=
  mem_union_left _ (mem_termOwnNegative.mpr ⟨rfl, hx⟩)

/-- A label below the cutoff in another bucket is a negative literal. -/
theorem mem_termNegative_of_cross {n : ℕ} {ranks : LabelOrders n} {hn : 0 < n}
    {T : OuterTerm n} {j y : Fin n} (hj : j ≠ T.bucket)
    (hy : ranks T.bucket y ≤ termCutoff ranks hn T j) :
    (j, y) ∈ termNegative ranks hn T := by
  apply mem_union_right
  apply mem_biUnion.mpr
  exact ⟨j, by simp [hj], mem_termCrossPrefix.mpr ⟨rfl, hy⟩⟩

/-! ## Unambiguity -/

/-- Two terms in the same bucket with different label sets: some label
lies in one set and not the other, and that label is positive in one term
and negative in the other. -/
theorem termSigned_incompatible_same_bucket {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T U : OuterTerm n)
    (hbucket : T.bucket = U.bucket) (hchosen : T.chosen ≠ U.chosen) :
    (termSigned ranks hn T).Incompatible (termSigned ranks hn U) := by
  by_cases hTU : T.chosen ⊆ U.chosen
  · have hUT : ¬U.chosen ⊆ T.chosen := fun h => hchosen (subset_antisymm hTU h)
    obtain ⟨x, hxU, hxT⟩ := Finset.not_subset.mp hUT
    refine ⟨(U.bucket, x), Or.inr ⟨mem_termPositive.mpr ⟨rfl, hxU⟩, ?_⟩⟩
    change (U.bucket, x) ∈ termNegative ranks hn T
    rw [← hbucket]
    exact mem_termNegative_of_own hxT
  · obtain ⟨x, hxT, hxU⟩ := Finset.not_subset.mp hTU
    refine ⟨(T.bucket, x), Or.inl ⟨mem_termPositive.mpr ⟨rfl, hxT⟩, ?_⟩⟩
    change (T.bucket, x) ∈ termNegative ranks hn U
    rw [hbucket]
    exact mem_termNegative_of_own hxU

/-- Two terms in different buckets: whichever term has the smaller first
rank toward the other bucket has a positive label inside the other term's
prefix. -/
theorem termSigned_incompatible_distinct_bucket {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T U : OuterTerm n)
    (hbucket : T.bucket ≠ U.bucket) :
    (termSigned ranks hn T).Incompatible (termSigned ranks hn U) := by
  by_cases hab : termCutoff ranks hn T U.bucket ≤ termCutoff ranks hn U T.bucket
  · obtain ⟨x, hxT, hxrank⟩ := exists_chosen_rank_eq_termCutoff ranks hn T U.bucket
    refine ⟨(T.bucket, x), Or.inl ⟨mem_termPositive.mpr ⟨rfl, hxT⟩, ?_⟩⟩
    change (T.bucket, x) ∈ termNegative ranks hn U
    exact mem_termNegative_of_cross (T := U) hbucket (by simpa [hxrank] using hab)
  · have hba : termCutoff ranks hn U T.bucket ≤ termCutoff ranks hn T U.bucket :=
      le_of_lt (lt_of_not_ge hab)
    obtain ⟨y, hyU, hyrank⟩ := exists_chosen_rank_eq_termCutoff ranks hn U T.bucket
    refine ⟨(U.bucket, y), Or.inr ⟨mem_termPositive.mpr ⟨rfl, hyU⟩, ?_⟩⟩
    change (U.bucket, y) ∈ termNegative ranks hn T
    exact mem_termNegative_of_cross (T := T) hbucket.symm (by simpa [hyrank] using hba)

/-- Lemma "Distinct outer terms conflict": every two distinct terms are
incompatible. -/
@[tutorial_box "lem:tutorial-term-conflict"]
theorem distinct_terms_conflict {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T U : OuterTerm n) (hTU : T ≠ U) :
    (termSigned ranks hn T).Incompatible (termSigned ranks hn U) := by
  by_cases hbucket : T.bucket = U.bucket
  · apply termSigned_incompatible_same_bucket ranks hn T U hbucket
    intro hchosen
    exact hTU (OuterTerm.ext hbucket hchosen)
  · exact termSigned_incompatible_distinct_bucket ranks hn T U hbucket

/-- Consequently no valuation satisfies two different terms. -/
theorem thresholdTerms_unambiguous {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (v : Fin n × Fin n → Prop)
    {T U : ThresholdTerm n}
    (hT : (termSigned ranks hn T).Satisfied v)
    (hU : (termSigned ranks hn U).Satisfied v) : T = U := by
  have h := SignedTerm.atMostOne_satisfied (termSigned ranks hn)
    (distinct_terms_conflict ranks hn) v hT hU
  exact ThresholdTerm.ext (congrArg OuterTerm.bucket h) (congrArg OuterTerm.chosen h)

/-! ## Consistency and the positive characteristic valuation -/

theorem termPositive_disjoint_termNegative {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T : OuterTerm n) :
    Disjoint (termPositive T) (termNegative ranks hn T) := by
  rw [Finset.disjoint_left]
  intro p hp hneg
  rcases p with ⟨i, x⟩
  obtain ⟨hi, hx⟩ := mem_termPositive.mp hp
  rcases mem_union.mp hneg with hown | hcross
  · exact (mem_termOwnNegative.mp hown).2 hx
  · obtain ⟨j, hj, hpref⟩ := mem_biUnion.mp hcross
    have hij := (mem_termCrossPrefix.mp hpref).1
    exact (mem_filter.mp hj).2 (hij.symm.trans hi)

/-- No coordinate is required both positively and negatively in a single outer term. -/
theorem termSigned_consistent {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T : OuterTerm n) :
    Disjoint (termSigned ranks hn T).positive (termSigned ranks hn T).negative :=
  termPositive_disjoint_termNegative ranks hn T

/-- Setting exactly a term's positive labels to true makes that term true.
This is the semantic bridge used by the spectral matrix. -/
theorem outerDNF_positiveCharacteristic {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T : ThresholdTerm n) :
    outerDNF ranks hn (fun u => u ∈ termPositive T) :=
  ⟨T, SignedTerm.satisfied_positiveCharacteristic _ (termSigned_consistent ranks hn T)⟩

/-! ## Literal counts -/

theorem card_termPositive {n : ℕ} (T : OuterTerm n) :
    (termPositive T).card = T.chosen.card :=
  card_termCoordinates _ _

/-- The own-bucket negative literals are the `n - |S|` unselected labels. -/
theorem card_termOwnNegative {n : ℕ} (T : OuterTerm n) :
    (termOwnNegative T).card = n - T.chosen.card := by
  rw [termOwnNegative, card_image_of_injective]
  · rw [card_sdiff_of_subset (subset_univ T.chosen), card_univ, Fintype.card_fin]
  · intro x y hxy
    exact congrArg Prod.snd hxy

/-- The rank prefix is the inverse-permutation image of the interval ending at the cutoff. -/
theorem termRankPrefix_eq_image_Iic {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : OuterTerm n) (j : Fin n) :
    (univ.filter fun y : Fin n =>
      ranks T.bucket y ≤ termCutoff ranks hn T j) =
      (Finset.Iic (termCutoff ranks hn T j)).image (ranks T.bucket).symm := by
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_image, Finset.mem_Iic]
  constructor
  · intro hy
    exact ⟨ranks T.bucket y, hy, by simp⟩
  · rintro ⟨a, ha, hay⟩
    rw [← hay]
    simpa using ha

/-- A prefix ending at rank `M` contains `M+1` coordinates. -/
theorem card_termCrossPrefix {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (T : OuterTerm n) (j : Fin n) :
    (termCrossPrefix ranks hn T j).card = (termCutoff ranks hn T j : ℕ) + 1 := by
  rw [termCrossPrefix, card_image_of_injective]
  · rw [termRankPrefix_eq_image_Iic ranks hn T j, card_image_of_injective]
    · simp
    · exact (ranks T.bucket).symm.injective
  · intro x y hxy
    exact congrArg Prod.snd hxy

/-- Exact prefix accounting: a term has `n` literals in its own bucket and
one prefix in each other bucket. -/
theorem termSigned_literalCount_le {n : ℕ}
    (ranks : LabelOrders n) (hn : 0 < n) (T : OuterTerm n) :
    (termSigned ranks hn T).positive.card +
        (termSigned ranks hn T).negative.card ≤
      n + ∑ j ∈ univ.filter (fun j : Fin n => j ≠ T.bucket),
        ((termCutoff ranks hn T j : ℕ) + 1) := by
  have hcross :
      ((univ.filter fun j : Fin n => j ≠ T.bucket).biUnion
          (termCrossPrefix ranks hn T)).card ≤
        ∑ j ∈ univ.filter (fun j : Fin n => j ≠ T.bucket),
          ((termCutoff ranks hn T j : ℕ) + 1) := by
    simpa only [card_termCrossPrefix ranks hn T] using
      (card_biUnion_le :
        ((univ.filter fun j : Fin n => j ≠ T.bucket).biUnion
          (termCrossPrefix ranks hn T)).card ≤
        ∑ j ∈ univ.filter (fun j : Fin n => j ≠ T.bucket),
          (termCrossPrefix ranks hn T j).card)
  have hnegative :
      (termNegative ranks hn T).card ≤
        (n - T.chosen.card) + ∑ j ∈ univ.filter (fun j : Fin n => j ≠ T.bucket),
          ((termCutoff ranks hn T j : ℕ) + 1) := by
    calc
      (termNegative ranks hn T).card ≤
          (termOwnNegative T).card +
            ((univ.filter fun j : Fin n => j ≠ T.bucket).biUnion
              (termCrossPrefix ranks hn T)).card :=
        card_union_le (termOwnNegative T) _
      _ ≤ (n - T.chosen.card) + ∑ j ∈ univ.filter (fun j : Fin n => j ≠ T.bucket),
          ((termCutoff ranks hn T j : ℕ) + 1) := by
        rw [card_termOwnNegative]
        exact Nat.add_le_add_left hcross _
  have hkn := T.card_chosen_le
  change (termPositive T).card + (termNegative ranks hn T).card ≤ _
  rw [card_termPositive]
  omega

/-- The cost over all `n` orders dominates the literal count. -/
theorem termSigned_literalCount_le_rankTupleCost {n : ℕ}
    (r : LabelOrders n) (hn : 0 < n) (T : OuterTerm n) :
    (termSigned r hn T).positive.card +
        (termSigned r hn T).negative.card ≤
      n + rankTupleCost r T.chosen := by
  have houter := termSigned_literalCount_le r hn T
  calc
    (termSigned r hn T).positive.card +
        (termSigned r hn T).negative.card
        ≤ n + ∑ j ∈ univ.filter (fun j : Fin n => j ≠ T.bucket),
          ((termCutoff r hn T j : ℕ) + 1) := houter
    _ ≤ n + ∑ j : Fin n,
          ((termCutoff r hn T j : ℕ) + 1) := by
      apply Nat.add_le_add_left
      exact sum_le_sum_of_subset (filter_subset _ _)
    _ = n + rankTupleCost r T.chosen := by
      simp only [rankTupleCost, termCutoff_val]

/-! ## The union bound over the threshold family -/

/-- Pure finite union bound over the label sets of one bucket. -/
theorem exists_rankTuple_threshold {n C : ℕ}
    (hbad :
      ∑ S ∈ eligibleLabelSets n, (badRankTuples C S).card <
        Fintype.card (LabelOrders n)) :
    ∃ r : LabelOrders n, ∀ S : Finset (Fin n), n ≤ 3 * S.card →
      rankTupleCost r S ≤ C * n := by
  classical
  by_contra hnone
  push Not at hnone
  let badUnion : Finset (LabelOrders n) :=
    (eligibleLabelSets n).biUnion fun S => badRankTuples C S
  have huniv_subset : (univ : Finset (LabelOrders n)) ⊆ badUnion := by
    intro r _hr
    obtain ⟨S, hS, hrbad⟩ := hnone r
    apply mem_biUnion.mpr
    exact ⟨S, mem_eligibleLabelSets.mpr hS,
      mem_filter.mpr ⟨mem_univ _, hrbad⟩⟩
  have hsample_le : Fintype.card (LabelOrders n) ≤ badUnion.card := by
    rw [← card_univ]
    exact card_le_card huniv_subset
  have hunion_le : badUnion.card ≤
      ∑ S ∈ eligibleLabelSets n, (badRankTuples C S).card :=
    card_biUnion_le
  omega

/-- Apply the moment bound and Markov's inequality to each eligible set.
There are fewer than `2^n` such sets to check, and each fails the `9*n`
cost bound with probability at most `3^n * (4/5)^{9*n+1}`. The expected
number of failures is below one because `(5/4)^9 > 6`. -/
theorem sum_badRankTuples_threshold_nine_lt {n : ℕ} (hn : 0 < n) :
    ∑ S ∈ eligibleLabelSets n, (badRankTuples 9 S).card <
      Fintype.card (LabelOrders n) := by
  let fam := eligibleLabelSets n
  let x : ℝ := (5 : ℝ) / 4
  let P : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hx : 1 ≤ x := by norm_num [x]
  have hsum :
      ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) * x ^ (9 * n + 1) ≤
        (fam.card : ℝ) * (3 * P) ^ n := by
    calc
      ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) * x ^ (9 * n + 1) =
          ∑ S ∈ fam, ((badRankTuples 9 S).card : ℝ) * x ^ (9 * n + 1) := by
        push_cast
        rw [sum_mul]
      _ ≤ ∑ _S ∈ fam, (3 * P) ^ n := by
        apply sum_le_sum
        intro S hSmem
        have hthird : n ≤ 3 * S.card := mem_eligibleLabelSets.mp hSmem
        have hS : S.Nonempty := card_pos.mp (by omega)
        apply card_badRankTuples_mul_pow_le_of_singleMoment
          (C := 9) (x := x) (M := 3) hx S
        simpa [P, x] using singleMoment_three S hS hthird
      _ = (fam.card : ℝ) * (3 * P) ^ n := by
        rw [sum_const, nsmul_eq_mul]
  have hfamilyNat : fam.card ≤ 2 ^ n := by
    show (eligibleLabelSets n).card ≤ 2 ^ n
    have := card_eligible_add_card_ineligible n
    omega
  have hfamily : (fam.card : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hfamilyNat
  have hsum' :
      ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) * x ^ (9 * n + 1) ≤
        (6 * P) ^ n := by
    calc
      ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) * x ^ (9 * n + 1)
          ≤ (fam.card : ℝ) * (3 * P) ^ n := hsum
      _ ≤ (2 : ℝ) ^ n * (3 * P) ^ n :=
        mul_le_mul_of_nonneg_right hfamily (by positivity)
      _ = (6 * P) ^ n := by
        rw [← mul_pow]
        ring
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hstrict : (6 * P) ^ n < P ^ n * x ^ (9 * n + 1) := by
    rw [mul_pow]
    exact mul_lt_mul_of_pos_right
      (by simpa [x] using six_pow_lt_five_four_pow_nine_mul hn)
      (pow_pos hPpos n) |>.trans_eq (by ring)
  have hcastlt :
      ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) <
        Fintype.card (LabelOrders n) := by
    have hmul :
        ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) * x ^ (9 * n + 1) <
          (Fintype.card (LabelOrders n) : ℝ) * x ^ (9 * n + 1) := by
      calc
        ((∑ S ∈ fam, (badRankTuples 9 S).card : ℕ) : ℝ) * x ^ (9 * n + 1)
            ≤ (6 * P) ^ n := hsum'
        _ < P ^ n * x ^ (9 * n + 1) := hstrict
        _ = (Fintype.card (LabelOrders n) : ℝ) * x ^ (9 * n + 1) := by
          simp [P, LabelOrders]
    exact lt_of_mul_lt_mul_right hmul (by positivity)
  exact_mod_cast hcastlt

/-- Some tuple of label orders makes every eligible term have at most
`10*n` literals: at most `n` in its own bucket and `9*n` in the others. -/
@[tutorial_box "lem:tutorial-term-width"]
theorem every_term_short {n : ℕ} (hn : 0 < n) :
    ∃ ranks : LabelOrders n,
      ∀ T : ThresholdTerm n,
        (termSigned ranks hn T).positive.card +
            (termSigned ranks hn T).negative.card ≤ 10 * n := by
  obtain ⟨r, hr⟩ := exists_rankTuple_threshold (sum_badRankTuples_threshold_nine_lt hn)
  refine ⟨r, ?_⟩
  intro T
  have h := (termSigned_literalCount_le_rankTupleCost r hn T).trans
    (Nat.add_le_add_left (hr T.chosen T.third) n)
  omega

/-! ## The number of terms -/

/-- A term is determined by its bucket and its label set. -/
def thresholdTermEmbedding (n : ℕ) : ThresholdTerm n → Fin n × Finset (Fin n) :=
  fun T => (T.bucket, T.chosen)

/-- The bucket and chosen labels recover the selected term; its eligibility proof carries no
additional data. -/
theorem thresholdTermEmbedding_injective (n : ℕ) :
    Function.Injective (thresholdTermEmbedding n) := by
  intro T U h
  simp only [thresholdTermEmbedding, Prod.mk.injEq] at h
  exact ThresholdTerm.ext h.1 h.2

instance thresholdTermFintype (n : ℕ) : Fintype (ThresholdTerm n) :=
  Fintype.ofInjective _ (thresholdTermEmbedding_injective n)

/-- At most `n 2^n` terms. -/
theorem card_thresholdTerm_le (n : ℕ) :
    Fintype.card (ThresholdTerm n) ≤ n * 2 ^ n := by
  calc
    Fintype.card (ThresholdTerm n) ≤ Fintype.card (Fin n × Finset (Fin n)) :=
      Fintype.card_le_of_injective _ (thresholdTermEmbedding_injective n)
    _ = n * 2 ^ n := by simp [Fintype.card_prod, Fintype.card_finset]

end

end DDNNFNegation
