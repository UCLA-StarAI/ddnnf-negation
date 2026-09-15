import DDNNFNegation.Gadget
import TutorialBox

/-!
# Composing the outer function with a linear map

For an arbitrary family of columns `E`, the encoded function evaluates the
outer function at their selected sum. The definitions and identities here
do not require the large-image property; that property is established
separately in `EncoderExistence.lean`.
-/

namespace DDNNFNegation

open Finset

variable {ι G : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix multiplication by the encoding columns, written as a subset sum. -/
@[tutorial_box "def:tutorial-hard-function"]
def subsetSum [AddCommMonoid G] (a : ι → G) (x : ι → Bool) : G :=
  ∑ i, if x i then a i else 0

/-- The number of Boolean variables, the tutorial's `N = 60 n²`. -/
abbrev encodedInputCount (n : ℕ) : ℕ :=
  60 * (n * n)

/-- The encoded function `L_n(x) = F_n(Ex)`, for arbitrary encoding columns. -/
@[tutorial_box "def:tutorial-hard-function"]
def hardFunction {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (a : ι → ((Fin n × Fin n) → GadgetVector)) (x : ι → Bool) : Prop :=
  outerFunction ranks hn (subsetSum a x)

end DDNNFNegation
