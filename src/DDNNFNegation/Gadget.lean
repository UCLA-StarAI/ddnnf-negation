import DDNNFNegation.OuterDNF
import TutorialBox

/-!
# The four-bit gadget and the outer function

`Q` takes the inner product of two two-bit vectors. Its value is zero on
ten of the sixteen inputs and one on six. Applying `Q` coordinatewise
supplies the Boolean inputs to the outer unambiguous DNF. The resulting
function `F` is the intermediate layer used in the encoded construction
and in the matrix's zero-set argument.
-/

namespace DDNNFNegation

open Finset

/-! ## The gadget and the function `F_n` -/

/-- The four-bit alphabet `V`: two paired copies of `𝔽₂²`. -/
@[tutorial_box "def:tutorial-gadget"]
abbrev GadgetVector := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

/-- The inner product of the two halves, `Q(w, w') = w₁ w'₁ + w₂ w'₂`. -/
@[tutorial_box "def:tutorial-gadget"]
def quadForm (t : GadgetVector) : ZMod 2 :=
  t.1.1 * t.2.1 + t.1.2 * t.2.2

/-- The four-bit gadget evaluates to zero on the all-zero vector. -/
theorem quadForm_zero : quadForm (0 : GadgetVector) = 0 := by decide

/-- A bit is `1` exactly when it is not `0`. -/
theorem quadForm_eq_one_iff (t : GadgetVector) :
    quadForm t = 1 ↔ quadForm t ≠ 0 := by
  generalize quadForm t = b
  revert b
  decide

/-- Every string of the alphabet is its own negative: `1 + 1 = 0` in `𝔽₂`,
so addition is bitwise XOR. -/
theorem gadget_add_self (t : GadgetVector) : t + t = 0 := by
  revert t
  decide

/-- Every vector of `G = V^Ω` is its own negative, coordinate by
coordinate. -/
theorem gridVector_add_self {Ω : Type*} (a : Ω → GadgetVector) : a + a = 0 := by
  funext u
  exact gadget_add_self (a u)

/-- The alphabet has `|V| = 16` strings. -/
theorem gadget_card : Fintype.card GadgetVector = 16 := by decide

/-- `|G| = 16^{|Ω|}`: over the `n × n` grid, `|G| = 16^{n²}`. -/
theorem gridVector_card (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :
    Fintype.card (Ω → GadgetVector) = 16 ^ Fintype.card Ω := by
  rw [Fintype.card_fun, gadget_card]

/-- The Boolean vector read off a vector `z ∈ G`: bit `u` is `Q(z_u)`. -/
def gadgetBits {Ω : Type*} (z : Ω → GadgetVector) (u : Ω) : Prop :=
  quadForm (z u) = 1

/-- `F_n(z) = f_n((Q(z_u))_u)`, the outer DNF applied to the bits the
gadget produces at the coordinates. -/
@[tutorial_box "def:tutorial-gadget"]
def outerFunction {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n)
    (z : (Fin n × Fin n) → GadgetVector) : Prop :=
  outerDNF ranks hn (gadgetBits z)

/-- `F_n(0) = 0`, because `Q(0) = 0` and every term of `f_n` has a
positive literal. -/
theorem outerFunction_zero {n : ℕ} (ranks : LabelOrders n) (hn : 0 < n) :
    ¬ outerFunction ranks hn 0 := by
  rintro ⟨T, hT⟩
  obtain ⟨x, hx⟩ := T.nonempty
  have hvalue := hT.1 (T.bucket, x) (mem_termPositive.mpr ⟨rfl, hx⟩)
  simp [gadgetBits, quadForm_zero] at hvalue

end DDNNFNegation
