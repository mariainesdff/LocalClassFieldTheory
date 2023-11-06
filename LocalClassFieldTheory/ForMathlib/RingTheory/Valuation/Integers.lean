import Mathlib.RingTheory.Valuation.Integers

#align_import for_mathlib.ring_theory.valuation.integers

/-!
# Valutation of units

The main result of this file, `valuation_one_of_isUnit` is a generalization of
`valuation.integers.one_of_is_unit` with a slightly weaker assumption

-/


namespace Valuation

variable {R : Type _} {Γ₀ : Type _} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

variable {v : Valuation R Γ₀} {O : Type _} [CommRing O] [Algebra O R]

theorem valuation_one_of_isUnit {x : O} (hx : IsUnit x) (hv : ∀ x, v (algebraMap O R x) ≤ 1) :
    v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx
  le_antisymm (hv _) <|
    by
    rw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul]
    exact mul_le_mul_left' (hv (u⁻¹ : Units O)) _

end Valuation
