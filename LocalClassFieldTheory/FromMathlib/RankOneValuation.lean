/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.Real.NNReal
import Mathlib.RingTheory.Valuation.Basic

#align_import from_mathlib.rank_one_valuation

/-!
# Rank one valuations

We define rank one valuations and discrete valuations

## Main Definitions
* `IsRankOne` : A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.

## Tags

valuation, rank one, discrete, with_zero
-/


noncomputable section

open Function Multiplicative

open scoped NNReal

variable {R : Type _} [Ring R] {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀]

theorem mult_withTop_R_zero :
    Multiplicative.ofAdd (OrderDual.toDual ⊤) = (0 : Multiplicative (WithTop ℝ)ᵒᵈ) :=
  rfl

section IsRankOne

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`. -/
class IsRankOne (v : Valuation R Γ₀) where
  hom : Γ₀ →*₀ ℝ≥0
  strictMono : StrictMono hom
  nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `is_rank_one.hom v`, then
  `x = 0`. -/
theorem zero_of_isRankOne_hom_zero (v : Valuation R Γ₀) [IsRankOne v] {x : Γ₀}
    (hx : IsRankOne.hom v x = 0) : x = 0 := by
  have hx0 : 0 ≤ x := zero_le'
  cases' le_iff_lt_or_eq.mp hx0 with h_lt h_eq
  · have hs := @IsRankOne.strictMono _ _ _ _ v _ _ _ h_lt
    rw [map_zero, hx] at hs
    exact absurd hs not_lt_zero'
  · exact h_eq.symm

/-- If `v` is a rank one valuation, then`x : Γ₀` has image `0` under `is_rank_one.hom v` if and
  only if `x = 0`. -/
theorem isRankOne_hom_eq_zero_iff (v : Valuation R Γ₀) [hv : IsRankOne v] {x : Γ₀} :
    IsRankOne.hom v x = 0 ↔ x = 0 :=
  ⟨fun h => zero_of_isRankOne_hom_zero v h, fun h => by rw [h, map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one valuation `v : valuation R Γ₀`. -/
def isRankOneUnit (v : Valuation R Γ₀) [hv : IsRankOne v] : Γ₀ˣ :=
  Units.mk0 (v (Classical.choose hv.nontrivial)) (Classical.choose_spec hv.nontrivial).1

/-- A proof that `is_rank_one_unit v ≠ 1`. -/
theorem isRankOneUnit_ne_one (v : Valuation R Γ₀) [hv : IsRankOne v] : isRankOneUnit v ≠ 1 := by
  rw [Ne.def, ← Units.eq_iff, Units.val_one]
  exact (Classical.choose_spec hv.nontrivial).2

end IsRankOne

-- In this section, we develop some API for `with_zero`, to be PR'd to mathlib.
namespace WithZero

variable {G H : Type _}

/-- A term of `G` that represents a nonzero term of `with_zero G`. -/
def some {x : WithZero G} (hx : x ≠ 0) : G :=
  Classical.choose (ne_zero_iff_exists.mp hx)

theorem some_spec {x : WithZero G} (hx : x ≠ 0) : ↑(some hx) = x :=
  Classical.choose_spec (ne_zero_iff_exists.mp hx)

@[simp]
theorem some_coe {g : G} : some (@coe_ne_zero G g) = g :=
  coe_inj.mp (Classical.choose_spec (ne_zero_iff_exists.mp (@coe_ne_zero G g)))

/-- If `G` is a monoid and `x y : with_zero G` have a nonzero product, then
  `some hxy = some (left_ne_zero_of_mul hxy) * some (right_ne_zero_of_mul hxy)`  -/
theorem some_hMul [Monoid G] {x y : WithZero G} (hxy : x * y ≠ 0) :
    some hxy = some (left_ne_zero_of_mul hxy) * some (right_ne_zero_of_mul hxy) := by
  rw [← coe_inj, coe_mul, some_spec, some_spec, some_spec]

/-- The monoid_with_zero homomorphism `with_zero G →* with_zero H` induced by a monoid homomorphism
  `f : G →* H`. -/
def coeMonoidHom [Monoid G] [Monoid H] (f : G →* H) [DecidableEq (WithZero G)] :
    WithZero G →*₀ WithZero H
    where
  toFun x := if hx : x = 0 then 0 else f (some hx)
  map_zero' := by simp only [dif_pos]
  map_one' := by
    have h1 : (1 : WithZero G) ≠ 0 := one_ne_zero
    have h := Classical.choose_spec (ne_zero_iff_exists.mp h1)
    simp only [dif_neg h1]
    simp_rw [← coe_one] at h ⊢
    rw [coe_inj, some_coe, f.map_one]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · simp only [dif_pos hxy]
      cases' zero_eq_mul.mp (Eq.symm hxy) with hx hy
      · rw [dif_pos hx, MulZeroClass.zero_mul]
      · rw [dif_pos hy, MulZeroClass.mul_zero]
    · simp only
      rw [dif_neg hxy, dif_neg (left_ne_zero_of_mul hxy), dif_neg (right_ne_zero_of_mul hxy), ←
        coe_mul, coe_inj, ← f.map_mul, some_hMul hxy]

end WithZero
