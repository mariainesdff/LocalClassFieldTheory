/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Extensions

#align_import discrete_valuation_ring.trivial_extension

/-!
# Trivial extensions of discrete valuations

When `K` is a complete, discretely valued field, the trivial extension of the valuation
`extended_valuation K K` is mathematically, but not definitionally, equal to the valuation on `K`.
In this file, we provide some rewrite lemmas for dealing with this trivial extension.

##  Main Theorems
* `discrete_valuation.extension.trivial_extension_eq_valuation` : the extension of the valuation on
  `K` to itself is equal to the original valuation.
-/


open AddSubgroup DiscreteValuation Polynomial Valuation WithZero

open scoped DiscreteValuation

namespace DiscreteValuation.Extension

variable {K : Type _} [Field K] [hv : Valued K ℤₘ₀] [IsDiscrete hv.v] [CompleteSpace K]

theorem trivial_powExtensionOnUnits_eq_valuation (x : Kˣ) :
    powExtensionOnUnits K K x = unzero (Valuation.unit_ne_zero hv.v x) := by
  rw [powExtensionOnUnits_apply]
  congr 1
  simp only [FiniteDimensional.finrank_self, minpoly.eq_X_sub_C', coeff_sub, coeff_X_zero,
    coeff_C_zero, zero_sub, Valuation.map_neg, natDegree_X_sub_C, Nat.div_self,
    Nat.lt_one_iff, pow_one]

variable (K)

theorem trivial_expExtensionOnUnits_eq_one : expExtensionOnUnits K K = 1 := by
  have h : zmultiples (expExtensionOnUnits K K : ℤ) = ⊤ := by
    rw [zmultiples_eq_closure, ← expExtensionOnUnits_generates_range',
      map_eq_top_iff Subgroup.toAddSubgroup]
    apply Subgroup.map_top_of_surjective
    intro z
    have hz : ∃ u : Kˣ, Valued.v (u : K) = (z : ℤₘ₀) := by
      have hd : IsDiscrete hv.v := inferInstance
      obtain ⟨k, hk⟩ := hd.surj z
      have hk0 : k ≠ 0 := by rw [Ne.def, ← Valuation.zero_iff hv.v, hk]; exact coe_ne_zero
      exact ⟨IsUnit.unit (isUnit_iff_ne_zero.mpr hk0), hk⟩
    obtain ⟨u, hu⟩ := hz
    use u
    rw [trivial_powExtensionOnUnits_eq_valuation, ← WithZero.coe_inj, ← hu, coe_unzero]
  rw [← Int.natCast_inj, Nat.cast_one]
  apply Int.eq_one_of_dvd_one (Nat.cast_nonneg _)
  rw [← Int.mem_zmultiples_iff, h]
  exact AddSubgroup.mem_top _

/-- The extension of the valuation on `K` to itself is equal to the original valuation. -/
theorem trivial_extension_eq_valuation : extendedValuation K K = hv.v := by
  ext x
  rw [Extension.apply]
  split_ifs with hx
  · rw [hx, Valuation.map_zero]
  · set u : Kˣ := (isUnit_iff_ne_zero.mpr hx).unit
    rw [← zpow_eq_pow]
    convert (exists_mul_expExtensionOnUnits K u).choose_spec
    · simp_rw [zpow_eq_pow, trivial_expExtensionOnUnits_eq_one, pow_one,
        (isUnit_iff_ne_zero.mpr hx).choose_spec]
    · simp only [FiniteDimensional.finrank_self, minpoly.eq_X_sub_C', IsUnit.unit_spec, coeff_sub,
        coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg, natDegree_X_sub_C, Nat.div_self,
        Nat.lt_one_iff, pow_one]
      rfl

end DiscreteValuation.Extension
