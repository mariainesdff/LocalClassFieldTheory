/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Rank one valuations

We introduce some lemmas relating the values of a rank one valuation and of the norm it induces.

Let `L` be a valued field whose valuation has rank one.

## Main Definitions

* `mul_ring_norm_def` : the multiplicative ring norm induced by a rank one valuation on a field.


## Main Results

* `norm_le_one_iff_val_le_one` : the norm of `x : L` is `≤ 1` if and only if the valuation of `x`
  is `≤ 1`.
* `norm_lt_one_iff_val_lt_one` : the norm of `x : L` is `< 1` if and only if the valuation of `x`
  is `< 1`.
* `norm_pos_iff_val_pos` : `x ; L` has positive norm if and only if it has positive valuation.


## Tags

valuation, rank_one_valuation
-/

open NNReal Valuation

open scoped Multiplicative

namespace RankOneValuation

variable {L : Type*} [Field L] [Valued L ℤₘ₀] [hv : RankOne (Valued.v (R := L))]

-- theorem norm_le_one_iff_val_le_one (x : L) : Valued.norm x ≤ 1 ↔ Valued.v x ≤ (1 : ℤₘ₀) := by
--   exact toNormedField.norm_le_one_iff

-- theorem norm_lt_one_iff_val_lt_one (x : L) : Valued.norm x < 1 ↔ Valued.v x < (1 : ℤₘ₀) := by
--   exact toNormedField.norm_lt_one_iff

-- In **#23277**
theorem norm_pos_iff_val_pos (x : L) : 0 < Valued.norm x ↔ (0 : ℤₘ₀) < Valued.v x := by
  erw [← coe_zero, coe_lt_coe, ← map_zero (RankOne.hom (Valued.v (R := L))),
    StrictMono.lt_iff_lt]
  exact RankOne.strictMono Valued.v

end RankOneValuation

-- namespace Valued

-- variable (L : Type _) [Field L] (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀]
--   [val : Valued L Γ₀] [hv : RankOne val.v]

-- theorem norm_isNonarchimedean : IsNonarchimedean (norm (hv := hv)) := norm_add_le

-- *Outdated*
/- If `L` is a valued field with respect to a rank one valuation, `mulRingNormDef` is the
  multiplicative norm on `L` induced by this valuation. -/
-- def mulRingNormDef : MulRingNorm L where
--   toFun        := norm
--   map_zero'    := by simp only [norm, _root_.map_zero, coe_zero, coe_zero]
--   add_le' x y  := IsNonarchimedean.add_le norm_nonneg (norm_isNonarchimedean _ _)
--   neg' x       := by simp only [norm, Valuation.map_neg]
--   map_one'     := by simp only [norm, _root_.map_one, coe_one, coe_one]
--   map_mul' x y := by simp only [norm, _root_.map_mul, Nonneg.coe_mul, NNReal.coe_mul]
--   eq_zero_of_map_eq_zero' x := norm_eq_zero

-- end Valued

--PR'd in #13064
-- namespace IsDedekindDomain.HeightOneSpectrum

-- theorem intValuation_apply {R : Type _} [CommRing R] [IsDomain R] [IsDedekindDomain R]
--     (v : IsDedekindDomain.HeightOneSpectrum R) {r : R} : intValuation v r = intValuationDef v r :=
--   refl _

-- end IsDedekindDomain.HeightOneSpectrum

#min_imports
