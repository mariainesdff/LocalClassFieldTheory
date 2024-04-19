/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import LocalClassFieldTheory.FromMathlib.NormedValued

#align_import for_mathlib.rank_one_valuation

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


open scoped DiscreteValuation

namespace RankOneValuation

variable {L : Type _} [Field L] [Valued L ℤₘ₀] [hv : IsRankOne (@Valued.v L _ ℤₘ₀ _ _)]

theorem norm_le_one_iff_val_le_one (x : L) :
    RankOneValuation.normDef x ≤ 1 ↔ Valued.v x ≤ (1 : ℤₘ₀) :=
  by
  have hx : RankOneValuation.normDef x = hv.hom (Valued.v x) := rfl
  rw [hx, ← NNReal.coe_one, NNReal.coe_le_coe, ← map_one (IsRankOne.hom (@Valued.v L _ ℤₘ₀ _ _)),
    StrictMono.le_iff_le]
  exact IsRankOne.strictMono

theorem norm_lt_one_iff_val_lt_one (x : L) :
    RankOneValuation.normDef x < 1 ↔ Valued.v x < (1 : ℤₘ₀) :=
  by
  have hx : RankOneValuation.normDef x = hv.hom (Valued.v x) := rfl
  rw [hx, ← NNReal.coe_one, NNReal.coe_lt_coe, ← map_one (IsRankOne.hom (@Valued.v L _ ℤₘ₀ _ _)),
    StrictMono.lt_iff_lt]
  exact IsRankOne.strictMono

theorem norm_pos_iff_val_pos (x : L) : 0 < RankOneValuation.normDef x ↔ (0 : ℤₘ₀) < Valued.v x :=
  by
  have hx : RankOneValuation.normDef x = hv.hom (Valued.v x) := rfl
  rw [hx, ← NNReal.coe_zero, NNReal.coe_lt_coe, ← map_zero (IsRankOne.hom (@Valued.v L _ ℤₘ₀ _ _)),
    StrictMono.lt_iff_lt]
  exact IsRankOne.strictMono

end RankOneValuation

namespace RankOneValuation

variable (L : Type _) [Field L] (Γ₀ : Type _) [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : IsRankOne val.v]

theorem normDef_isNonarchimedean : IsNonarchimedean (@normDef L _ Γ₀ _ val hv) :=
  normDef_add_le

/-- If `L` is a valued field with respect to a rank one valuation, `mul_ring_norm_def` is the
  multiplicative norm on `L` induced by this valuation. -/
def mulRingNormDef : MulRingNorm L where
  toFun := normDef
  map_zero' := by simp only [normDef, map_zero, Nonneg.coe_zero, NNReal.coe_zero]
  add_le' x y := add_le_of_isNonarchimedean normDef_nonneg (normDef_isNonarchimedean L Γ₀) x y
  neg' x := by simp only [normDef, Valuation.map_neg]
  map_one' := by simp only [normDef, map_one, Nonneg.coe_one, NNReal.coe_one]
  map_mul' x y := by simp only [normDef, map_mul, Nonneg.coe_mul,NNReal.coe_mul]
  eq_zero_of_map_eq_zero' x := normDef_eq_zero

end RankOneValuation

namespace IsDedekindDomain.HeightOneSpectrum

theorem intValuation_apply {R : Type _} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) {r : R} : intValuation v r = intValuationDef v r :=
  refl _

end IsDedekindDomain.HeightOneSpectrum
