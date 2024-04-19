/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.WellKnown

-- Porting note: I am adding these
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.RatFunc
#align_import for_mathlib.power_series

/-!
# Generalities on power series
In this file we gather some general results concerning power series.

## Main Definitions
* Given a  power series `f`, we define `divided_by_X_pow_order f` to be the power series obtained by
dividing `f` bythe largest power of `X` occurring in `f`, namely `f.order` (this is also equal to
its `X`-adic valuation, up to some type-theoretical difference).

## Main Results
We obtain instances of Dedekind domain and of normalization monoid on the power series with
coefficients in a field.
* The definition `residue_field_of_power_series` is the ring isomorphism between the residue field
of the ring of power series valued in a field `K` and `K` itself.

In the final section, we prove
* `single_pow`
* `single_inv`
* `single_zpow`
relating the powers and the inverse of the Hahn series `single 1 1` with the Hahn series
`single n 1` for `n : ℤ`.
-/


noncomputable section

-- namespace PowerSeries

-- open scoped DiscreteValuation

-- --`FAE` Became useless
-- -- theorem coeff_zero_eq_eval {K : Type _} [Semiring K] (f : PowerSeries K) :
-- --     (coeff K 0) f = f 0 := by
-- --   simp
-- --   rfl
-- --   -- simp only [coeff, Mvcoeff, LinearMap.coe_proj, Finsupp.single_zero]
-- --   exact LinearMap.proj_apply (R := K) (ι := Unit →₀ ℕ) 0 f

-- -- `FAE` in PR #12160
-- theorem order_zero_of_unit {R : Type _} [Semiring R] [Nontrivial R] {f : PowerSeries R} :
--     IsUnit f → f.order = 0 := by
--   rintro ⟨⟨u, v, hu, hv⟩, hf⟩
--   apply And.left
--   rw [← add_eq_zero_iff, ← hf, ← nonpos_iff_eq_zero, ← @order_one R _ _, ← hu]
--   exact order_mul_ge _ _

-- -- `FAE` used to be `irreducible_x`, is in PR #12160
-- theorem X_Irreducible {K : Type _} [Field K] : Irreducible (X : PowerSeries K) :=
--   Prime.irreducible X_prime

-- open DiscreteValuationRing PowerSeries

-- -- open scoped Classical

-- section Semiring

-- variable {K : Type _} [Semiring K]

-- -- `FAE` Is in PR #12160
-- /-- Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
--   dividing out the largest power of X that divides `f`, that is its order-/
-- def divided_by_X_pow_order {f : PowerSeries K} (hf : f ≠ 0) : PowerSeries K :=
--   (exists_eq_mul_right_of_dvd (X_pow_order_dvd (order_finite_iff_ne_zero.2 hf))).choose

-- -- `FAE` Is in PR #12160
-- theorem self_eq_X_pow_order_mul_divided_by_X_pow_order {f : PowerSeries K} (hf : f ≠ 0) :
--     X ^ f.order.get (order_finite_iff_ne_zero.mpr hf) * divided_by_X_pow_order hf = f :=
--   haveI dvd := X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf)
--   (exists_eq_mul_right_of_dvd dvd).choose_spec.symm

-- end Semiring

-- section Domain

-- variable {K : Type _} [CommRing K] [Nontrivial K] [IsDomain K]

-- -- `FAE` Is in PR #12160
-- @[simp]
-- theorem divided_by_X_pow_order_of_X_eq_one : divided_by_X_pow_order X_ne_zero = (1 : K⟦X⟧) := by
--   rw [← mul_eq_left₀ X_ne_zero]
--   simpa only [order_X, X_ne_zero, PartENat.get_one, pow_one,/-  mul_eq_left₀, -/ Ne.def,
--     not_false_iff] using self_eq_X_pow_order_mul_divided_by_X_pow_order (@X_ne_zero K _ _)

-- -- `FAE` Is in PR #12160
-- theorem divided_by_X_pow_orderMul {f g : PowerSeries K} (hf : f ≠ 0) (hg : g ≠ 0) :
--     divided_by_X_pow_order hf * divided_by_X_pow_order hg = divided_by_X_pow_order (mul_ne_zero hf hg) := by
--   set df := f.order.get (order_finite_iff_ne_zero.mpr hf)
--   set dg := g.order.get (order_finite_iff_ne_zero.mpr hg)
--   set dfg := (f * g).order.get (order_finite_iff_ne_zero.mpr (mul_ne_zero hf hg)) with hdfg
--   have H_add_d : df + dg = dfg := by simp_all only [PartENat.get_add, order_mul f g]
--   have H := self_eq_X_pow_order_mul_divided_by_X_pow_order (mul_ne_zero hf hg)
--   have : f * g = X ^ dfg * (divided_by_X_pow_order hf * divided_by_X_pow_order hg) := by
--     calc
--       f * g = X ^ df * divided_by_X_pow_order hf * (X ^ dg * divided_by_X_pow_order hg) := by
--         rw [self_eq_X_pow_order_mul_divided_by_X_pow_order, self_eq_X_pow_order_mul_divided_by_X_pow_order]
--       _ = X ^ df * X ^ dg * divided_by_X_pow_order hf * divided_by_X_pow_order hg := by ring
--       _ = X ^ (df + dg) * divided_by_X_pow_order hf * divided_by_X_pow_order hg := by rw [pow_add]
--       _ = X ^ dfg * divided_by_X_pow_order hf * divided_by_X_pow_order hg := by rw [H_add_d]
--       _ = X ^ dfg * (divided_by_X_pow_order hf * divided_by_X_pow_order hg) := by rw [mul_assoc]
--   simp [← hdfg, this] at H
--   refine' (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (pow_ne_zero dfg X_ne_zero) _).symm
--   convert H

-- end Domain

-- section Field

-- variable {K : Type _} [Field K]

-- -- `FAE` Is in PR #12160
-- /-- `first_unit_coeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
--   field.-/
-- def firstUnitCoeff {f : PowerSeries K} (hf : f ≠ 0) : Kˣ := by
--   set d := f.order.get (order_finite_iff_ne_zero.mpr hf)
--   have f_const : coeff K d f ≠ 0 := by apply coeff_order
--   have : Invertible (constantCoeff K (divided_by_X_pow_order hf)) := by
--     apply invertibleOfNonzero
--     convert f_const using 1
--     · rw [← coeff_zero_eq_constantCoeff, ← zero_add d]
--       convert
--       (coeff_X_pow_mul
--           (exists_eq_mul_right_of_dvd
--               (X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf))).choose
--           d 0).symm
--       exact (@self_eq_X_pow_order_mul_divided_by_X_pow_order K _ f hf).symm
--   exact unitOfInvertible (constantCoeff K (divided_by_X_pow_order hf))

-- -- `FAE` Is in PR #12160
-- /-- `divided_by_X_pow_orderInv` is the inverse of the element obtained by diving a non-zero power series
-- by the largest power of `X` dividing it. Useful to create a term of type `units` -/
-- def divided_by_X_pow_orderInv {f : PowerSeries K} (hf : f ≠ 0) : PowerSeries K :=
--   invOfUnit (divided_by_X_pow_order hf) (firstUnitCoeff hf)

-- -- `FAE` Is in PR #12160
-- theorem divided_by_X_pow_orderInv_right_inv {f : PowerSeries K} (hf : f ≠ 0) :
--     divided_by_X_pow_order hf * divided_by_X_pow_orderInv hf = 1 :=
--   mul_invOfUnit (divided_by_X_pow_order hf) (firstUnitCoeff hf) rfl

-- -- `FAE` Is in PR #12160
-- theorem divided_by_X_pow_orderInv_left_inv {f : PowerSeries K} (hf : f ≠ 0) :
--     divided_by_X_pow_orderInv hf * divided_by_X_pow_order hf = 1 := by
--   rw [mul_comm]
--   exact mul_invOfUnit (divided_by_X_pow_order hf) (firstUnitCoeff hf) rfl


-- open Classical
-- -- `FAE` Is in PR #12160
-- /-- `unit_of_divided_by_X_pow_order` is the unit of power series obtained by dividing a non-zero power
-- series by the largest power of `X` that divides it. -/
-- def unit_of_divided_by_X_pow_order (f : PowerSeries K) : (PowerSeries K)ˣ :=
--   if hf : f = 0 then 1
--   else
--     { val := divided_by_X_pow_order hf
--       inv := divided_by_X_pow_orderInv hf
--       val_inv := divided_by_X_pow_orderInv_right_inv hf
--       inv_val := divided_by_X_pow_orderInv_left_inv hf }

-- -- `FAE` Is in PR #12160
-- theorem isUnit_divided_by_X_pow_order {f : PowerSeries K} (hf : f ≠ 0) : IsUnit (divided_by_X_pow_order hf) :=
--   ⟨unit_of_divided_by_X_pow_order f, by simp only [unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]⟩

-- -- `FAE` Is in PR #12160
-- theorem unit_of_divided_by_X_pow_order_nonzero {f : PowerSeries K} (hf : f ≠ 0) :
--     ↑(unit_of_divided_by_X_pow_order f) = divided_by_X_pow_order hf := by
--   simp only [unit_of_divided_by_X_pow_order, dif_neg hf, Units.val_mk]

-- -- `FAE` Is in PR #12160
-- theorem unit_of_divided_by_X_pow_order_zero : unit_of_divided_by_X_pow_order (0 : PowerSeries K) = 1 := by
--   simp only [unit_of_divided_by_X_pow_order, dif_pos]

-- -- `FAE` Is in PR #12160
-- theorem eq_divided_by_X_iff_unit {f : PowerSeries K} (hf : f ≠ 0) :
--     f = divided_by_X_pow_order hf ↔ IsUnit f :=
--   ⟨fun h => by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h => by
--     have : f.order.get (order_finite_iff_ne_zero.mpr hf) = 0 := by
--       simp only [order_zero_of_unit h, PartENat.get_zero]
--     convert (self_eq_X_pow_order_mul_divided_by_X_pow_order hf).symm
--     simp only [this, pow_zero, one_mul]⟩

-- -- `FAE` Is in PR #12160
-- theorem hasUnitMulPowIrreducibleFactorization :
--     HasUnitMulPowIrreducibleFactorization (PowerSeries K) :=
--   ⟨X,
--     And.intro X_Irreducible
--       (by
--         intro f hf
--         use f.order.get (order_finite_iff_ne_zero.mpr hf)
--         use unit_of_divided_by_X_pow_order f
--         simp only [unit_of_divided_by_X_pow_order_nonzero hf]
--         exact self_eq_X_pow_order_mul_divided_by_X_pow_order hf)⟩

-- -- `FAE` Is in PR #12160
-- instance : UniqueFactorizationMonoid (PowerSeries K) :=
--   hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

-- -- `FAE` Is in PR #12160
-- instance : DiscreteValuationRing (PowerSeries K) :=
--   ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

-- -- `FAE` Is in PR #12160
-- instance : IsPrincipalIdealRing (PowerSeries K) :=
--   inferInstance

-- -- `FAE` Is in PR #12160
-- instance isNoetherianRing : IsNoetherianRing (PowerSeries K) :=
--   PrincipalIdealRing.isNoetherianRing

-- -- variable (K)
-- -- `FAE` Is in PR #12160
-- theorem maximalIdeal_eq_span_x :
--     LocalRing.maximalIdeal (PowerSeries K) = Ideal.span {X} := by
--   have hX : (Ideal.span {(X : PowerSeries K)}).IsMaximal := by
--     rw [Ideal.isMaximal_iff]
--     constructor
--     · rw [Ideal.mem_span_singleton]
--       exact Prime.not_dvd_one X_prime
--     intro I f hI hfX hfI
--     rw [Ideal.mem_span_singleton, X_dvd_iff] at hfX
--     have hfI0 : C K (f 0) ∈ I := by
--       have : C K (f 0) = f - (f - C K (f 0)) := by rw [sub_sub_cancel]
--       rw [this]
--       apply Ideal.sub_mem I hfI
--       apply hI
--       rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, ←
--         coeff_zero_eq_constantCoeff_apply, sub_eq_zero, coeff_zero_eq_constantCoeff]
--       rfl
--     rw [← Ideal.eq_top_iff_one]
--     apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map (C K) (Ne.isUnit hfX))
--   rw [LocalRing.eq_maximalIdeal hX]

-- -- `FAE` Is in PR #12160
-- theorem not_isField (R : Type _) [CommRing R] [Nontrivial R] : ¬IsField (PowerSeries R) := by
--   nontriviality R
--   rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
--   use Ideal.span {X}
--   constructor
--   · rw [bot_lt_iff_ne_bot, Ne.def, Ideal.span_singleton_eq_bot]
--     exact X_ne_zero
--   · rw [lt_top_iff_ne_top, Ne.def, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
--       X_dvd_iff, constantCoeff_one]
--     exact one_ne_zero

-- -- `FAE` Is in PR #12160
-- instance isDedekindDomain : IsDedekindDomain (PowerSeries K) :=
--   IsPrincipalIdealRing.isDedekindDomain (PowerSeries K)

-- -- `FAE` Is in PR #12160
-- instance : NormalizationMonoid (PowerSeries K)
--     where
--   normUnit f := (unit_of_divided_by_X_pow_order f)⁻¹
--   normUnit_zero := by simp only [unit_of_divided_by_X_pow_order_zero, inv_one]
--   normUnit_mul  := fun hf hg => by
--     simp only [← mul_inv, inv_inj]
--     simp only [unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
--       unit_of_divided_by_X_pow_order_nonzero hf, unit_of_divided_by_X_pow_order_nonzero hg, Units.ext_iff,
--       val_unitOfInvertible, Units.val_mul, divided_by_X_pow_orderMul]
--   normUnit_coe_units := by
--     intro u
--     set u₀ := u.1 with hu
--     have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
--     rw [inv_inj, Units.ext_iff, ← hu, unit_of_divided_by_X_pow_order_nonzero h₀.ne_zero]
--     exact ((eq_divided_by_X_iff_unit h₀.ne_zero).mpr h₀).symm

-- open LocalRing

-- -- `FAE` Is in PR #12160
-- theorem constantCoeff_surj (R : Type _) [CommRing R] : Function.Surjective (constantCoeff R) :=
--   fun r => ⟨(C R) r, constantCoeff_C r⟩

-- -- `FAE` Is in PR #12160
-- theorem ker_constantCoeff_eq_max_ideal : RingHom.ker (constantCoeff K) = maximalIdeal _ :=
--   Ideal.ext fun _ => by
--     rw [RingHom.mem_ker, maximalIdeal_eq_span_x, Ideal.mem_span_singleton, X_dvd_iff]

-- -- `FAE` Is in PR #12160
-- /-- The ring isomorphism between the residue field of the ring of power series valued in a field `K`
-- and `K` itself. -/
-- def residueFieldOfPowerSeries : ResidueField (PowerSeries K) ≃+* K :=
--   (Ideal.quotEquivOfEq (ker_constantCoeff_eq_max_ideal ).symm).trans
--     (RingHom.quotientKerEquivOfSurjective (constantCoeff_surj K))

-- end Field

-- end PowerSeries
-- `FAE` Stopped here while creating PR #12160

-- `FAE` What follows is in PR #12245
/-
In this final section, we prove
* `single_pow`
* `single_inv`
* `single_zpow`
relating the powers and the inverse of the Hahn series `single 1 1` with the Hahn series
`single n 1` for `n : ℤ`.
-/

section Polynomial

variable {K : Type _} [Field K]

namespace RatFunc

open PowerSeries Polynomial

-- Porting note: I added this
instance : Coe (Polynomial K) (RatFunc K) := ⟨algebraMap _ _⟩

theorem coe_coe (P : Polynomial K) : (P : LaurentSeries K) = (P : RatFunc K) := by
  erw [RatFunc.coe_def, RatFunc.coeAlgHom, liftAlgHom_apply, RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap P, map_one, div_one]
  rfl

theorem coe_ne_zero {f : Polynomial K} : f ≠ 0 → (↑f : PowerSeries K) ≠ 0 := by
  simp only [Ne.def, coe_eq_zero_iff, imp_self]

end RatFunc

end Polynomial

section HahnSeries

namespace HahnSeries

theorem single_pow {R : Type _} [Ring R] (n : ℕ) :
    HahnSeries.single (n : ℤ) (1 : R) = HahnSeries.single (1 : ℤ) 1 ^ n := by
  induction' n with n h_ind
  · simp only [Nat.zero_eq, Int.ofNat_eq_coe, ZMod.natCast_self, zpow_zero]
    rfl
  · rw [← Int.ofNat_add_one_out, pow_succ', ← h_ind, HahnSeries.single_mul_single, one_mul,
      add_comm]

variable {K : Type _} [Field K]

theorem single_inv (d : ℤ) (α : K) (hα : α ≠ 0) :
    (HahnSeries.single (d : ℤ) (α : K))⁻¹ = HahnSeries.single (-d) (α⁻¹ : K) := by
  rw [inv_eq_of_mul_eq_one_left];
  simp only [HahnSeries.single_mul_single, add_left_neg, inv_mul_cancel hα]
  rfl

theorem single_zpow (n : ℤ) :
    HahnSeries.single (n : ℤ) (1 : K) = HahnSeries.single (1 : ℤ) 1 ^ n := by
  induction' n with n_pos n_neg
  · apply single_pow
  · rw [Int.negSucc_coe, Int.ofNat_add, Nat.cast_one, ← inv_one, ←
      single_inv (n_neg + 1 : ℤ) (1 : K) one_ne_zero, zpow_neg, ← Nat.cast_one, ← Int.ofNat_add,
      Nat.cast_one, inv_inj, zpow_natCast, single_pow, inv_one]


end HahnSeries

end HahnSeries
