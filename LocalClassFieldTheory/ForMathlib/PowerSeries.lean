import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.ValuationSubring
-- import LocalClassFieldTheory.ForMathlib.DiscreteUniformity
-- import LocalClassFieldTheory.ForMathlib.Polynomial
-- import LocalClassFieldTheory.Mathlib.Algebra.Order.Hom.Monoid
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
* Given a  power series `f`, we define `divided_by_X_pow f` to be the power series obtained by
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

namespace PowerSeries

open scoped DiscreteValuation


theorem coeff_zero_eq_eval {K : Type _} [Semiring K] (f : PowerSeries K) :
    (PowerSeries.coeff K 0) f = f 0 := by
  simp only [PowerSeries.coeff, MvPowerSeries.coeff, LinearMap.coe_proj,/-  Function.eval_apply, -/
    Finsupp.single_zero]
  exact LinearMap.proj_apply (R := K) (ι := Unit →₀ ℕ) 0 f


theorem order_zero_of_unit {R : Type _} [Semiring R] [Nontrivial R] {f : PowerSeries R} :
    IsUnit f → f.order = 0 := by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero_iff, ← hf, ← nonpos_iff_eq_zero, ← @PowerSeries.order_one R _ _, ← hu]
  exact PowerSeries.order_mul_ge _ _

variable {K : Type _} [Field K]

theorem irreducible_x : Irreducible (PowerSeries.X : PowerSeries K) :=
  Prime.irreducible PowerSeries.X_prime

open DiscreteValuationRing PowerSeries

open scoped Classical

/-- Given a non-zero power series `f`, this is the power series obtained by dividing out the largest
  power of X that divides `f`-/
def divided_by_X_pow {f : PowerSeries K} (hf : f ≠ 0) : PowerSeries K :=
  (exists_eq_mul_right_of_dvd (PowerSeries.X_pow_order_dvd (order_finite_iff_ne_zero.2 hf))).choose

theorem self_eq_X_pow_mul_divided_by_X_pow {f : PowerSeries K} (hf : f ≠ 0) :
    X ^ f.order.get (order_finite_iff_ne_zero.mpr hf) * divided_by_X_pow hf = f :=
  haveI dvd := PowerSeries.X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf)
  (exists_eq_mul_right_of_dvd dvd).choose_spec.symm

@[simp]
theorem divided_by_X_pow_of_X_eq_one : divided_by_X_pow (@X_ne_zero K _ _) = 1 := by
  simpa only [order_X, X_ne_zero, PartENat.get_one, pow_one, mul_eq_left₀, Ne.def,
    not_false_iff] using self_eq_X_pow_mul_divided_by_X_pow (@X_ne_zero K _ _)

theorem divided_by_X_powMul {f g : PowerSeries K} (hf : f ≠ 0) (hg : g ≠ 0) :
    divided_by_X_pow hf * divided_by_X_pow hg = divided_by_X_pow (mul_ne_zero hf hg) := by
  set df := f.order.get (order_finite_iff_ne_zero.mpr hf)
  set dg := g.order.get (order_finite_iff_ne_zero.mpr hg)
  set dfg := (f * g).order.get (order_finite_iff_ne_zero.mpr (mul_ne_zero hf hg)) with hdfg
  have H_add_d : df + dg = dfg := by sorry--simp only [PartENat.get_add, order_mul f g]
  have H := self_eq_X_pow_mul_divided_by_X_pow (mul_ne_zero hf hg)
  have : f * g = X ^ dfg * (divided_by_X_pow hf * divided_by_X_pow hg) := by
    calc
      f * g = X ^ df * divided_by_X_pow hf * (X ^ dg * divided_by_X_pow hg) := by
        sorry--simp only [self_eq_X_pow_mul_divided_by_X_pow]
      _ = X ^ df * X ^ dg * divided_by_X_pow hf * divided_by_X_pow hg := by ring
      _ = X ^ (df + dg) * divided_by_X_pow hf * divided_by_X_pow hg := by rw [pow_add]
      _ = X ^ dfg * divided_by_X_pow hf * divided_by_X_pow hg := by rw [H_add_d]
      _ = X ^ dfg * (divided_by_X_pow hf * divided_by_X_pow hg) := by rw [mul_assoc]
  simp [← hdfg, this] at H
  refine' (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (pow_ne_zero dfg X_ne_zero) _).symm
  convert H


/-- `first_unit_coeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
  field.-/
def firstUnitCoeff {f : PowerSeries K} (hf : f ≠ 0) : Kˣ := by
  set d := f.order.get (PowerSeries.order_finite_iff_ne_zero.mpr hf)
  have f_const : PowerSeries.coeff K d f ≠ 0 := by apply PowerSeries.coeff_order
  have : Invertible (PowerSeries.constantCoeff K (divided_by_X_pow hf)) := by
    apply invertibleOfNonzero
    convert f_const using 1
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← zero_add d]
      convert
      (PowerSeries.coeff_X_pow_mul
          (exists_eq_mul_right_of_dvd
              (PowerSeries.X_pow_order_dvd (PowerSeries.order_finite_iff_ne_zero.mpr hf))).choose
          d 0).symm
      exact (@self_eq_X_pow_mul_divided_by_X_pow K _ f hf).symm
  exact unitOfInvertible (PowerSeries.constantCoeff K (divided_by_X_pow hf))

/-- `divided_by_X_powInv` is the inverse of the element obtained by diving a non-zero power series
by the largest power of `X` dividing it. Useful to create a term of type `units` -/
def divided_by_X_powInv {f : PowerSeries K} (hf : f ≠ 0) : PowerSeries K :=
  PowerSeries.invOfUnit (divided_by_X_pow hf) (firstUnitCoeff hf)

theorem divided_by_X_powInv_right_inv {f : PowerSeries K} (hf : f ≠ 0) :
    divided_by_X_pow hf * divided_by_X_powInv hf = 1 :=
  mul_invOfUnit (divided_by_X_pow hf) (firstUnitCoeff hf) rfl

theorem divided_by_X_powInv_left_inv {f : PowerSeries K} (hf : f ≠ 0) :
    divided_by_X_powInv hf * divided_by_X_pow hf = 1 := by
  rw [mul_comm]
  exact mul_invOfUnit (divided_by_X_pow hf) (firstUnitCoeff hf) rfl

/-- `unit_of_divided_by_X_pow` is the unit of power series obtained by dividing a non-zero power
series by the largest power of `X` that divides it. -/
def unit_of_divided_by_X_pow (f : PowerSeries K) : (PowerSeries K)ˣ :=
  if hf : f = 0 then 1
  else
    { val := divided_by_X_pow hf
      inv := divided_by_X_powInv hf
      val_inv := divided_by_X_powInv_right_inv hf
      inv_val := divided_by_X_powInv_left_inv hf }

theorem isUnit_divided_by_X_pow {f : PowerSeries K} (hf : f ≠ 0) : IsUnit (divided_by_X_pow hf) :=
  ⟨unit_of_divided_by_X_pow f, by simp only [unit_of_divided_by_X_pow, dif_neg hf, Units.val_mk]⟩

theorem unit_of_divided_by_X_pow_nonzero {f : PowerSeries K} (hf : f ≠ 0) :
    ↑(unit_of_divided_by_X_pow f) = divided_by_X_pow hf := by
  simp only [unit_of_divided_by_X_pow, dif_neg hf, Units.val_mk]

theorem unit_of_divided_by_X_pow_zero : unit_of_divided_by_X_pow (0 : PowerSeries K) = 1 := by
  simp only [unit_of_divided_by_X_pow, dif_pos]

theorem eq_divided_by_X_iff_unit {f : PowerSeries K} (hf : f ≠ 0) :
    f = divided_by_X_pow hf ↔ IsUnit f :=
  ⟨fun h => by rw [h]; exact isUnit_divided_by_X_pow hf, fun h => by
    have : f.order.get (order_finite_iff_ne_zero.mpr hf) = 0 := by
      simp only [order_zero_of_unit h, PartENat.get_zero]
    convert (self_eq_X_pow_mul_divided_by_X_pow hf).symm
    simp only [this, pow_zero, one_mul]⟩

theorem hasUnitMulPowIrreducibleFactorization :
    HasUnitMulPowIrreducibleFactorization (PowerSeries K) :=
  ⟨PowerSeries.X,
    And.intro PowerSeries.irreducible_x
      (by
        intro f hf
        use f.order.get (PowerSeries.order_finite_iff_ne_zero.mpr hf)
        use unit_of_divided_by_X_pow f
        simp only [unit_of_divided_by_X_pow_nonzero hf]
        exact self_eq_X_pow_mul_divided_by_X_pow hf)⟩

instance : UniqueFactorizationMonoid (PowerSeries K) :=
  hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

instance : DiscreteValuationRing (PowerSeries K) :=
  ofHasUnitMulPowIrreducibleFactorization PowerSeries.hasUnitMulPowIrreducibleFactorization

instance : IsPrincipalIdealRing (PowerSeries K) :=
  inferInstance

instance isNoetherianRing : IsNoetherianRing (PowerSeries K) :=
  PrincipalIdealRing.isNoetherianRing

variable (K)

theorem maximalIdeal_eq_span_x :
    LocalRing.maximalIdeal (PowerSeries K) = Ideal.span {PowerSeries.X} := by
  have hX : (Ideal.span {(PowerSeries.X : PowerSeries K)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one PowerSeries.X_prime
    intro I f hI hfX hfI
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hfX
    have hfI0 : PowerSeries.C K (f 0) ∈ I := by
      have : PowerSeries.C K (f 0) = f - (f - PowerSeries.C K (f 0)) := by rw [sub_sub_cancel]
      rw [this]
      apply Ideal.sub_mem I hfI
      apply hI
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, ←
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_eval, sub_eq_zero]
    rw [← Ideal.eq_top_iff_one]
    apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map (PowerSeries.C K) (Ne.isUnit hfX))
  rw [LocalRing.eq_maximalIdeal hX]

theorem not_isField (R : Type _) [CommRing R] [Nontrivial R] : ¬IsField (PowerSeries R) := by
  nontriviality R
  rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  use Ideal.span {PowerSeries.X}
  constructor
  · rw [bot_lt_iff_ne_bot, Ne.def, Ideal.span_singleton_eq_bot]
    exact PowerSeries.X_ne_zero
  · rw [lt_top_iff_ne_top, Ne.def, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_one]
    exact one_ne_zero

instance isDedekindDomain : IsDedekindDomain (PowerSeries K) :=
  IsPrincipalIdealRing.isDedekindDomain (PowerSeries K)

instance : NormalizationMonoid (PowerSeries K)
    where
  normUnit f := (unit_of_divided_by_X_pow f)⁻¹
  normUnit_zero := by simp only [unit_of_divided_by_X_pow_zero, inv_one]
  normUnit_mul  := fun hf hg => by
    simp only [← mul_inv, inv_inj]
    simp only [unit_of_divided_by_X_pow_nonzero (mul_ne_zero hf hg),
      unit_of_divided_by_X_pow_nonzero hf, unit_of_divided_by_X_pow_nonzero hg, Units.ext_iff,
      val_unitOfInvertible, Units.val_mul, divided_by_X_powMul]
  normUnit_coe_units := by
    intro u
    set u₀ := u.1 with hu
    have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
    rw [inv_inj, Units.ext_iff, ← hu, unit_of_divided_by_X_pow_nonzero h₀.ne_zero]
    exact ((eq_divided_by_X_iff_unit h₀.ne_zero).mpr h₀).symm

open LocalRing

theorem constantCoeff_surj (R : Type _) [CommRing R] : Function.Surjective (constantCoeff R) :=
  fun r => ⟨(C R) r, constantCoeff_C r⟩

theorem ker_constantCoeff_eq_max_ideal : RingHom.ker (constantCoeff K) = maximalIdeal _ :=
  Ideal.ext fun _ => by
    rw [RingHom.mem_ker, PowerSeries.maximalIdeal_eq_span_x K, Ideal.mem_span_singleton, X_dvd_iff]

/-- The ring isomorphism between the residue field of the ring of power series valued in a field `K`
and `K` itself. -/
def residueFieldOfPowerSeries : ResidueField (PowerSeries K) ≃+* K :=
  (Ideal.quotEquivOfEq (ker_constantCoeff_eq_max_ideal K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (constantCoeff_surj K))

end PowerSeries

variable {K : Type _} [Field K]

namespace Polynomial

open RatFunc PowerSeries

-- Porting note: I added this
instance : Coe (Polynomial K) (RatFunc K) := ⟨algebraMap _ _⟩

theorem coe_coe (P : Polynomial K) : (P : LaurentSeries K) = (P : RatFunc K) := by
  erw [RatFunc.coe_def, RatFunc.coeAlgHom, liftAlgHom_apply, RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap P, map_one, div_one]
  rfl

theorem coe_ne_zero {f : Polynomial K} : f ≠ 0 → (↑f : PowerSeries K) ≠ 0 := by
  simp only [Ne.def, coe_eq_zero_iff, imp_self]

end Polynomial

namespace HahnSeries

theorem single_pow {R : Type _} [Ring R] (n : ℕ) :
    HahnSeries.single (n : ℤ) (1 : R) = HahnSeries.single (1 : ℤ) 1 ^ n := by
  induction' n with n h_ind
  · simp only [Nat.zero_eq, Int.ofNat_eq_coe, ZMod.nat_cast_self, zpow_zero]
    rfl
  · rw [← Int.ofNat_add_one_out, ← one_mul (1 : R), ← HahnSeries.single_mul_single, h_ind,
      pow_succ', one_mul (1 : R)]

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
      Nat.cast_one, inv_inj, zpow_coe_nat, single_pow, inv_one]

end HahnSeries
