/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.CharP.Subring
import Mathlib.FieldTheory.Finite.GaloisField
import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.LaurentSeriesEquivAdicCompletion
import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.RankOne

#align_import eq_characteristic.basic

/-!
# Equal characteristic local fields

In this file we focus on the `X`-adic completion `FpX_completion` of the ring of rational functions
over the finite field `𝔽_[p]` and we define an equal characteristic local field as a finite
extension of `FpX_completion`.

## Main Definitions
* `FpX_completion` is the adic completion of the rational functions `𝔽_p(X)`.
* `FpX_int_completion` is the unit ball in the adic completion of the rational functions `𝔽_p(X)`.
* `isomLaurent` is the ring isomorphism `(LaurentSeries 𝔽_[p]) ≃+* FpX_completion`
* `integers_equiv_power_series` is the isomorphism `(power_series 𝔽_[p]) ≃+* FpX_int_completion`.
* `eq_char_local_field` defines an equal characteristic local field as a finite dimensional
FpX_completion`-algebra for some prime number `p`.

##  Main Theorems
* `residue_field_card_eq_char` stated the the (natural) cardinality of the residue field of
  `FpX_completion` is `p`.
* For the comparison between the `valued` structures on `FpX_completion` (as adic completion)
  and on `(laurent_series 𝔽_[p])` (coming from its `X`-adic valuation), see `valuation_compare` in
  `power_series_adic_completion`.
* We record as an `instance` that `FpX_completion` itself is an equal characteristic local
  field and that its `ring_of_integers` is isomorphic to `FpX_int_completion` :=
-/


noncomputable section

open scoped DiscreteValuation

open Polynomial Multiplicative RatFunc IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  RankOneValuation Valuation ValuationSubring

variable (p : ℕ) [Fact (Nat.Prime p)]

notation3 "𝔽_[" p "]" => GaloisField p 1

/-- `FpX_completion` is the adic completion of the rational functions `𝔽_p(X)`. -/
@[reducible]
def FpXCompletion :=
  (idealX 𝔽_[p]).adicCompletion (RatFunc 𝔽_[p])

/-- `FpX_int_completion` is the unit ball in the adic completion of the rational functions
`𝔽_p(X)`. -/
@[reducible]
def FpXIntCompletion :=
  (idealX 𝔽_[p]).adicCompletionIntegers (RatFunc 𝔽_[p])

open PowerSeries GaloisField

instance : Fintype (LocalRing.ResidueField (PowerSeries 𝔽_[p])) :=
  Fintype.ofEquiv _ (residueFieldOfPowerSeries).toEquiv.symm

instance RatFunc.charP : CharP (RatFunc 𝔽_[p]) p :=
  charP_of_injective_algebraMap (algebraMap 𝔽_[p] (RatFunc 𝔽_[p])).injective p

namespace FpXCompletion

variable {p}

instance : Coe (RatFunc 𝔽_[p]) (FpXCompletion p) :=
  ⟨algebraMap (RatFunc 𝔽_[p]) (FpXCompletion p)⟩

theorem algebraMap_eq_coe (f : RatFunc 𝔽_[p]) :
    algebraMap (RatFunc 𝔽_[p]) (FpXCompletion p) f = Coe.coe f :=
  rfl

instance charP : CharP (FpXCompletion p) p :=
  charP_of_injective_algebraMap (algebraMap (RatFunc (GaloisField p 1)) (FpXCompletion p)).injective
    p

/-- The `valued` structure on the adic completion `FpX_completion`. -/
def WithZero.valued : Valued (FpXCompletion p) ℤₘ₀ :=
  HeightOneSpectrum.valuedAdicCompletion (RatFunc 𝔽_[p]) (Polynomial.idealX 𝔽_[p])

theorem valuation_X :
    Valued.v ((algebraMap (RatFunc (GaloisField p 1)) (FpXCompletion p)) X) = ofAdd (-1 : ℤ) := by
  erw [valuedAdicCompletion_def, FpXCompletion.algebraMap_eq_coe, Valued.extension_extends,
    val_X_eq_neg_one]

theorem mem_FpXIntCompletion {x : FpXCompletion p} :
    x ∈ FpXIntCompletion p ↔ (Valued.v x : ℤₘ₀) ≤ 1 :=
  Iff.rfl

theorem X_mem_FpXIntCompletion : algebraMap (RatFunc 𝔽_[p]) _ X ∈ FpXIntCompletion p := by
  erw [FpXCompletion.mem_FpXIntCompletion, FpXCompletion.valuation_X, ← WithZero.coe_one,
    WithZero.coe_le_coe, ← ofAdd_zero, ofAdd_le]
  linarith

instance : Inhabited (FpXCompletion p) :=
  ⟨(0 : FpXCompletion p)⟩

instance : RankOne (@FpXCompletion.WithZero.valued p _).v :=
  DiscreteValuation.rankOne Valued.v

instance : NormedField (FpXCompletion p) :=
  Valued.toNormedField (FpXCompletion p) ℤₘ₀

theorem mem_FpX_int_completion' {x : FpXCompletion p} : x ∈ FpXIntCompletion p ↔ ‖x‖ ≤ 1 := by
  erw [FpXCompletion.mem_FpXIntCompletion, norm_le_one_iff_val_le_one]

variable (p)

/-- `isomLaurent` is the ring isomorphism `FpX_completion ≃+* (LaurentSeries 𝔽_[p])`. -/
def isomLaurent : LaurentSeries 𝔽_[p] ≃+* FpXCompletion p :=
  sorry --CompletionLaurentSeries.LaurentSeriesRingEquiv 𝔽_[p]

end FpXCompletion

namespace FpXIntCompletion

/-- `integers_equiv_power_series` is the ring isomorphism `(power_series 𝔽_[p])` ≃+*
  `FpX_int_completion`. -/
noncomputable def integers_equiv_powerSeries : PowerSeries 𝔽_[p] ≃+* FpXIntCompletion p :=
  sorry --CompletionLaurentSeries.powerSeriesRingEquiv 𝔽_[p]

theorem residueField_powerSeries_card :
    Fintype.card (LocalRing.ResidueField (PowerSeries 𝔽_[p])) = p := by
  convert Fintype.ofEquiv_card (residueFieldOfPowerSeries).toEquiv.symm
  rw [GaloisField.card p 1 one_ne_zero, pow_one]

variable {p}

theorem residueField_card_eq_char :
    Nat.card (LocalRing.ResidueField (FpXIntCompletion p)) = p := by
  simp only [← Nat.card_congr
    (LocalRing.ResidueField.mapEquiv (integers_equiv_powerSeries p)).toEquiv,
    Nat.card_eq_fintype_card, residueField_powerSeries_card p]

variable (p)

noncomputable instance : Fintype (LocalRing.ResidueField (FpXIntCompletion p)) :=
  Fintype.ofEquiv _ (LocalRing.ResidueField.mapEquiv (integers_equiv_powerSeries p)).toEquiv

/-- The `fintype` structure on the residue field of `FpX_int_completion`. -/
noncomputable def residueFieldFintypeOfCompletion :
    Fintype (LocalRing.ResidueField (FpXIntCompletion p)) :=
  inferInstance

lemma residueFieldFiniteOfCompletion :
    Finite (LocalRing.ResidueField (FpXIntCompletion p)) := Finite.of_fintype _

end FpXIntCompletion

namespace FpXCompletion

theorem valuation_base_eq_char : Valuation.base (FpXCompletion p) Valued.v = p := by
  rw [Valuation.base, if_pos]
  · exact Nat.cast_inj.mpr FpXIntCompletion.residueField_card_eq_char
  · erw [FpXIntCompletion.residueField_card_eq_char]
    exact Nat.Prime.one_lt Fact.out

end FpXCompletion

namespace FpXIntCompletion

variable {p}

instance : DiscreteValuationRing (FpXIntCompletion p) :=
  DiscreteValuation.dvr_of_isDiscrete _

instance : Algebra (FpXIntCompletion p) (FpXCompletion p) :=
  (by infer_instance :
    Algebra ((Polynomial.idealX 𝔽_[p]).adicCompletionIntegers (RatFunc 𝔽_[p]))
      ((Polynomial.idealX 𝔽_[p]).adicCompletion (RatFunc 𝔽_[p])))

instance : Coe (FpXIntCompletion p) (FpXCompletion p) :=
  ⟨algebraMap _ _⟩

theorem algebraMap_eq_coe (x : FpXIntCompletion p) :
    algebraMap (FpXIntCompletion p) (FpXCompletion p) x = x :=
  rfl

instance isFractionRing : IsFractionRing (FpXIntCompletion p) (FpXCompletion p) :=
  (by infer_instance :
    IsFractionRing ((Polynomial.idealX 𝔽_[p]).adicCompletionIntegers (RatFunc 𝔽_[p]))
      ((Polynomial.idealX 𝔽_[p]).adicCompletion (RatFunc 𝔽_[p])))

variable (p)

instance : IsIntegralClosure (FpXIntCompletion p) (FpXIntCompletion p) (FpXCompletion p) :=
  IsIntegrallyClosed.instIsIntegralClosure

/-- `FpX_int_completions.X` is the polynomial variable `X : ratfunc 𝔽_[p]`, first coerced to the
completion `FpX_completion` and then regarded as an integral element using the bound on its norm.-/
def X : FpXIntCompletion p :=
  ⟨algebraMap (RatFunc 𝔽_[p]) _ RatFunc.X, FpXCompletion.X_mem_FpXIntCompletion⟩

end FpXIntCompletion

namespace FpXCompletion

/-- `FpX_completions.X` is the image of `FpX_int_completions.X` along the `algebra_map` given by the
embedding of the ring of integers in the whole space `FpX_completion` The next lemma shows that this
is simply the coercion of `X : ratfunc 𝔽_[p]` to its adic completion `FpX_completion`. -/
def X :=
  algebraMap (FpXIntCompletion p) (FpXCompletion p) (FpXIntCompletion.X p)

theorem X_eq_coe : X p = ↑(@RatFunc.X 𝔽_[p] _ _) :=
  rfl

theorem norm_X : ‖X p‖ = 1 / (p : ℝ) := by
  have hv : Valued.v (X p) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [← val_X_eq_neg_one 𝔽_[p], HeightOneSpectrum.valuedAdicCompletion_def,
      FpXCompletion.X_eq_coe]
    erw [Valued.extension_extends]
    rfl
  have hX : ‖X p‖ = RankOne.hom _ (Valued.v (X p)) := rfl
  rw [hX, hv, DiscreteValuation.rankOne_hom_def]
  simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, map_inv₀, NNReal.coe_inv, one_div, inv_inj]
  --simp only [ofAdd_neg, WithZero.coe_inv, map_inv₀, Nonneg.coe_inv, one_div, inv_inj]
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    withZeroMultIntToNNRealDef, WithZero.coe_ne_zero, ↓reduceDite, WithZero.unzero_coe, toAdd_ofAdd,
    zpow_one]
  rw [valuation_base_eq_char, NNReal.coe_natCast]

variable {p}

theorem norm_X_pos : 0 < ‖X p‖ := by
  rw [norm_X, one_div, inv_pos, Nat.cast_pos]; exact (Nat.Prime.pos Fact.out)

theorem norm_X_lt_one : ‖X p‖ < 1 := by
  rw [norm_X, one_div]; exact inv_lt_one (Nat.one_lt_cast.mpr (Nat.Prime.one_lt Fact.out))

instance : NontriviallyNormedField (FpXCompletion p) :=
  { (by infer_instance : NormedField (FpXCompletion p)) with
    non_trivial := by
      use(X p)⁻¹
      rw [norm_inv]
      exact one_lt_inv norm_X_pos norm_X_lt_one }

theorem X_mem_int_completion : X p ∈ FpXIntCompletion p := by
  rw [mem_FpXIntCompletion, ← norm_le_one_iff_val_le_one]
  exact le_of_lt norm_X_lt_one

theorem norm_isNonarchimedean : IsNonarchimedean (norm : FpXCompletion p → ℝ) :=
  Valued.norm_isNonarchimedean _ _

end FpXCompletion

namespace FpXIntCompletion

theorem X_ne_zero : FpXIntCompletion.X p ≠ 0 := by
  have h0 : (0 : FpXIntCompletion p) = ⟨(0 : FpXCompletion p), Subring.zero_mem _⟩ := by rfl
  rw [FpXIntCompletion.X, ne_eq, h0, Subtype.mk_eq_mk, _root_.map_eq_zero]
  exact RatFunc.X_ne_zero

open /- CompletionLaurentSeries  -/LaurentSeries

theorem dvd_of_norm_lt_one {F : FpXIntCompletion p} :
    Valued.v (F : FpXCompletion p) < (1 : ℤₘ₀) → FpXIntCompletion.X p ∣ F := by
  set f : FpXCompletion p := ↑F with h_Ff
  set g := (ratfuncAdicComplRingEquiv 𝔽_[p]) f with h_fg
  have h_gf : (LaurentSeriesRingEquiv 𝔽_[p]) g = f := by rw [h_fg, RingEquiv.symm_apply_apply]
  erw [← h_gf, valuation_compare 𝔽_[p] g, ← WithZero.coe_one, ← ofAdd_zero, ← neg_zero]
  intro h
  obtain ⟨G, h_Gg⟩ : ∃ G : PowerSeries 𝔽_[p], ↑G = g :=
    by
    replace h := le_of_lt h
    rwa [neg_zero, ofAdd_zero, WithZero.coe_one, val_le_one_iff_eq_coe] at h
  rw [neg_zero, ← neg_add_self (1 : ℤ), WithZero.lt_succ_iff_le, ← h_Gg, ← Int.ofNat_one,
    LaurentSeries.int_valuation_le_iff_coeff_zero_of_lt] at h
  specialize h 0 zero_lt_one
  rw [PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.X_dvd_iff] at h
  obtain ⟨C, rfl⟩ := dvd_iff_exists_eq_mul_left.mp h
  refine' dvd_of_mul_left_eq ⟨(LaurentSeriesRingEquiv 𝔽_[p]) C, _⟩ _
  · erw [FpXCompletion.mem_FpXIntCompletion, valuation_compare, val_le_one_iff_eq_coe]
    use C
  apply_fun algebraMap (FpXIntCompletion p) (FpXCompletion p) using Subtype.val_injective
  apply_fun ratfuncAdicComplRingEquiv 𝔽_[p]
  erw [algebraMap_eq_coe, algebraMap_eq_coe, ← h_Ff, ← h_fg, ← h_Gg, _root_.map_mul]
  rw [PowerSeries.coe_mul, RingEquiv.apply_symm_apply, ← coe_X_compare 𝔽_[p]]
  rfl

theorem norm_lt_one_of_dvd {F : FpXIntCompletion p} :
    FpXIntCompletion.X p ∣ F → Valued.v (F : FpXCompletion p) < (1 : ℤₘ₀) := by
  rcases F with ⟨f, f_mem⟩
  obtain ⟨G, h_fG⟩ := exists_powerSeries_of_memIntegers 𝔽_[p] f_mem
  rintro ⟨⟨y, y_mem⟩, h⟩
  simp only
  erw [← h_fG, valuation_compare 𝔽_[p], ← WithZero.coe_one, ← ofAdd_zero, ← neg_zero, neg_zero, ←
    neg_add_self (1 : ℤ), WithZero.lt_succ_iff_le, ← Int.ofNat_one,
    LaurentSeries.int_valuation_le_iff_coeff_zero_of_lt]
  intro n hn
  replace hn : n = 0 := Nat.lt_one_iff.mp hn
  rw [hn]
  clear hn n
  rw [PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.X_dvd_iff]
  replace h_fy : f = y * FpXCompletion.X p := by
    apply_fun algebraMap (FpXIntCompletion p) (FpXCompletion p) at h
    rw [_root_.map_mul, algebraMap_eq_coe, algebraMap_eq_coe, algebraMap_eq_coe, mul_comm,
      ← Subring.coe_mul] at h
    exact h
  obtain ⟨Z, hZ⟩ := exists_powerSeries_of_memIntegers 𝔽_[p] y_mem
  refine' dvd_of_mul_left_eq Z _
  apply_fun HahnSeries.ofPowerSeries ℤ 𝔽_[p] using HahnSeries.ofPowerSeries_injective
  apply_fun LaurentSeriesRingEquiv 𝔽_[p]
  sorry/- rw [← LaurentSeries.coe_powerSeries]
  erw [PowerSeries.coe_mul, _root_.map_mul, hZ, h_fG, ← coe_X_compare 𝔽_[p], h_fy,
    RingEquiv.symm_apply_apply]
  rfl -/

theorem norm_lt_one_iff_dvd (F : FpXIntCompletion p) :
    ‖(F : FpXCompletion p)‖ < 1 ↔ FpXIntCompletion.X p ∣ F := by
  have H : ‖(F : FpXCompletion p)‖ = Valued.norm (F : FpXCompletion p) := rfl
  suffices Valued.v (F : FpXCompletion p) < (1 : ℤₘ₀) ↔ FpXIntCompletion.X p ∣ F by
    rwa [H, RankOneValuation.norm_lt_one_iff_val_lt_one]
  exact ⟨dvd_of_norm_lt_one p, norm_lt_one_of_dvd p⟩

end FpXIntCompletion

namespace AdicAlgebra


variable (K L : Type _) [Field K] [Algebra (FpXCompletion p) K] [Field L]

variable [Algebra (FpXCompletion p) L]

instance toIntAlgebra : Algebra (FpXIntCompletion p) K :=
  ValuationSubring.algebra' _ K

@[simp]
theorem int_algebraMap_def :
    algebraMap (FpXIntCompletion p) K = (AdicAlgebra.toIntAlgebra p K).toRingHom :=
  rfl

instance (priority := 10000) : IsScalarTower (FpXIntCompletion p) (FpXCompletion p) K :=
  ValuationSubring.isScalarTower _ _

instance (priority := 1000) int_isScalarTower [Algebra K L] [IsScalarTower (FpXCompletion p) K L] :
    IsScalarTower (FpXIntCompletion p) K L :=
  ValuationSubring.int_isScalarTower _ K L

theorem algebraMap_injective : Function.Injective ⇑(algebraMap (FpXIntCompletion p) L) :=
  ValuationSubring.algebraMap_injective _ L

end AdicAlgebra

/-- An equal characteristic local field is a field which is finite
dimensional over `𝔽_p((X))`, for some prime `p`. -/
class EqCharLocalField (p : outParam ℕ) [Fact (Nat.Prime p)] (K : Type _) [Field K] extends
    Algebra (FpXCompletion p) K where
  [to_finiteDimensional : FiniteDimensional (FpXCompletion p) K]

attribute [instance] EqCharLocalField.to_finiteDimensional

namespace EqCharLocalField

variable (K L : Type _) [Field K] [EqCharLocalField p K] [Field L] [EqCharLocalField p L]

instance (priority := 100) charP : CharP K p :=
  charP_of_injective_algebraMap (algebraMap (FpXCompletion p) K).injective p

/-- The ring of integers of an equal characteristic local field is the integral closure of
`FpX_int_completion` in the local field. -/
def ringOfIntegers :=
  integralClosure (FpXIntCompletion p) K

scoped notation3 "𝓞" => EqCharLocalField.ringOfIntegers

theorem mem_ringOfIntegers (x : K) : x ∈ 𝓞 p K ↔ IsIntegral (FpXIntCompletion p) x :=
  Iff.rfl

/-- Given an extension of two local fields over `FpX_completion`, we define an algebra structure
between their two rings of integers. For now, this is not an instance by default as it creates an
equal-but-not-defeq diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not
being defeq on subtypes. It will be an instance when ported to Lean 4, since the above will not be
an issue. -/
def ringOfIntegersAlgebra [Algebra K L] [IsScalarTower (FpXCompletion p) K L] :
    Algebra (𝓞 p K) (𝓞 p L) :=
  ValuationSubring.valuationSubringAlgebra _ K L

namespace RingOfIntegers

variable {K}

instance : IsFractionRing (𝓞 p K) K :=
  @integralClosure.isFractionRing_of_finite_extension (FpXIntCompletion p) (FpXCompletion p) _ _ K _
    _ _ FpXIntCompletion.isFractionRing _ _ _ _

instance : IsIntegralClosure (𝓞 p K) (FpXIntCompletion p) K :=
  integralClosure.isIntegralClosure _ _

-- Porting note: inferInstance no longer works
instance : Algebra (FpXIntCompletion p) (𝓞 p K) := Subalgebra.algebra _

-- Porting note : needed to add this
instance : SMul ↥(FpXIntCompletion p) ↥(𝓞 p K) := Algebra.toSMul

-- Porting note: inferInstance no longer works
instance : IsScalarTower (FpXIntCompletion p) (𝓞 p K) K :=
  IsScalarTower.subalgebra' (FpXIntCompletion p) K K (𝓞 p K)

theorem isIntegral_coe (x : 𝓞 p K) : IsIntegral (FpXIntCompletion p) (x : K) :=
  x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `FpX_int_completion`
insie `K` -/
protected noncomputable def equiv (R : Type _) [CommRing R] [hR : Algebra (FpXIntCompletion p) R]
    [Algebra R K] [htow : IsScalarTower (FpXIntCompletion p) R K]
    [hic : IsIntegralClosure R (FpXIntCompletion p) K] : 𝓞 p K ≃+* R := by
  letI : Algebra Valued.v.valuationSubring R := hR
  letI : IsIntegralClosure R (Valued.v.valuationSubring) K := hic
  letI : IsScalarTower (Valued.v.valuationSubring) R K := htow
  exact ValuationSubring.equiv _ K R

variable (K)

instance : CharP (𝓞 p K) p :=
  CharP.subring' K p (𝓞 p K).toSubring

theorem algebraMap_injective :
    Function.Injective ⇑(algebraMap (FpXIntCompletion p) (ringOfIntegers p K)) :=
  ValuationSubring.integralClosure_algebraMap_injective _ K

end RingOfIntegers

end EqCharLocalField

namespace FpXCompletion

open EqCharLocalField

open scoped EqCharLocalField

instance eqCharLocalField (p : ℕ) [Fact (Nat.Prime p)] : EqCharLocalField p (FpXCompletion p) where
  to_finiteDimensional := by
    convert (inferInstance : FiniteDimensional (FpXCompletion p) (FpXCompletion p))

/-- The ring of integers of `FpX_completion` as a mixed characteristic local field coincides with
  `FpX_int_completion`. -/
def ringOfIntegersEquiv (p : ℕ) [Fact (Nat.Prime p)] :
    ringOfIntegers p (FpXCompletion p) ≃+* FpXIntCompletion p := by
  -- Porting note: I had to add these local instances
  letI : SMul ↥(FpXIntCompletion p) ↥(FpXIntCompletion p) := Algebra.toSMul
  letI : IsScalarTower (FpXIntCompletion p) (FpXIntCompletion p) (FpXCompletion p) :=
    IsScalarTower.left _
  apply @RingOfIntegers.equiv p _ (FpXCompletion p) _ _ (FpXIntCompletion p) _ _


theorem open_unit_ball_def :
    LocalRing.maximalIdeal (FpXIntCompletion p) = Ideal.span {FpXIntCompletion.X p} := by
  apply DiscreteValuation.IsUniformizer_is_generator; exact valuation_X

end FpXCompletion

namespace FpXIntCompletion

variable (K : Type _) [Field K] [EqCharLocalField p K]

open EqCharLocalField

open scoped EqCharLocalField


theorem x_coe_ne_zero : ¬(algebraMap (FpXIntCompletion p) (𝓞 p K)) (FpXIntCompletion.X p) = 0 := by
  -- Porting note: needed to add local instance
  letI : AddMonoidHomClass (↥(FpXIntCompletion p) →+* ↥(ringOfIntegers p K))
    ↥(FpXIntCompletion p) ↥(ringOfIntegers p K) := RingHomClass.toAddMonoidHomClass
  intro h
  exact FpXIntCompletion.X_ne_zero p
      ((injective_iff_map_eq_zero _).mp (RingOfIntegers.algebraMap_injective p K) _ h)

instance : Algebra (RatFunc 𝔽_[p]) K :=
  (RingHom.comp (algebraMap (FpXCompletion p) K)
      (algebraMap (RatFunc 𝔽_[p]) (FpXCompletion p))).toAlgebra

end FpXIntCompletion
