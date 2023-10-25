import Mathlib.Algebra.CharP.Subring
import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.LaurentSeriesEquivAdicCompletion
import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.DedekindDomain.AdicValuation

#align_import eq_characteristic.basic

/-!
# Equal characteristic local fields

In this file we focus on the `X`-adic completion `FpX_completion` of the ring of rational functions
over the finite field `𝔽_[p]` and we define an equal characteristic local field as a finite
extension of `FpX_completion`.

## Main Definitions
* `FpX_completion` is the adic completion of the rational functions `𝔽_p(X)`.
* `FpX_int_completion` is the unit ball in the adic completion of the rational functions `𝔽_p(X)`.
* `isom_laurent` is the ring isomorphism `(laurent_series 𝔽_[p]) ≃+* FpX_completion`
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
  RankOneValuation ValuationSubring

variable (p : ℕ) [Fact (Nat.Prime p)]

notation "𝔽_[" p "]" => GaloisField p 1

/-- `FpX_completion` is the adic completion of the rational functions `𝔽_p(X)`. -/
@[reducible]
def FpXCompletion :=
  (idealX 𝔽_[p]).adicCompletion (RatFunc 𝔽_[p])

/-- `FpX_int_completion` is the unit ball in the adic completion of the rational functions
`𝔽_p(X)`. -/
@[reducible]
def fpXIntCompletion :=
  (idealX 𝔽_[p]).adicCompletionIntegers (RatFunc 𝔽_[p])

open PowerSeries

instance : Fintype (LocalRing.ResidueField (PowerSeries 𝔽_[p])) :=
  Fintype.ofEquiv _ (residueFieldOfPowerSeries 𝔽_[p]).toEquiv.symm

instance RatFunc.charP : CharP (RatFunc 𝔽_[p]) p :=
  charP_of_injective_algebraMap (algebraMap 𝔽_[p] (RatFunc 𝔽_[p])).Injective p

namespace FpXCompletion

variable {p}

instance : Coe (RatFunc 𝔽_[p]) (FpXCompletion p) :=
  ⟨algebraMap (RatFunc 𝔽_[p]) (FpXCompletion p)⟩

theorem algebraMap_eq_coe (f : RatFunc 𝔽_[p]) :
    algebraMap (RatFunc 𝔽_[p]) (FpXCompletion p) f = coe f :=
  rfl

instance charP : CharP (FpXCompletion p) p :=
  charP_of_injective_algebraMap (algebraMap (RatFunc (GaloisField p 1)) (FpXCompletion p)).Injective
    p

/-- The `valued` structure on the adic completion `FpX_completion`. -/
def WithZero.valued : Valued (FpXCompletion p) ℤₘ₀ :=
  HeightOneSpectrum.valuedAdicCompletion (RatFunc 𝔽_[p]) (idealX 𝔽_[p])

theorem valuation_x :
    Valued.v ((algebraMap (RatFunc (GaloisField p 1)) (FpXCompletion p)) X) = ofAdd (-1 : ℤ) := by
  erw [valued_adic_completion_def, FpXCompletion.algebraMap_eq_coe, Valued.extension_extends,
    val_X_eq_neg_one]

theorem mem_fpXIntCompletion {x : FpXCompletion p} :
    x ∈ fpXIntCompletion p ↔ (Valued.v x : ℤₘ₀) ≤ 1 :=
  Iff.rfl

theorem x_mem_fpXIntCompletion : algebraMap (RatFunc 𝔽_[p]) _ X ∈ fpXIntCompletion p :=
  by
  erw [FpXCompletion.mem_fpXIntCompletion, FpXCompletion.valuation_x, ← WithZero.coe_one,
    WithZero.coe_le_coe, ← ofAdd_zero, of_add_le]
  linarith

instance : Inhabited (FpXCompletion p) :=
  ⟨(0 : FpXCompletion p)⟩

instance : IsRankOne (@FpXCompletion.WithZero.valued p _).V :=
  DiscreteValuation.isRankOne Valued.v

instance : NormedField (FpXCompletion p) :=
  ValuedField.toNormedField (FpXCompletion p) ℤₘ₀

theorem mem_FpX_int_completion' {x : FpXCompletion p} : x ∈ fpXIntCompletion p ↔ ‖x‖ ≤ 1 := by
  erw [FpXCompletion.mem_fpXIntCompletion, norm_le_one_iff_val_le_one]

variable (p)

/-- `isom_laurent` is the ring isomorphism `FpX_completion ≃+* (laurent_series 𝔽_[p])`. -/
def isomLaurent : LaurentSeries 𝔽_[p] ≃+* FpXCompletion p :=
  CompletionLaurentSeries.laurentSeriesRingEquiv 𝔽_[p]

end FpXCompletion

namespace fpXIntCompletion

/-- `integers_equiv_power_series` is the ring isomorphism `(power_series 𝔽_[p])` ≃+*
  `FpX_int_completion`. -/
noncomputable def integersEquivPowerSeries : PowerSeries 𝔽_[p] ≃+* fpXIntCompletion p :=
  CompletionLaurentSeries.powerSeriesRingEquiv 𝔽_[p]

noncomputable theorem residueField_powerSeries_card :
    Fintype.card (LocalRing.ResidueField (PowerSeries 𝔽_[p])) = p :=
  by
  convert Fintype.ofEquiv_card (residue_field_of_power_series 𝔽_[p]).toEquiv.symm
  rw [GaloisField.card p 1 one_ne_zero, pow_one]

variable {p}

noncomputable theorem residueField_card_eq_char :
    Nat.card (LocalRing.ResidueField (fpXIntCompletion p)) = p := by
  simp only [←
    Nat.card_congr (LocalRing.ResidueField.mapEquiv (integers_equiv_power_series p)).toEquiv,
    Nat.card_eq_fintype_card, residue_field_power_series_card p]

variable (p)

noncomputable instance : Fintype (LocalRing.ResidueField (fpXIntCompletion p)) :=
  Fintype.ofEquiv _ (LocalRing.ResidueField.mapEquiv (integersEquivPowerSeries p)).toEquiv

/-- The `fintype` structure on the residue field of `FpX_int_completion`. -/
noncomputable def residueFieldFintypeOfCompletion :
    Fintype (LocalRing.ResidueField (fpXIntCompletion p)) :=
  inferInstance

end fpXIntCompletion

namespace FpXCompletion

theorem valuation_base_eq_char : Valuation.base (FpXCompletion p) Valued.v = p :=
  by
  rw [Valuation.base, if_pos]
  · exact nat.cast_inj.mpr fpXIntCompletion.residueField_card_eq_char
  · erw [fpXIntCompletion.residueField_card_eq_char]
    exact (Fact.out (Nat.Prime p)).one_lt

end FpXCompletion

namespace fpXIntCompletion

variable {p}

instance : DiscreteValuationRing (fpXIntCompletion p) :=
  DiscreteValuation.dvr_of_isDiscrete _

instance : Algebra (fpXIntCompletion p) (FpXCompletion p) :=
  (by infer_instance :
    Algebra ((Polynomial.idealX 𝔽_[p]).adicCompletionIntegers (RatFunc 𝔽_[p]))
      ((Polynomial.idealX 𝔽_[p]).adicCompletion (RatFunc 𝔽_[p])))

instance : Coe (fpXIntCompletion p) (FpXCompletion p) :=
  ⟨algebraMap _ _⟩

theorem algebraMap_eq_coe (x : fpXIntCompletion p) :
    algebraMap (fpXIntCompletion p) (FpXCompletion p) x = x :=
  rfl

instance isFractionRing : IsFractionRing (fpXIntCompletion p) (FpXCompletion p) :=
  (by infer_instance :
    IsFractionRing ((Polynomial.idealX 𝔽_[p]).adicCompletionIntegers (RatFunc 𝔽_[p]))
      ((Polynomial.idealX 𝔽_[p]).adicCompletion (RatFunc 𝔽_[p])))

variable (p)

instance : IsIntegralClosure (fpXIntCompletion p) (fpXIntCompletion p) (FpXCompletion p) :=
  IsIntegrallyClosed.isIntegralClosure

/-- `FpX_int_completions.X` is the polynomial variable `X : ratfunc 𝔽_[p]`, first coerced to the
completion `FpX_completion` and then regarded as an integral element using the bound on its norm.-/
def x : fpXIntCompletion p :=
  ⟨algebraMap (RatFunc 𝔽_[p]) _ X, FpXCompletion.x_mem_fpXIntCompletion⟩

end fpXIntCompletion

namespace FpXCompletion

/-- `FpX_completions.X` is the image of `FpX_int_completions.X` along the `algebra_map` given by the
embedding of the ring of integers in the whole space `FpX_completion` The next lemma shows that this
is simply the coercion of `X : ratfunc 𝔽_[p]` to its adic completion `FpX_completion`. -/
def x :=
  algebraMap (fpXIntCompletion p) (FpXCompletion p) (fpXIntCompletion.x p)

theorem x_eq_coe : x p = ↑(@RatFunc.X 𝔽_[p] _ _) :=
  rfl

theorem norm_x : ‖x p‖ = 1 / (p : ℝ) :=
  by
  have hv : Valued.v (X p) = Multiplicative.ofAdd (-1 : ℤ) :=
    by
    rw [← val_X_eq_neg_one 𝔽_[p], height_one_spectrum.valued_adic_completion_def,
      FpXCompletion.x_eq_coe, Valued.extension_extends]
    rfl
  have hX : ‖X p‖ = IsRankOne.hom _ (Valued.v (X p)) := rfl
  rw [hX, hv, DiscreteValuation.isRankOne_hom_def]
  simp only [ofAdd_neg, WithZero.coe_inv, map_inv₀, Nonneg.coe_inv, one_div, inv_inj]
  simp only [withZeroMultIntToNnreal, withZeroMultIntToNnrealDef, MonoidWithZeroHom.coe_mk]
  rw [dif_neg]
  · simp only [WithZero.unzero_coe, toAdd_ofAdd, zpow_one]
    rw [valuation_base_eq_char]; simp only [NNReal.coe_nat_cast]
  · simp only [WithZero.coe_ne_zero, withZeroMultIntToNnreal_strictMono, not_false_iff]

variable {p}

theorem norm_x_pos : 0 < ‖x p‖ := by
  rw [norm_X, one_div, inv_pos, Nat.cast_pos] <;> exact _inst_1.out.Pos

theorem norm_x_lt_one : ‖x p‖ < 1 := by
  rw [norm_X, one_div] <;> exact inv_lt_one (nat.one_lt_cast.mpr _inst_1.out.one_lt)

instance : NontriviallyNormedField (FpXCompletion p) :=
  { (by infer_instance : NormedField (FpXCompletion p)) with
    non_trivial := by
      use(X p)⁻¹
      rw [norm_inv]
      exact one_lt_inv norm_X_pos norm_X_lt_one }

theorem x_mem_int_completion : x p ∈ fpXIntCompletion p :=
  by
  rw [mem_FpX_int_completion, ← norm_le_one_iff_val_le_one]
  exact le_of_lt norm_X_lt_one

theorem norm_isNonarchimedean : IsNonarchimedean (norm : FpXCompletion p → ℝ) :=
  normDef_isNonarchimedean _ _

end FpXCompletion

namespace fpXIntCompletion

variable (p)

theorem x_ne_zero : fpXIntCompletion.x p ≠ 0 :=
  by
  have h0 : (0 : fpXIntCompletion p) = ⟨(0 : FpXCompletion p), Subring.zero_mem _⟩ := by rfl
  rw [fpXIntCompletion.x, Ne.def, h0, Subtype.mk_eq_mk, _root_.map_eq_zero]
  exact RatFunc.X_ne_zero

open CompletionLaurentSeries LaurentSeries

theorem dvd_of_norm_lt_one {F : fpXIntCompletion p} :
    Valued.v (F : FpXCompletion p) < (1 : ℤₘ₀) → fpXIntCompletion.x p ∣ F :=
  by
  set f : FpXCompletion p := ↑F with h_Ff
  set g := (ratfunc_adic_compl_ring_equiv 𝔽_[p]) f with h_fg
  have h_gf : (laurent_series_ring_equiv 𝔽_[p]) g = f := by rw [h_fg, RingEquiv.symm_apply_apply]
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
  refine' dvd_of_mul_left_eq ⟨(laurent_series_ring_equiv 𝔽_[p]) C, _⟩ _
  · erw [FpXCompletion.mem_fpXIntCompletion, valuation_compare, val_le_one_iff_eq_coe]
    use⟨C, refl _⟩
  apply_fun algebraMap (fpXIntCompletion p) (FpXCompletion p) using Subtype.val_injective
  apply_fun ratfunc_adic_compl_ring_equiv 𝔽_[p]
  erw [algebra_map_eq_coe, algebra_map_eq_coe, ← h_Ff, ← h_fg, ← h_Gg, map_mul, PowerSeries.coe_mul,
    RingEquiv.apply_symm_apply, ← coe_X_compare 𝔽_[p]]
  rfl

theorem norm_lt_one_of_dvd {F : fpXIntCompletion p} :
    fpXIntCompletion.x p ∣ F → Valued.v (F : FpXCompletion p) < (1 : ℤₘ₀) :=
  by
  rcases F with ⟨f, f_mem⟩
  obtain ⟨G, h_fG⟩ := exists_power_series_of_mem_integers 𝔽_[p] f_mem
  rintro ⟨⟨y, y_mem⟩, h⟩
  rw [← Subtype.val_eq_coe]
  simp only
  erw [← h_fG, valuation_compare 𝔽_[p], ← WithZero.coe_one, ← ofAdd_zero, ← neg_zero, neg_zero, ←
    neg_add_self (1 : ℤ), WithZero.lt_succ_iff_le, ← Int.ofNat_one,
    LaurentSeries.int_valuation_le_iff_coeff_zero_of_lt]
  intro n hn
  replace hn : n = 0 := nat.lt_one_iff.mp hn
  rw [hn]
  clear hn n
  rw [PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.X_dvd_iff]
  replace h_fy : f = y * X p
  · apply_fun algebraMap (fpXIntCompletion p) (FpXCompletion p) at h
    simp only [map_mul, algebra_map_eq_coe, mul_comm, SetLike.coe_mk, Subring.coe_mul] at h
    exact h
  obtain ⟨Z, hZ⟩ := exists_power_series_of_mem_integers 𝔽_[p] y_mem
  refine' dvd_of_mul_left_eq Z _
  apply_fun HahnSeries.ofPowerSeries ℤ 𝔽_[p] using HahnSeries.ofPowerSeries_injective
  apply_fun laurent_series_ring_equiv 𝔽_[p]
  simp only [← LaurentSeries.coe_powerSeries]
  erw [PowerSeries.coe_mul, map_mul, hZ, h_fG, ← coe_X_compare 𝔽_[p], h_fy,
    RingEquiv.symm_apply_apply]
  rfl

theorem norm_lt_one_iff_dvd (F : fpXIntCompletion p) :
    ‖(F : FpXCompletion p)‖ < 1 ↔ fpXIntCompletion.x p ∣ F :=
  by
  have H : ‖(F : FpXCompletion p)‖ = RankOneValuation.normDef (F : FpXCompletion p) := rfl
  suffices Valued.v (F : FpXCompletion p) < (1 : ℤₘ₀) ↔ fpXIntCompletion.x p ∣ F by
    rwa [H, RankOneValuation.norm_lt_one_iff_val_lt_one]
  exact ⟨dvd_of_norm_lt_one p, norm_lt_one_of_dvd p⟩

end fpXIntCompletion

namespace AdicAlgebra

variable {p} (K L : Type _) [Field K] [Algebra (FpXCompletion p) K] [Field L]

variable [Algebra (FpXCompletion p) L]

instance toIntAlgebra : Algebra (fpXIntCompletion p) K :=
  ValuationSubring.algebra' _ K

@[simp]
theorem int_algebraMap_def :
    algebraMap (fpXIntCompletion p) K = (AdicAlgebra.toIntAlgebra K).toRingHom :=
  rfl

instance (priority := 10000) : IsScalarTower (fpXIntCompletion p) (FpXCompletion p) K :=
  ValuationSubring.isScalarTower _ _

instance (priority := 1000) int_isScalarTower [Algebra K L] [IsScalarTower (FpXCompletion p) K L] :
    IsScalarTower (fpXIntCompletion p) K L :=
  ValuationSubring.int_isScalarTower _ K L

theorem algebraMap_injective : Function.Injective ⇑(algebraMap (fpXIntCompletion p) L) :=
  ValuationSubring.algebraMap_injective _ L

end AdicAlgebra

variable (p)

/-- An equal characteristic local field is a field which is finite
dimensional over `𝔽_p((X))`, for some prime `p`. -/
class EqCharLocalField (p : outParam ℕ) [Fact (Nat.Prime p)] (K : Type _) [Field K] extends
    Algebra (FpXCompletion p) K where
  [to_finiteDimensional : FiniteDimensional (FpXCompletion p) K]

attribute [instance] EqCharLocalField.to_finiteDimensional

namespace EqCharLocalField

variable (p) (K L : Type _) [Field K] [EqCharLocalField p K] [Field L] [EqCharLocalField p L]

instance (priority := 100) charP : CharP K p :=
  charP_of_injective_algebraMap (algebraMap (FpXCompletion p) K).Injective p

/-- The ring of integers of an equal characteristic local field is the integral closure of
`FpX_int_completion` in the local field. -/
def ringOfIntegers :=
  integralClosure (fpXIntCompletion p) K

scoped notation "𝓞" => EqCharLocalField.ringOfIntegers

theorem mem_ringOfIntegers (x : K) : x ∈ 𝓞 p K ↔ IsIntegral (fpXIntCompletion p) x :=
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
  @integralClosure.isFractionRing_of_finite_extension (fpXIntCompletion p) (FpXCompletion p) _ _ K _
    _ _ fpXIntCompletion.isFractionRing _ _ _ _

instance : IsIntegralClosure (𝓞 p K) (fpXIntCompletion p) K :=
  integralClosure.isIntegralClosure _ _

instance : Algebra (fpXIntCompletion p) (𝓞 p K) :=
  inferInstance

instance : IsScalarTower (fpXIntCompletion p) (𝓞 p K) K :=
  inferInstance

theorem isIntegral_coe (x : 𝓞 p K) : IsIntegral (fpXIntCompletion p) (x : K) :=
  x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `FpX_int_completion`
insie `K` -/
protected noncomputable def equiv (R : Type _) [CommRing R] [Algebra (fpXIntCompletion p) R]
    [Algebra R K] [IsScalarTower (fpXIntCompletion p) R K]
    [IsIntegralClosure R (fpXIntCompletion p) K] : 𝓞 p K ≃+* R :=
  by
  letI : Algebra valued.v.valuation_subring R := _inst_7
  letI : IsIntegralClosure R (↥valued.v.valuation_subring) K := _inst_10
  letI : IsScalarTower (↥valued.v.valuation_subring) R K := _inst_9
  exact ValuationSubring.equiv _ K R

variable (K)

instance : CharP (𝓞 p K) p :=
  CharP.subring' K p (𝓞 p K).toSubring

theorem algebraMap_injective :
    Function.Injective ⇑(algebraMap (fpXIntCompletion p) (ringOfIntegers p K)) :=
  ValuationSubring.integralClosure_algebraMap_injective _ K

end RingOfIntegers

end EqCharLocalField

namespace FpXCompletion

open EqCharLocalField

open scoped EqCharLocalField

instance eqCharLocalField (p : ℕ) [Fact (Nat.Prime p)] : EqCharLocalField p (FpXCompletion p)
    where to_finiteDimensional := by
    convert (inferInstance : FiniteDimensional (FpXCompletion p) (FpXCompletion p))

/-- The ring of integers of `FpX_completion` as a mixed characteristic local field coincides with
  `FpX_int_completion`. -/
def ringOfIntegersEquiv (p : ℕ) [Fact (Nat.Prime p)] :
    ringOfIntegers p (FpXCompletion p) ≃+* fpXIntCompletion p :=
  by
  have h :=
    @ring_of_integers.equiv p _ (FpXCompletion p) _ _ (fpXIntCompletion p) _ _
      (fpXIntCompletion p).Algebra (IsScalarTower.left (fpXIntCompletion p))
  have h1 := fpXIntCompletion.FpXCompletion.isIntegralClosure p
  exact @h h1

theorem open_unit_ball_def :
    LocalRing.maximalIdeal (fpXIntCompletion p) = Ideal.span {fpXIntCompletion.x p} := by
  apply DiscreteValuation.isUniformizer_is_generator <;> exact valuation_X

end FpXCompletion

namespace fpXIntCompletion

variable (K : Type _) [Field K] [EqCharLocalField p K]

open EqCharLocalField

open scoped EqCharLocalField

theorem x_coe_ne_zero : ¬(algebraMap (fpXIntCompletion p) (𝓞 p K)) (fpXIntCompletion.x p) = 0 :=
  by
  intro h
  exact
    fpXIntCompletion.x_ne_zero p
      ((injective_iff_map_eq_zero _).mp (ring_of_integers.algebra_map_injective p K) _ h)

instance : Algebra (RatFunc 𝔽_[p]) K :=
  (RingHom.comp (algebraMap (FpXCompletion p) K)
      (algebraMap (RatFunc 𝔽_[p]) (FpXCompletion p))).toAlgebra

end fpXIntCompletion
