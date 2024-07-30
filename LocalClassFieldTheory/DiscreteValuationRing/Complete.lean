/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open scoped DiscreteValuation

open Multiplicative

/-!
# Complete DVR's
Starting with a Dedekind domain `R` with fraction field `K` and a maximal ideal `v`,
the adic completion `K_v` of `K` with respect to `v.valuation` has a valuation that extends
`v.valuation`. We prove that since `v.valuation` is discrete, so is its extension and therefore, by
the results in `discrete_valuation_ring.basic`, the unit ball in `K_v` is a discrete valuation ring.
In particular, `K_v` can be endowed with the adic valuation associated to the unique maximal ideal
of its unit ball. In this file we prove that these two valuations on `K_v`, namely the extension of
`v.valuation` and the adic valuation just discussed, coincide.

## Main definitions
* `K_v` and `R_v` are, respectively, the adic completion of `K` with respect to `v.valuation` and
the unit ball inside `K_v`.
* `maxIdealOfCompletion` Is the maximal ideal of `R_v`, that is a discrete valuation ring, as a
term of the `height_one_spectrum` of `R_v`. The underlying ideal is `height_one_spectrum_def`.
* `v_adic_of_compl` is the adic valuation on `K_v` attached to `maxIdealOfCompletion`
* `v_compl_of_adic` is the uniform extension of `valuation.v` to the adic (=uniform) completion
`K_v` of `K`.


## Main results:
* `is_dedekind_domain.height_one_spectrum.completion.is_discrete` is the instance that the extension
of the adic valuation to the completion is discrete (i.e. surjective onto `ℤₘ₀`). As a consequence,
the unit ball `R_v` is a discrete valuation ring.
* `adic_of_compl_eq_compl_of_adic` shows that the two valuations on `K_v`, namely
`v_adic_of_compl` and `compl_of_v_adic`, coincide.

## Implementation details
* When viewing `K_v` as the completion of `K`, its `valued` instance comes from the completion of
the valuation on `K`, and this is of course different from the `valued` instance on the fraction
field of `R_v`, itself isomorphic (but not **equal**) to `K_v`, that instead comes from the
`discrete_valuation_ring` instance on `R_v`. In particular, no diamond arises because the types
`fraction_ring R_v` and `K_v` are different, although equivalent as fields.
* The terms `maxIdealOfCompletionDef` and `maxIdealOfCompletion` represent the same
mathematical object but one is an ideal, the other is a term of the height-one spectrum and it is
the second that has an adic valuation attached to it.
-/


noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Valuation

namespace IsDedekindDomain.HeightOneSpectrum.Completion

variable (R : Type _) [CommRing R] [IsDomain R] [IsDedekindDomain R] (v : HeightOneSpectrum R)

variable (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

local notation "R_v" => adicCompletionIntegers K v

local notation "K_v" => adicCompletion K v

instance isDiscrete : IsDiscrete (@Valued.v K_v _ ℤₘ₀ _ _) :=
  by
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v
  apply isDiscreteOfExistsUniformizer
  swap
  use(↑π : K_v)
  rw [IsUniformizer_iff, ← hπ]
  convert @Valued.extension_extends K _ _ _ (Valued.mk' v.valuation) π

/-- The maximal ideal of `R_v`, that is a discrete valuation ring. -/
def maxIdealOfCompletionDef : Ideal R_v :=
  LocalRing.maximalIdeal R_v

instance : DiscreteValuationRing R_v := DiscreteValuation.dvr_of_isDiscrete _

theorem IsDedekindDomain.HeightOneSpectrum.valuation_completion_integers_exists_uniformizer :
    ∃ π : R_v, Valued.v (π : K_v) = ofAdd (-1 : ℤ) := by
  letI ValI : Valued K ℤₘ₀ := adicValued v
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  use ⟨algebraMap R_v K_v (algebraMap _ R_v x), by simp only [ValuationSubring.algebraMap_apply,
    SetLike.coe_mem]⟩
  have h2 : v.intValuationDef x = v.intValuation x := rfl
  rw [← hx,/-  SetLike.coe_mk, -/ IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_def, h2,
    ← @IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap R _ _ K _ _ _ v x]
  exact @Valued.extension_extends K _ ℤₘ₀ _ _ (algebraMap _ K x)

theorem IsDedekindDomain.HeightOneSpectrum.valuation_completion_exists_uniformizer :
    ∃ π : K_v, Valued.v π = ofAdd (-1 : ℤ) := by
  letI : Valued K ℤₘ₀ := adicValued v
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  use x
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_def, ← hx, Valued.extension_extends]
  rfl

theorem adicCompletionIntegers_not_isField :
    ¬IsField (HeightOneSpectrum.adicCompletionIntegers K v) := by
  rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  use maxIdealOfCompletionDef R v K
  constructor
  · rw [bot_lt_iff_ne_bot, ne_eq]
    by_contra h
    obtain ⟨π, hπ⟩ :=
      IsDedekindDomain.HeightOneSpectrum.valuation_completion_integers_exists_uniformizer R v K
    have h1 : π ∈ maxIdealOfCompletionDef R v K := by
      rw [maxIdealOfCompletionDef, LocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one, hπ]
      exact WithZero.ofAdd_neg_one_lt_one
    rw [h, Ideal.mem_bot] at h1
    simp only [h1, ZeroMemClass.coe_zero, _root_.map_zero, ofAdd_neg, WithZero.coe_inv,
      zero_eq_inv, WithZero.zero_ne_coe] at hπ
  · simp only [lt_top_iff_ne_top, ne_eq, Ideal.eq_top_iff_one, maxIdealOfCompletionDef,
      LocalRing.mem_maximalIdeal, one_not_mem_nonunits, not_false_iff]

/-- The maximal ideal of `R_v`, as a term of the `height_one_spectrum` of `R_v`.
The underlying ideal is `height_one_spectrum_def`. -/
def maxIdealOfCompletion : HeightOneSpectrum R_v where
  asIdeal := maxIdealOfCompletionDef R v K
  isPrime := Ideal.IsMaximal.isPrime (LocalRing.maximalIdeal.isMaximal R_v)
  ne_bot := by
    rw [ne_eq, maxIdealOfCompletionDef, ← LocalRing.isField_iff_maximalIdeal_eq]
    exact adicCompletionIntegers_not_isField R v K

local notation "v_adic_of_compl" =>
  IsDedekindDomain.HeightOneSpectrum.valuation (K := K_v) (maxIdealOfCompletion R v K)

local notation "v_compl_of_adic" => (Valued.v : Valuation K_v ℤₘ₀)

open LocalRing DiscretelyValued

/-The following `instance` is needed to help in the following theorem, where it cannot be inferred
automatically-/
instance : IsDedekindDomain R_v := IsPrincipalIdealRing.isDedekindDomain _

theorem int_adic_of_compl_eq_int_compl_of_adic (a : R_v) :
    (maxIdealOfCompletion R v K).intValuation a = Valued.v (algebraMap _ K_v a) := by
  by_cases ha : a = 0
  · simp_all only [_root_.map_zero]
  · rw [intValuation_apply]
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, v_compl_of_adic a = ofAdd (-n : ℤ) := by
        replace ha : v_compl_of_adic a ≠ 0 := by rwa [Valuation.ne_zero_iff, ne_eq,
          Subring.coe_eq_zero_iff]
        have := (mem_integer v_compl_of_adic ↑a).mp a.2
        obtain ⟨α, hα⟩ := WithZero.ne_zero_iff_exists.mp ha
        rw [← hα, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, ← ofAdd_toAdd α,
          Multiplicative.ofAdd_le] at this
        obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat this
        use n
        rw [← hα, WithZero.coe_inj, ← ofAdd_toAdd α, hn]
      rw [ValuationSubring.algebraMap_apply, hn, intValuation_le_pow_iff_dvd]
      apply (DiscreteValuation.val_le_iff_dvd K_v _ n).mp (le_of_eq hn)
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, v_adic_of_compl a = ofAdd (-m : ℤ) := by
        replace ha : v_adic_of_compl a ≠ 0 := by
          rwa [Valuation.ne_zero_iff, ne_eq, Subring.coe_eq_zero_iff]
        have : (maxIdealOfCompletion R v K).valuation (algebraMap _ K_v a) ≤ 1 := by
          exact valuation_le_one _ _
        obtain ⟨α, hα⟩ := WithZero.ne_zero_iff_exists.mp ha
        rw [ValuationSubring.algebraMap_apply, ← hα, ← WithZero.coe_one, ← ofAdd_zero,
          WithZero.coe_le_coe, ← ofAdd_toAdd α, Multiplicative.ofAdd_le] at this
        obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat this
        use m
        rw [← hα, WithZero.coe_inj, ← ofAdd_toAdd α, hm]
      · erw [valuation_of_algebraMap, intValuation_apply] at hm
        rw [hm]
        replace hm := le_of_eq hm
        rw [intValuation_le_pow_iff_dvd] at hm
        rw [ValuationSubring.algebraMap_apply, DiscreteValuation.val_le_iff_dvd]
        apply hm

theorem adic_of_compl_eq_compl_of_adic (x : K_v) : v_adic_of_compl x = v_compl_of_adic x := by
  obtain ⟨a, b, H⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R_v) x
  have h1 := @valuation_of_mk' R_v _ _ K_v _ _ _ (maxIdealOfCompletion R v K) a b
  have h2 :
    Valued.v (IsLocalization.mk' (adicCompletion K v) a b) =
      Valued.v (↑a : K_v) / Valued.v (↑b : K_v) :=
    by
    rw [div_eq_mul_inv, ← map_inv₀, ← Valuation.map_mul]
    apply congr_arg
    simp only [IsFractionRing.mk'_eq_div, ValuationSubring.algebraMap_apply, div_eq_mul_inv]
  rw [H] at h1 h2
  rw [h1, h2]
  congr 1 <;> apply int_adic_of_compl_eq_int_compl_of_adic

end IsDedekindDomain.HeightOneSpectrum.Completion
