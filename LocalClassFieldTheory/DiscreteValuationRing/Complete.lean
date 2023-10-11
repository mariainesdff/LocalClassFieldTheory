import DiscreteValuationRing.Basic
import RingTheory.DedekindDomain.AdicValuation

#align_import discrete_valuation_ring.complete

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
* `K_v` and `R_v` are, respectively, the adico completion of `K` with respect to `v.valuation` and
the unit ball inside `K_v`.
* `max_ideal_of_completion` Is the maximal ideal of `R_v`, that is a discrete valuation ring, as a
term of the `height_one_spectrum` of `R_v`. The underlying ideal is `height_one_spectrum_def`.
* `v_adic_of_compl` is the adic valuation on `K_v` attached to `max_ideal_of_completion`
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
* The terms `max_ideal_of_completion_def` and `max_ideal_of_completion` represent the same 
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
  apply is_discrete_of_exists_uniformizer
  swap
  use(↑π : K_v)
  rw [is_uniformizer_iff, ← hπ]
  convert @Valued.extension_extends K _ _ _ (Valued.mk' v.valuation) π

/-- The maximal ideal of `R_v`, that is a discrete valuation ring. -/
def maxIdealOfCompletionDef : Ideal R_v :=
  LocalRing.maximalIdeal R_v

instance : DiscreteValuationRing R_v :=
  DiscreteValuation.dvr_of_isDiscrete _

theorem IsDedekindDomain.HeightOneSpectrum.valuation_completion_integers_exists_uniformizer :
    ∃ π : R_v, Valued.v (π : K_v) = ofAdd (-1 : ℤ) :=
  by
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.int_valuation_exists_uniformizer v
  have h : algebraMap R_v K_v ↑x = (↑(↑x : K) : K_v) := rfl
  use⟨algebraMap R_v K_v ↑x, by simp only [ValuationSubring.algebraMap_apply, SetLike.coe_mem]⟩
  simp_rw [h]
  have h1 : (↑x : K) = algebraMap R K x := rfl
  have h2 : v.int_valuation_def x = v.int_valuation x := rfl
  rw [← hx, SetLike.coe_mk, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_def,
    Valued.extension_extends, h1, h2, ←
    @IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap R _ _ _ K _ _ _ v x]
  rfl

theorem IsDedekindDomain.HeightOneSpectrum.valuation_completion_exists_uniformizer :
    ∃ π : K_v, Valued.v π = ofAdd (-1 : ℤ) :=
  by
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  use↑x
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_def, ← hx, Valued.extension_extends]
  rfl

theorem adicCompletionIntegers_not_isField :
    ¬IsField ↥(HeightOneSpectrum.adicCompletionIntegers K v) :=
  by
  rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  use max_ideal_of_completion_def R v K
  constructor
  · rw [bot_lt_iff_ne_bot, Ne.def]
    by_contra h
    obtain ⟨π, hπ⟩ :=
      is_dedekind_domain.height_one_spectrum.valuation_completion_integers_exists_uniformizer R v K
    have h1 : π ∈ max_ideal_of_completion_def R v K :=
      by
      rw [max_ideal_of_completion_def, LocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.integer.not_isUnit_iff_valuation_lt_one, hπ]
      exact WithZero.ofAdd_neg_one_lt_one
    rw [h, Ideal.mem_bot] at h1 
    simp only [h1, algebraMap.coe_zero, Valuation.map_zero, WithZero.zero_ne_coe] at hπ 
    exact hπ
  ·
    simp only [lt_top_iff_ne_top, Ne.def, Ideal.eq_top_iff_one, max_ideal_of_completion_def,
      LocalRing.mem_maximalIdeal, one_not_mem_nonunits, not_false_iff]

/-- The maximal ideal of `R_v`, as a term of the `height_one_spectrum` of `R_v`.
The underlying ideal is `height_one_spectrum_def`. -/
def maxIdealOfCompletion : HeightOneSpectrum R_v
    where
  asIdeal := maxIdealOfCompletionDef R v K
  IsPrime := Ideal.IsMaximal.isPrime (LocalRing.maximalIdeal.isMaximal R_v)
  ne_bot :=
    by
    rw [Ne.def, max_ideal_of_completion_def, ← LocalRing.isField_iff_maximalIdeal_eq]
    exact adic_completion_integers_not_is_field R v K

local notation "v_adic_of_compl" =>
  @IsDedekindDomain.HeightOneSpectrum.valuation R_v _ _ _ K_v _ _ _ (maxIdealOfCompletion R v K)

local notation "v_compl_of_adic" => (Valued.v : Valuation K_v ℤₘ₀)

open LocalRing DiscretelyValued

theorem int_adic_of_compl_eq_int_compl_of_adic (a : R_v) :
    (maxIdealOfCompletion R v K).intValuation a = Valued.v (a : K_v) :=
  by
  by_cases ha : a = 0
  · simp only [ha, Valuation.map_zero, algebraMap.coe_zero]
  · rw [int_valuation_apply]
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, v_compl_of_adic a = of_add (-n : ℤ) :=
        by
        replace ha : v_compl_of_adic a ≠ 0 := by
          rwa [Valuation.ne_zero_iff, Ne.def, Subring.coe_eq_zero_iff]
        have := (mem_integer v_compl_of_adic ↑a).mp a.2
        obtain ⟨α, hα⟩ := with_zero.ne_zero_iff_exists.mp ha
        rw [← hα, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, ← ofAdd_toAdd α,
          Multiplicative.ofAdd_le] at this 
        obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat this
        use n
        rw [← hα, WithZero.coe_inj, ← ofAdd_toAdd α, hn]
      rw [hn, int_valuation_le_pow_iff_dvd]
      apply (DiscreteValuation.val_le_iff_dvd K_v _ n).mp (le_of_eq hn)
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, v_adic_of_compl a = of_add (-m : ℤ) :=
        by
        replace ha : v_adic_of_compl a ≠ 0 := by
          rwa [Valuation.ne_zero_iff, Ne.def, Subring.coe_eq_zero_iff]
        have : (max_ideal_of_completion R v K).Valuation (↑a : K_v) ≤ 1 := valuation_le_one _ _
        obtain ⟨α, hα⟩ := with_zero.ne_zero_iff_exists.mp ha
        rw [← hα, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, ← ofAdd_toAdd α,
          Multiplicative.ofAdd_le] at this 
        obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat this
        use m
        rw [← hα, WithZero.coe_inj, ← ofAdd_toAdd α, hm]
      erw [valuation_of_algebra_map, int_valuation_apply] at hm 
      rw [hm]
      replace hm := le_of_eq hm
      rw [int_valuation_le_pow_iff_dvd] at hm 
      rw [DiscreteValuation.val_le_iff_dvd K_v _ m]
      apply hm
      infer_instance
      infer_instance

theorem adic_of_compl_eq_compl_of_adic (x : K_v) : v_adic_of_compl x = v_compl_of_adic x :=
  by
  obtain ⟨a, b, H⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R_v) x
  have h1 := @valuation_of_mk' R_v _ _ _ K_v _ _ _ (max_ideal_of_completion R v K) a b
  have h2 :
    Valued.v (IsLocalization.mk' (adicCompletion K v) a b) =
      Valued.v (↑a : K_v) / Valued.v (↑b : K_v) :=
    by
    rw [div_eq_mul_inv, ← map_inv₀, ← Valuation.map_mul]
    apply congr_arg
    simp only [IsFractionRing.mk'_eq_div, ValuationSubring.algebraMap_apply, _root_.coe_coe,
      div_eq_mul_inv]
  rw [H] at h1 h2 
  rw [h1, h2]
  congr <;> apply int_adic_of_compl_eq_int_compl_of_adic

end IsDedekindDomain.HeightOneSpectrum.Completion

