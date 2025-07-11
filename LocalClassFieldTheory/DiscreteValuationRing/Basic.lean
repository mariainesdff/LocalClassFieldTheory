/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
--import Mathlib.Algebra.Order.Group.Cyclic --**TODO**: reinstate after #26584 is merged.
import LocalClassFieldTheory.FromMathlib.Cyclic --**TODO**: remove after #26584 is merged.
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Discrete Valuation Rings

In this file we prove basic results about Discrete Valuation Rings. We focus in particular on
discrete valuations on the field of fractions of a DVR, as well as on a DVR
structure on the unit ball of a field with a discrete valuation.

## Main Definitions
* `Valuation.IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is
  a uniformizer if `v π` is a generator of the value group that is `<1`.
* `Valuation.Uniformizer`: A structure bundling an element of a ring and a proof that it is a
  uniformizer.

* `Valuation.base`: Given a valued field `K`, if the residue field of its unit ball (that is a
  local ring) is finite, then `Valuation.base` is the cardinal of the residue field, and otherwise
  it takes the value `6`, which is not a prime power.
* `Valuation.valuationSubring_isDiscreteValuationRing_of_isCyclic_of_Nontrivial`: this instance is
  the formalization of Chapter I, Section 1, Proposition 1 in [serre1968] showing that
  the unit ball of a discretely-valued field is a DVR.

## Main Results
* `Valuation.IsUniformizer.of_associated`: An element associated to a uniformizer is itself a
  uniformizer.
* `Valuation.associated_of_isUniformizer`: If two elements are uniformizers, they are associated.
* `Valuation.IsUniformizer.is_generator` A generator of the maximal ideal is a uniformizer when
  the valuation is discrete.
* `Valuation.IsRankOneDiscrete.mk'`: if the `valueGroup` of the valuation `v` is cyclic and
  nontrivial, then `v` is discrete.
* `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`: If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then there exists a uniformizer for `v`.
* `Valuation.isUniformizer_of_maximalIdeal_eq_span`: Given a discrete valuation `v` on a field `K`,
  a generator of the maximal ideal of `v.valuationSubring` is a uniformizer for `v`.
* `Valuation.valuationSubring_isDiscreteValuationRing` : If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then `v.valuationSubring` is a discrete
  valuation ring.
* `IsDiscreteValuationRing.isRankOneDiscrete`: Given a DVR `A` and a field `K` satisfying
  `IsFractionRing A K`, the valuation induced on `K` is discrete.
* `IsDiscreteValuationRing.equivValuationSubring` The ring isomorphism between a DVR and the
  unit ball in its field of fractions endowed with the adic valuation of the maximal ideal.


## References
* [Jean-Pierre Serre (1967), *Local class field theory*][serre1967]

* [Jean-Pierre Serre (1968), *Corps locaux*][serre1968]

-/
universe w₁ w₂

assert_not_exist isDiscrete

namespace WithZero

-- **Not PR'd for now: needed only for `ℤₘ₀`?**
instance (G : Type*) [Group G] [IsCyclic G] : IsCyclic (WithZero G)ˣ := by
    apply isCyclic_of_injective (G := (WithZero G)ˣ) (unitsWithZeroEquiv).toMonoidHom
    apply Equiv.injective

end WithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
namespace Valuation

-- **Not PR'd for now**: needed for `RankOne` instance.
section base

open scoped NNReal

-- **Not PR'd for now: needed only to connect with norms?**
variable (K : Type*) [Field K] (v : Valuation K Γ)
/-- If the residue field is finite, then `valuation_base` is the cardinal of the residue field, and
otherwise it takes the value `6` which is not a prime power.-/
noncomputable def base : ℝ≥0 :=
  if 1 < Nat.card (IsLocalRing.ResidueField v.valuationSubring) then
    Nat.card (IsLocalRing.ResidueField v.valuationSubring)
  else 6

-- **Not PR'd for now: needed only to connect with norms?**
theorem one_lt_base : 1 < base K v := by
  rw [base]
  split_ifs with hlt
  · rw [Nat.one_lt_cast]; exact hlt
  · norm_num

theorem base_ne_zero : base K v ≠ 0 :=
  ne_zero_of_lt (one_lt_base K v)

end base

section IsRankOneDiscrete

open LinearOrderedCommGroup MonoidHomWithZero Subgroup

section Ring

variable {R : Type*} [Ring R] {v : Valuation R Γ} [hv : IsRankOneDiscrete v]

--TODO: move after `generator_zpowers_eq_valueGroup`
lemma IsRankOneDiscrete.generator_zpowers_mem_valueGroup :
    (IsRankOneDiscrete.generator v) ∈ valueGroup v := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)

lemma valueGroup_genLTOne_eq_generator :
    Subgroup.genLTOne (valueGroup v) = IsRankOneDiscrete.generator v := by
  rw [eq_comm]
  apply (valueGroup v).genLTOne_unique
    ⟨IsRankOneDiscrete.generator v, IsRankOneDiscrete.generator_zpowers_mem_valueGroup⟩
  constructor
  · exact Subtype.coe_lt_coe.mp (IsRankOneDiscrete.generator_lt_one v)
  · have := IsRankOneDiscrete.generator_zpowers_eq_valueGroup v
    rw [eq_top_iff']
    intro x
    have hx : x.1 ∈ zpowers (IsRankOneDiscrete.generator v) := by
      rw [IsRankOneDiscrete.generator_zpowers_eq_valueGroup v]; exact x.2
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by ext1; exact hk⟩

variable (v) in
/-- An element `π : R` is a uniformizer if `v π` is a generator of the value group that is `< 1`. -/
def IsUniformizer (π : R) : Prop := v π = hv.generator

namespace IsUniformizer

theorem iff {π : R} : v.IsUniformizer π ↔ v π = hv.generator := refl _

theorem ne_zero {π : R} (hπ : IsUniformizer v π) : π ≠ 0 := by
  intro h0
  rw [h0, IsUniformizer, Valuation.map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

@[simp]
lemma val {π : R} (hπ : v.IsUniformizer π) : v π = hv.generator := hπ

lemma val_lt_one {π : R} (hπ : v.IsUniformizer π) : v π < 1 :=
  hπ ▸ hv.generator_lt_one

lemma val_ne_zero {π : R} (hπ : v.IsUniformizer π) : v π ≠ 0 := by
  by_contra h0
  simp [IsUniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ

theorem val_pos {π : R} (hπ : IsUniformizer v π) : 0 < v π := by
  rw [IsUniformizer.iff] at hπ ; simp [zero_lt_iff, ne_eq, hπ]

lemma zpowers_eq_valueGroup {π : R} (hπ : v.IsUniformizer π) :
    valueGroup v = zpowers (Units.mk0 (v π) hπ.val_ne_zero) := by
  rw [← (valueGroup v).genLTOne_zpowers_eq_top]
  congr
  simp_all [IsUniformizer.val, Units.mk0_val]
  exact valueGroup_genLTOne_eq_generator

end IsUniformizer

variable (v) in
/-- The structure `Uniformizer` bundles together the term in the ring and a proof that it is a
  Uniformizer.-/
@[ext]
structure Uniformizer where
  /-- The integer underlying a `Uniformizer` -/
  val : v.integer
  valuation_gt_one : v.IsUniformizer val

namespace Uniformizer

/-- A constructor for Uniformizers.-/
def mk' {x : R} (hx : v.IsUniformizer x) : v.Uniformizer where
  val := ⟨x, le_of_lt hx.val_lt_one⟩
  valuation_gt_one := hx

@[simp]
instance : Coe v.Uniformizer v.integer := ⟨fun π ↦ π.val⟩

theorem ne_zero (π : Uniformizer v) : π.1.1 ≠ 0 := π.2.ne_zero

end Uniformizer

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : Valuation R Γ} [hv : IsRankOneDiscrete v]

theorem IsUniformizer.not_isUnit {π : v.integer} (hπ : IsUniformizer v π) : ¬ IsUnit π := by
  intro h
  have h1 : v ((algebraMap (↥v.integer) R) π) = 1 :=
    Valuation.Integers.one_of_isUnit (Valuation.integer.integers v)  h
  exact ne_of_gt hπ.val_lt_one h1.symm

end CommRing

end IsRankOneDiscrete

section Ring

open LinearOrderedCommGroup MonoidHomWithZero

variable {R : Type*} [Ring R] (v : Valuation R Γ) [IsCyclic (valueGroup v)]
  [Nontrivial (valueGroup v)]

instance IsRankOneDiscrete.mk' : IsRankOneDiscrete v :=
  ⟨(valueGroup v).genLTOne,
    ⟨(valueGroup v).genLTOne_zpowers_eq_top, (valueGroup v).genLTOne_lt_one⟩⟩

end Ring

section Field

open Ideal IsLocalRing LinearOrderedCommGroup MonoidHomWithZero Set

variable {K : Type*} [Field K] (v : Valuation K Γ)

/- When the valuation is defined over a field instead that simply on a (commutative) ring, we use
the notion of `valuationSubring` instead of the weaker one of `integer` to access the
corresponding API. -/
local notation "K₀" => v.valuationSubring

section IsNontrivial

variable [IsCyclic (valueGroup v)] [Nontrivial (valueGroup v)]

theorem exists_isUniformizer_of_isCyclic_of_nontrivial : ∃ π : K₀, IsUniformizer v (π : K) := by
  simp only [IsUniformizer.iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  set g := (valueGroup v).genLTOne with hg
  have hg_mem : g.1 ∈ ((range v) \ {0}) := by
    rw [← valueGroup_eq_range, hg]
    exact mem_image_of_mem Units.val (valueGroup v).genLTOne_mem
  obtain ⟨⟨π, hπ⟩, hγ0⟩ := hg_mem
  use π
  rw [hπ, hg]
  exact ⟨le_of_lt (valueGroup v).genLTOne_lt_one, by rw [valueGroup_genLTOne_eq_generator]⟩

instance : Nonempty (Uniformizer v) :=
  ⟨⟨(exists_isUniformizer_of_isCyclic_of_nontrivial v).choose,
    (exists_isUniformizer_of_isCyclic_of_nontrivial v).choose_spec⟩⟩

end IsNontrivial

section IsRankOneDiscrete

section Uniformizer

variable {v} [hv : v.IsRankOneDiscrete]

/-- An element associated to a uniformizer is itself a uniformizer.-/
theorem IsUniformizer.of_associated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (H : Associated π₁ π₂) : IsUniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 :=
    (Integers.isUnit_iff_valuation_eq_one <|integer.integers v).mp u.isUnit
  rwa [IsUniformizer.iff, ← hu, Subring.coe_mul, Valuation.map_mul, this, mul_one,
    ← IsUniformizer.iff]

/-- If two elements of `K₀` are uniformizers, then they are associated.-/
theorem associated_of_isUniformizer {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (h2 : IsUniformizer v π₂): Associated π₁ π₂ := by
  have hval : v ((π₁ : K)⁻¹ * π₂) = 1 := by
    simp [IsUniformizer.iff.mp h1, IsUniformizer.iff.mp h2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑·) : K₀ → K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ h1.ne_zero]

theorem pow_Uniformizer {r : K₀} (hr : r ≠ 0) (π : Uniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1 * u.1 := by
  have hr₀ : v r ≠ 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr : Γˣ := Units.mk0 (v r) hr₀ with hvr_def
  have hvr : vr ∈ (valueGroup v) := by
    apply mem_valueGroup
    rw [hvr_def, Units.val_mk0 hr₀]
    exact mem_range_self _
  rw [π.2.zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    rw [← Units.val_mk0 hr₀, ← hm]
    simp [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hm₀ : 0 ≤ m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ π.2.val_pos π.2.val_lt_one, hm']
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [Valuation.map_mul, map_zpow₀, ← hm', zpow_neg, hm', inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) ≠ 0 := by
    simp only [zpow_neg, ne_eq, mul_eq_zero, inv_eq_zero, ZeroMemClass.coe_eq_zero, not_or, ha]
    refine ⟨?_, hr⟩
    rw [hn, zpow_natCast, pow_eq_zero_iff', not_and_or]
    exact Or.inl π.ne_zero
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec, Subring.coe_pow, ha, ← mul_assoc, zpow_neg, hn, zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero _ π.ne_zero), one_mul]

theorem Uniformizer.is_generator (π : Uniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} := by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply π.2.not_isUnit h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp only [hx₀, Ideal.zero_mem]
    · obtain ⟨n, ⟨u, hu⟩⟩ := pow_Uniformizer hx₀ π
      rw [← Subring.coe_mul, Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h ↦
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n ≠ 0 := fun h ↦ by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp only [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit,
        dvd_pow_self _ hn]

theorem IsUniformizer.is_generator {π : v.valuationSubring} (hπ : IsUniformizer v π) :
    maximalIdeal v.valuationSubring = Ideal.span {π} :=
  Uniformizer.is_generator ⟨π, hπ⟩

theorem pow_Uniformizer_is_pow_generator (π : Uniformizer v) (n : ℕ) :
    maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow, Uniformizer.is_generator]

end Uniformizer

end IsRankOneDiscrete

theorem not_isField [Nontrivial ↥(valueGroup v)] [IsCyclic (valueGroup v)] : ¬ IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

instance IsRankOneDiscrete.IsNontrivial [v.IsRankOneDiscrete] : v.IsNontrivial := sorry

theorem isUniformizer_of_maximalIdeal_eq_span [v.IsRankOneDiscrete] {r : K₀}
    (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsUniformizer v r := by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

-- **TODO**: PR when used.
theorem val_le_iff_dvd {L : Type*} [Field L] {w : Valuation L Γ} [hw : IsRankOneDiscrete w]
    [IsDiscreteValuationRing w.valuationSubring] (x : w.valuationSubring) (n : ℕ) :
    w x ≤ (hw.generator) ^ n ↔
      IsLocalRing.maximalIdeal w.valuationSubring ^ n ∣ Ideal.span {x} := by
  haveI := IsRankOneDiscrete.IsNontrivial w
  by_cases hx : x = 0
  · rw [Ideal.span_singleton_eq_bot.mpr hx, hx, Subring.coe_zero, Valuation.map_zero]
    simp only [← Ideal.zero_eq_bot, dvd_zero, zero_le']
  · set r := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal w.valuationSubring)
      with hr_def
    have hr : IsUniformizer w r := by
      apply isUniformizer_of_maximalIdeal_eq_span
      rw [hr_def, span_singleton_generator]
    have hrn : w (r ^ n) =
        (hw.generator) ^ n := by
      rw [Valuation.map_pow, hr]
    have := @Valuation.Integers.le_iff_dvd L Γ _ _ w w.valuationSubring _ _
        (Valuation.integer.integers w) x (r ^ n)
    erw [← hrn, this]
    have DD : IsDedekindDomain w.valuationSubring := by
      apply IsPrincipalIdealRing.isDedekindDomain
    rw [← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal w.valuationSubring), ← hr_def,
      Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton', dvd_iff_exists_eq_mul_left]
    tauto

/--  **TODO**: reinstate after Mathlib PRs. -/
/- section RankOne

open Valuation

variable [v.IsDiscrete]
-- variable [v.IsNontrivial] **FAE** This was the old assumption, do you prefer that one?

open Classical in
noncomputable instance _root_.DiscreteValuation.rankOne : RankOne v where
  hom := by
    let φ := choice <| IsDiscrete.nonempty_mulOrderIso_multiplicative_int v
    use (WithZeroMulInt.toNNReal (base_ne_zero K v)).comp (φ : Γ →*₀ ℤₘ₀) <;> simp
  strictMono' := by
    have := WithZeroMulInt.toNNReal_strictMono (one_lt_base K v)
    simp
    exact StrictMono.comp this <| OrderMonoidIso.strictMono ..
  nontrivial' := by
    have := IsDiscrete.nontrivial_value_group v
    have := IsDiscrete.cyclic_value_group v
    use (exists_isUniformizer_of_isDiscrete (v := v)).choose
    rw [(exists_isUniformizer_of_isDiscrete _).choose_spec]
    exact ⟨Units.ne_zero _, ne_of_lt <| (⊤ : Subgroup Γˣ).genLTOne_lt_one⟩

end RankOne -/

theorem ideal_isPrincipal [IsCyclic (valueGroup v)] [Nontrivial (valueGroup v)] (I : Ideal K₀) :
    I.IsPrincipal := by
  suffices ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := pow_Uniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu, Ideal.mul_unit_mem_iff_mem P u.isUnit,
        IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn), ← Ideal.span_singleton_le_iff_mem,
        ← π.is_generator ] at hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, π.is_generator⟩

theorem valuationSubring_isPrincipalIdealRing [IsCyclic (valueGroup v)] [Nontrivial (valueGroup v)] :
    IsPrincipalIdealRing K₀ := ⟨fun I ↦ ideal_isPrincipal v I⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
instance valuationSubring_isDiscreteValuationRing [IsCyclic (valueGroup v)]
    [Nontrivial (valueGroup v)] : IsDiscreteValuationRing K₀ where
  toIsPrincipalIdealRing := valuationSubring_isPrincipalIdealRing v
  toIsLocalRing := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact not_isField v

end Field

end Valuation

namespace IsDiscreteValuationRing

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing Multiplicative Subring Valuation

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The maximal ideal of a DVR-/
def maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by
    simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

instance isRankOneDiscrete :
    IsRankOneDiscrete ((maximalIdeal A).valuation K) := by
  have : Nontrivial ↥(MonoidHomWithZero.valueGroup (valuation K (maximalIdeal A))) := by
    let v := (maximalIdeal A).valuation K
    set π := valuation_exists_uniformizer K (maximalIdeal A)|>.choose with hπ_def
    have hπ : v π = ↑(ofAdd (-1 : ℤ)) :=
      valuation_exists_uniformizer K (maximalIdeal A)|>.choose_spec
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    use Units.mk0 (v π) (by simp [hπ])
    constructor
    · apply MonoidHomWithZero.mem_valueGroup
      simp only [Units.val_mk0, Set.mem_range]
      use π
    · simp only [hπ]
      exact not_eq_of_beq_eq_false rfl
  apply IsRankOneDiscrete.mk'

variable {A K}

theorem exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x ≤ (1 : ℤₘ₀)) :
    ∃ a : A, algebraMap A K a = x := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, ⟨b, ⟨hb, h_frac⟩⟩⟩ := IsFractionRing.div_surjective (A := A) x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha, _root_.map_zero, zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    replace hb := (mul_mem_nonZeroDivisors.mp hb).2
    rw [mul_comm (w : A) _, _root_.map_mul _ (u : A) _, _root_.map_mul _ _ (w : A),
      div_eq_mul_inv, mul_assoc, Valuation.map_mul, Integers.one_of_isUnit' u.isUnit,
      one_mul, mul_inv, ← mul_assoc, Valuation.map_mul, _root_.map_mul] at H
    simp only [map_inv₀] at H
    rw [Integers.one_of_isUnit' w.isUnit, inv_one, mul_one, ← div_eq_mul_inv, ← map_div₀,
      ← @IsFractionRing.mk'_mk_eq_div _ _ K _ _ _ (π ^ n) _ hb] at H
    erw [@valuation_of_mk' A _ _ K _ _ _ (maximalIdeal A) (π ^ n) ⟨π ^ m, hb⟩,
      _root_.map_pow, _root_.map_pow] at H
    have h_mn : m ≤ n := by
      have π_lt_one :=
        (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have : (maximalIdeal A).intValuation π ≠ 0 := intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← WithZero.coe_one, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← ofAdd_zero,
        ← zpow_neg, ← zpow_add₀, ← sub_eq_add_neg] at H
      rw [← sub_nonneg, ← zpow_le_one_iff_right_of_lt_one₀ _ π_lt_one]
      exacts [H, zero_lt_iff.mpr this, this]
    use u * π ^ (n - m) * w.2
    simp only [← h_frac, Units.inv_eq_val_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebraMap A _) ↑u) _ _]
    congr 1
    rw [div_eq_mul_inv, mul_inv, mul_comm ((algebraMap A _) ↑w)⁻¹ _, ←
      mul_assoc _ _ ((algebraMap A _) ↑w)⁻¹]
    congr
    rw [pow_sub₀ _ _ h_mn]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exacts [hπ.ne_zero, valuation_le_one (maximalIdeal A), valuation_le_one (maximalIdeal A)]

theorem map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ =
    ((maximalIdeal A).valuation K).valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR `A` and the valuation subring of a field of fractions
  of `A` endowed with the adic valuation of the maximal ideal. -/
noncomputable def equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

end IsDiscreteValuationRing
