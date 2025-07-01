/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.ForMathlib.WithZero
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.GroupTheory.SpecificGroups.Cyclic

import Mathlib.Algebra.GroupWithZero.Int

/-!
# Discrete Valuation Rings

In this file we prove basic results about Discrete Valuation Rings, building on the main definitions
provided in `RingTheory.DiscreteValuationRing.Basic`. We focus in particular on discrete
valuations and on `Valued` structures on the field of fractions of a DVR, as well as on a DVR
structure on the unit ball of a `Valued` field whose valuation is discrete.

## Main Definitions
* `IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is a
  uniformizer if `v π` is a generator of `Γ` that is `<1`.
* `Uniformizer`: A strucure bundling an element of a ring and a proof that it is a uniformizer.
* `base`: Given a valued field `K`, if the residue field of its unit ball (that is a local field)
  is finite, then `valuation_base` is the cardinal of the residue field, and otherwise it takes the
  value `6` which  is not a prime power.
* The `instance dvr_of_is_discrete` is the formalization of Chapter I, Section 1, Proposition 1 in
  Serre's **Local Fields** showing that the unit ball of a discretely-valued field is a DVR.


## Main Results
* `associated_of_Uniformizer` An element associated to a uniformizer is itself a uniformizer
* `Uniformizer_of_associated` If two elements are uniformizers, they are associated.
* `isUniformizer_is_generator` A generator of the maximal ideal is a uniformizer if the valuation
  is discrete.
* `isDiscrete_of_exists_isUniformizer` If there exists a uniformizer, the valuation is discrete.
* `exists_isUniformizer_of_isDiscrete` Conversely, if the valuation is discrete there exists a
  uniformizer.
* `IsUniformizer_of_generator` A uniformizer generates the maximal ideal.
* `discrete_valuation.is_discrete` Given a DVR, the valuation induced on its ring of fractions is
  discrete.
* `discrete_valuation.dvr_equiv_unit_ball` The ring isomorphism between a DVR and the unit ball in
  its field of fractions endowed with the adic valuation of the maximal ideal.

## Implementation details
In the section `discrete_valuation` we put a `valued` instance only on `fraction_field A`, where
`A` is the DVR, and not on any field `L` such that `[is_fraction_field A L]` because this creates
loops in the type-class inference mechanism.
-/
universe w₁ w₂

assert_not_exist isDiscrete

open Multiplicative

namespace WithZero

-- **Not PR'd for now: needed only for `ℤₘ₀`?**
instance (G : Type*) [Group G] [IsCyclic G] : IsCyclic (WithZero G)ˣ := by
    apply isCyclic_of_injective (G := (WithZero G)ˣ) (unitsWithZeroEquiv).toMonoidHom
    apply Equiv.injective

end WithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
namespace Valuation

section Ring

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

-- **Not PR'd for now: needed only to connect with norms?**
theorem base_ne_zero : base K v ≠ 0 :=
  ne_zero_of_lt (one_lt_base K v)

end Ring

open Function Ideal Multiplicative Polynomial Set Valuation WithZero

section Field

section IsRankOneDiscrete

variable {K : Type*} [Ring K] (v : Valuation K Γ) [hv : IsRankOneDiscrete v]

open Valuation LinearOrderedCommGroup

/-- An element `π : K` is a pre-uniformizer if `v π` generates `v.unitsMapRange` .-/
def IsPreuniformizer (π : K) : Prop := v π = hv.generator

@[simp]
lemma val_Preuniformizer {π : K} (hπ : v.IsPreuniformizer π) : v π = hv.generator := hπ

variable {v}

lemma isPreuniformizer_val_lt_one {π : K} (hπ : v.IsPreuniformizer π) : v π < 1 :=
  hπ ▸ hv.generator_lt_one

lemma isPreuniformizer_val_ne_zero {π : K} (hπ : v.IsPreuniformizer π) : v π ≠ 0 := by
  by_contra h0
  simp [IsPreuniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ

open MonoidHomWithZero Subgroup

lemma isPreuniformizer_val_generates_unitsMapRange {π : K} (hπ : v.IsPreuniformizer π) :
    valueGroup v = zpowers (Units.mk0 (v π) (v.isPreuniformizer_val_ne_zero hπ)) := by
  sorry/- rw [← v.unitsMapRange.genLTOne_zpowers_eq_top]
  congr
  simp_all [val_Preuniformizer, Units.mk0_val] -/

    --Units.mk0 (zpowers (v π)) (v.isPreuniformizer_val_ne_zero) := sorry--((/- WithZero.unitsMap  -/(v.isPreuniformizer_val_ne_zero hπ))) := by
  -- convert (Mul.exists_generator_lt_one ℤ v.unitsMapRange_ne_bot).choose_spec.2.symm
  -- rw [← WithZero.coe_inj, ← hπ, WithZero.coe_unitsMap]

variable (v) in
/-- The structure `Preuniformizer` bundles together the term in the ring and a proof that it is a
  preuniformizer.-/
@[ext]
structure Preuniformizer where
  /-- The integer underlying a `Preuniformizer` -/
  val : v.integer
  valuation_gt_one : v.IsPreuniformizer val

theorem isPreuniformizer_iff {π : K} :
    v.IsPreuniformizer π ↔ v π = hv.generator := refl _

/-- A constructor for preuniformizers.-/
def Preuniformizer.mk' {x : K} (hx : v.IsPreuniformizer x) :
    v.Preuniformizer where
  val := ⟨x, le_of_lt (v.isPreuniformizer_val_lt_one hx)⟩
  valuation_gt_one := hx

@[simp]
instance : Coe v.Preuniformizer v.integer := ⟨fun π ↦ π.val⟩

theorem isPreuniformizer_ne_zero {π : K} (hπ : IsPreuniformizer v π) : π ≠ 0 := by
  intro h0
  rw [h0, IsPreuniformizer, Valuation.map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

theorem preuniformizer_ne_zero (π : Preuniformizer v) : π.1.1 ≠ 0 :=
  isPreuniformizer_ne_zero π.2

theorem isPreuniformizer_val_pos {π : K} (hπ : IsPreuniformizer v π) : 0 < v π := by
  rw [isPreuniformizer_iff] at hπ ; simp [zero_lt_iff, ne_eq, hπ]

theorem isPreuniformizer_not_isUnit {π : v.integer} (hπ : IsPreuniformizer v π) : ¬ IsUnit π := by
  sorry
  /- intro h
  have h1 : v ((algebraMap (↥v.integer) K) π) = 1 :=
    Valuation.Integers.one_of_isUnit (Valuation.integer.integers v)  h
  exact ne_of_gt (isPreuniformizer_val_lt_one hπ) h1.symm -/


end IsRankOneDiscrete

section IsNontrivial

open MonoidHomWithZero

variable {K : Type*} [Ring K] (v : Valuation K Γ) [IsCyclic (valueGroup v)]
  [Nontrivial (valueGroup v)]

-- TODO: this
theorem IsRankOneDiscrete.mk' {π : K}
    (hπ : v π = (LinearOrderedCommGroup.genLTOne (valueGroup v)).1) :
    IsRankOneDiscrete v := by
  sorry/- apply IsRankOneDiscrete.mk
  use Units.mk0 (v π) (isPreuniformizer_val_ne_zero hπ)
  constructor
  · sorry
  · sorry -/
  /- simp [hπ, genLTOne_eq_of_top, Units.mk0_val]
  refine ⟨?_, by use π⟩
  simpa [Units.mk0_val, Subgroup.genLTOne_zpowers_eq_top, Subgroup.mem_top]
    using Subgroup.genLTOne_lt_one ⊤ -/

--TODO: unify with previous thm
/- theorem exists_isPreuniformizer_of_isNontrivial [v.IsNontrivial] [IsCyclic Γˣ] :
    ∃ π : K₀, IsPreuniformizer v (π : K) := by
  simp only [isPreuniformizer_iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  have : Nontrivial v.unitsMapRange := unitsMapRange_ne_bot v
  set g := (⊤ : Subgroup v.unitsMapRange).genLTOne with hg
  have hg_mem : g.1 ∈ v.unitsMapRange := SetLike.coe_mem ..
  obtain ⟨π, hπ⟩ := hg_mem
  use π.1
  constructor
  · apply le_of_lt
    rw [← unitsMap_apply, hπ]
    have := Subgroup.genLTOne_lt_one (H := v.unitsMapRange)
    rw [hg]
    rw [← Units.val_one]
    rw [Units.val_lt_val]
    rw [Subgroup.genLTOne_val_eq_genLTOne]
    exact this
  · rw [← unitsMap_apply, hπ, hg]
    rw [Subgroup.genLTOne_val_eq_genLTOne]
    -- **FAE : The above `splitting` should not be performed**


instance [IsNontrivial v] : Nonempty (Preuniformizer v) :=
  ⟨⟨(exists_isPreuniformizer_of_isNontrivial v).choose,
    (exists_isPreuniformizer_of_isNontrivial v).choose_spec⟩⟩ -/

end IsNontrivial

end Field

open LinearOrderedCommGroup


open scoped NNReal

section Field

open Valuation Ideal Multiplicative WithZero IsLocalRing

variable {K : Type w₁} [Field K] (v : Valuation K Γ)

/- When the valuation is defined over a field instead that simply on a (commutative) ring, we use
the notion of `valuation_subring` instead of the weaker one of `integer`s to access the
corresponding API. -/
local notation "K₀" => v.valuationSubring

section PreUniformizer

variable {v} [hv : v.IsRankOneDiscrete]

theorem isPreuniformizer_of_associated {π₁ π₂ : K₀} (h1 : IsPreuniformizer v π₁)
    (H : Associated π₁ π₂) : IsPreuniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 :=
    (Integers.isUnit_iff_valuation_eq_one <|integer.integers v).mp u.isUnit
  rwa [isPreuniformizer_iff, ← hu, Subring.coe_mul, Valuation.map_mul, this, mul_one,
    ← isPreuniformizer_iff]

theorem associated_of_isPreuniformizer (π₁ π₂ : Preuniformizer v) : Associated π₁.1 π₂.1 := by
  have hval : v ((π₁.1 : K)⁻¹ * π₂.1) = 1 := by
    simp [isPreuniformizer_iff.mp π₁.2, isPreuniformizer_iff.mp π₂.2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑·) : K₀ → K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ (isPreuniformizer_ne_zero π₁.2)]

theorem pow_preuniformizer {r : K₀} (hr : r ≠ 0) (π : Preuniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1 * u.1 := by
  sorry
  /- have hr₀ : v r ≠ 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr := unitsMap v (Units.mk0 r.1 (by norm_cast)) with hvr_def
  have hvr : vr ∈ v.unitsMapRange := by
    simp only [unitsMapRange, Subgroup.mem_mk, Set.mem_range, unitsMap_apply]
    have hr' : (r : K) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hr
    use Units.mk0 r hr'
  rw [isPreuniformizer_val_generates_unitsMapRange π.2, Subgroup.mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    simp [← v.unitsMap_of_ne_zero (x := r.1) (by norm_cast), ← hm]
  have hm₀ : 0 ≤ m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ (isPreuniformizer_val_pos π.2)
      (isPreuniformizer_val_lt_one π.2), hm']
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
    exact Or.inl (preuniformizer_ne_zero π)
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec, Subring.coe_pow, ha, ← mul_assoc, zpow_neg, hn, zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero _ (preuniformizer_ne_zero π)), one_mul] -/

theorem preuniformizer_is_generator (π : Preuniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} := by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply isPreuniformizer_not_isUnit π.2 h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp only [hx₀, Ideal.zero_mem]
    · obtain ⟨n, ⟨u, hu⟩⟩ := pow_preuniformizer hx₀ π
      rw [← Subring.coe_mul, Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h ↦
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n ≠ 0 := fun h ↦ by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp only [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit,
        dvd_pow_self _ hn]

theorem isPreuniformizer_is_generator {π : v.valuationSubring} (hπ : IsPreuniformizer v π) :
    maximalIdeal v.valuationSubring = Ideal.span {π} :=
  preuniformizer_is_generator ⟨π, hπ⟩

theorem pow_preuniformizer_is_pow_generator (π : Preuniformizer v) (n : ℕ) :
    maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow, preuniformizer_is_generator]

end PreUniformizer

theorem not_isField [IsNontrivial v] [IsCyclic Γˣ] : ¬ IsField K₀ := by
  sorry
  /- obtain ⟨π, hπ⟩ := exists_isPreuniformizer_of_isNontrivial v
  rintro ⟨-, -, h⟩
  have := isPreuniformizer_ne_zero hπ
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact isPreuniformizer_not_isUnit hπ h -/


theorem _root_.Valuation.isPreuniformizer_of_generator [v.IsRankOneDiscrete]
    {r : K₀} (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsPreuniformizer v r := by
  sorry
  /- have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isPreuniformizer_of_isNontrivial v
  obtain ⟨n, u, hu⟩ := pow_preuniformizer hr₀ ⟨π, hπ⟩
  rw [preuniformizer_is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact isPreuniformizer_of_associated hπ hr -/

/- **TODO** : reinstate -/
/- theorem val_le_iff_dvd {L : Type*} [Field L] {w : Valuation L Γ} [IsNontrivial w]
    [IsRankOneDiscrete w] [IsDiscreteValuationRing w.valuationSubring] (x : w.valuationSubring) (n : ℕ) :
    haveI := IsDiscrete.cyclic_value_group w
    haveI := IsDiscrete.nontrivial_value_group w
    w x ≤ (genLTOne Γˣ) ^ n ↔
      IsLocalRing.maximalIdeal w.valuationSubring ^ n ∣ Ideal.span {x} := by
  haveI := IsDiscrete.cyclic_value_group w
  haveI := IsDiscrete.nontrivial_value_group w
  by_cases hx : x = 0
  · rw [Ideal.span_singleton_eq_bot.mpr hx, hx, Subring.coe_zero, Valuation.map_zero]
    simp only [WithZero.zero_le, true_iff, ← Ideal.zero_eq_bot, dvd_zero, zero_le']
  · set r := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal w.valuationSubring)
      with hr_def
    have hr : IsPreuniformizer w r := by
      apply isPreuniformizer_of_generator
      rw [hr_def, span_singleton_generator]
    have hrn : w (r ^ n) =
        (genLTOne Γˣ) ^ n := by
      rw [Valuation.map_pow, hr]
      congr
      exact unitsMapRange_eq_top w
    have := @Valuation.Integers.le_iff_dvd L Γ _ _ w w.valuationSubring _ _
        (Valuation.integer.integers w) x (r ^ n)
    erw [← hrn, this]
    have DD : IsDedekindDomain w.valuationSubring := by
      apply IsPrincipalIdealRing.isDedekindDomain
    rw [← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal w.valuationSubring), ← hr_def,
      Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton', dvd_iff_exists_eq_mul_left]
    tauto -/

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

theorem ideal_isPrincipal [v.IsNontrivial] [IsCyclic Γˣ] (I : Ideal K₀) : I.IsPrincipal := by
  suffices ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  sorry
  /- intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Preuniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := pow_preuniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu, Ideal.mul_unit_mem_iff_mem P u.isUnit,
        IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn), ← Ideal.span_singleton_le_iff_mem,
        ← preuniformizer_is_generator π] at hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, preuniformizer_is_generator π⟩ -/

theorem integer_isPrincipalIdealRing [v.IsNontrivial] [IsCyclic Γˣ] : IsPrincipalIdealRing K₀ :=
  ⟨fun I ↦ ideal_isPrincipal v I⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
instance dvr_of_isDiscrete [v.IsNontrivial] [IsCyclic Γˣ] :
    IsDiscreteValuationRing K₀ where
  toIsPrincipalIdealRing := integer_isPrincipalIdealRing v
  toIsLocalRing  := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact not_isField v

end Field

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Subring IsDiscreteValuationRing
open Ideal IsLocalRing

/-- The maximal ideal of a DVR-/
def _root_.IsDiscreteValuationRing.maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by
    simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using IsDiscreteValuationRing.not_isField A

-- variable {A}

noncomputable instance instAdicValued : Valued (FractionRing A) ℤₘ₀ :=
  (IsDiscreteValuationRing.maximalIdeal A).adicValued

instance : IsRankOneDiscrete (instAdicValued A).v := by
  sorry/- apply isDiscrete_of_exists_isUniformizer
    (π := valuation_exists_uniformizer (FractionRing A) (maximalIdeal A)|>.choose)
  convert valuation_exists_uniformizer (FractionRing A) (maximalIdeal A)|>.choose_spec
  rw [← genLTOne_eq_of_top, ← Multiplicative.genLTOne_eq_neg_one]
  norm_cast -/

theorem exists_of_le_one {x : FractionRing A} (H : Valued.v x ≤ (1 : ℤₘ₀)) :
    ∃ a : A, algebraMap A (FractionRing A) a = x := by
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
      ← @IsFractionRing.mk'_mk_eq_div _ _ (FractionRing A) _ _ _ (π ^ n) _ hb] at H
    erw [@valuation_of_mk' A _ _ (FractionRing A) _ _ _ (maximalIdeal A) (π ^ n) ⟨π ^ m, hb⟩,
      _root_.map_pow, _root_.map_pow] at H
    have h_mn : m ≤ n :=
      by
      have π_lt_one :=
        (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have : (IsDiscreteValuationRing.maximalIdeal A).intValuation π ≠ 0 :=
        intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← WithZero.coe_one, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← ofAdd_zero, ← zpow_neg, ← zpow_add₀,
        ← sub_eq_add_neg] at H
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

variable {A}

theorem _root_.Valuation.algebraMap_eq_integers :
    Subring.map (algebraMap A (FractionRing A)) ⊤ = Valued.v.valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_of_le_one _ h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR and the unit ball in
  its field of fractions endowed with the adic valuation of the maximal ideal.-/
noncomputable def dvrEquivUnitBall :
    A ≃+* (@Valued.v (FractionRing A) _ ℤₘ₀ _ _).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A (FractionRing A))
    (IsFractionRing.injective A _))).trans (RingEquiv.subringCongr algebraMap_eq_integers)


end Valuation
