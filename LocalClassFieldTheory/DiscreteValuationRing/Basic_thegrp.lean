/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.ForMathlib.WithZero
import LocalClassFieldTheory.FromMathlib.Yakov
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
-- import Mathlib.RingTheory.Valuation.Discrete.Basic -- importing `Yakov` that imports `FromMathlib.DiscreteBasic` instead
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

section Subgroup
-- **NOT NEEDED ANYMORE**
-- theorem AddSubgroup.toSubgroup_closure {A : Type} [AddGroup A] (S : Set A) :
--     AddSubgroup.toSubgroup (AddSubgroup.closure S) =
--       Subgroup.closure (Multiplicative.toAdd ⁻¹' S) :=
--   le_antisymm
--     (AddSubgroup.toSubgroup.to_galoisConnection.l_le <|
--       (AddSubgroup.closure_le _).2 <| Subgroup.subset_closure (G := Multiplicative A))
--     ((Subgroup.closure_le _).2 <| AddSubgroup.subset_closure (G := A))
--
-- theorem Subgroup.toAddSubgroup_closure {G : Type} [Group G] (S : Set G) :
--     Subgroup.toAddSubgroup (Subgroup.closure S) =
--       AddSubgroup.closure (Additive.toMul ⁻¹' S) :=
--   le_antisymm
--     (Subgroup.toAddSubgroup.le_symm_apply.1 <|
--       (Subgroup.closure_le _).2 (AddSubgroup.subset_closure (G := Additive G)))
--     ((AddSubgroup.closure_le _).2 (Subgroup.subset_closure (G := G)))
--
-- theorem Subgroup.toAddSubgroup_toSubgroup' {G : Type*} [Group G] (H : Subgroup G) :
--     AddSubgroup.toSubgroup' (Subgroup.toAddSubgroup H) = H := by
--   ext x
--   simp only [OrderIso.symm_apply_apply]

--TODO: use this in DVR.Extensions.

-- **In PR #21361**
/- @[to_additive]
theorem Subgroup.isCyclic_iff_exists_zpowers_eq_top {α : Type*} [Group α] (H : Subgroup α) :
    IsCyclic H ↔ ∃ g : α, Subgroup.zpowers g = H := by
  rw [_root_.isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨fun ⟨⟨k, k_mem⟩, hk⟩ ↦ ⟨k, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨⟨k, zpowers_le.mp <| le_of_eq hk⟩, ?_⟩⟩
  · simp [← range_subtype H, ← Subgroup.map_eq_range_iff.mpr, hk,
      ← (coeSubtype H ▸ (H.subtype).map_zpowers ⟨k, k_mem⟩)]
  · apply_fun Subgroup.map H.subtype using Subgroup.map_injective <| subtype_injective H
    simp [(H.subtype).map_zpowers ⟨k, _⟩, coeSubtype, hk, Subgroup.map_eq_range_iff.mpr,
      range_subtype] -/

-- **from here... #1**
-- namespace Subgroup
--
-- variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [IsCyclic G]
-- variable (H : Subgroup G) [Nontrivial H]
--
-- lemma exists_generator_lt_one : ∃ (a : G), a < 1 ∧ Subgroup.zpowers a = H := by
--   have h_cyc := Subgroup.isCyclic H
--   obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp h_cyc
--   by_cases ha1 : a < 1
--   · use a, ha1, ha
--   · simp only [not_lt, le_iff_eq_or_lt] at ha1
--     rcases ha1 with (ha1 | ha1)
--     · rw [← ha1, Subgroup.zpowers_one_eq_bot] at ha
--       exact absurd ha.symm <| (H.nontrivial_iff_ne_bot).mp (by infer_instance)
--     · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
--       rw [Subgroup.zpowers_inv, ha]
--
-- protected noncomputable
-- def genLTOne : G := H.exists_generator_lt_one.choose
--
-- lemma genLTOne_lt_one (H : Subgroup G) [Nontrivial H] : H.genLTOne < 1 :=
--     H.exists_generator_lt_one.choose_spec.1
--
-- @[simp]
-- lemma genLTOne_zpowers_eq_top (H : Subgroup G) [Nontrivial H] :
--     Subgroup.zpowers H.genLTOne = H :=
--   H.exists_generator_lt_one.choose_spec.2
--
-- -- It is in **23589**
-- -- instance {G : Type*} [Group G] [Nontrivial G] : Nontrivial (⊤ : Subgroup G) := by
-- --   rw [nontrivial_iff_ne_bot]
-- --   exact top_ne_bot
--
-- end Subgroup
--
-- namespace LinearOrderedCommGroup
--
-- variable (G : Type*) [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [IsCyclic G] [Nontrivial G]
--
-- noncomputable
-- def genLTOne : G := (⊤ : Subgroup G).genLTOne
--
-- @[simp]
-- lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl
--
-- end LinearOrderedCommGroup
-- **...to here #1: in PR#23725**

-- **FAE** The four lemmas below seem only needed for `ℤₘ₀`.
-- @[simp]
-- lemma MultInt.zpowers_ofAdd_neg_one : Subgroup.zpowers (ofAdd (-1)) = ⊤ := by
--   simp only [Int.reduceNeg, ofAdd_neg, Subgroup.zpowers_inv, Subgroup.eq_top_iff',
--     Multiplicative.forall]
--   intro z
--   use z
--   simp [Int.reduceNeg, ofAdd_neg, zpow_neg, inv_zpow', inv_inv, ← Int.ofAdd_mul, one_mul]
-- --
-- theorem MultInt.mem_zpowers_iff {a b : Multiplicative ℤ} :
--     b ∈ Subgroup.zpowers a ↔ toAdd a ∣ toAdd b := by
--   rw [Subgroup.mem_zpowers_iff, dvd_iff_exists_eq_mul_left]
--   exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [← smul_eq_mul, ← toAdd_zpow, hk]⟩,
--     fun ⟨k, hk⟩ ↦ ⟨k, by rw [← ofAdd_toAdd b, hk, mul_comm k, Int.ofAdd_mul, ofAdd_toAdd]⟩⟩
-- --
-- lemma Int.eq_neg_one_of_dvd_one {a : ℤ} (H : a ≤ 0) (H' : a ∣ 1) : a = -1 := by
--   replace H' := H'.choose_spec
--   rw [Eq.comm, Int.mul_eq_one_iff_eq_one_or_neg_one] at H'
--   simp_all [show a ≠ 1 from (by linarith)]
--
-- --
-- lemma MultInt.eq_ofAdd_neg_one_of_generates_top {a : Multiplicative ℤ} (ha1 : a < 1)
--     (ha : Subgroup.zpowers a = ⊤) : a = ofAdd (-1) := by
--   rw [← MultInt.zpowers_ofAdd_neg_one] at ha
--   have hin : ofAdd (-1) ∈ Subgroup.zpowers a := ha ▸ Subgroup.mem_zpowers _
--   rw [MultInt.mem_zpowers_iff] at hin
--   simp only [Int.reduceNeg, ofAdd_neg, toAdd_inv, toAdd_ofAdd, IsUnit.neg_iff, isUnit_one,
--     IsUnit.dvd, dvd_neg] at hin
--   rw [← ofAdd_toAdd a, Int.eq_neg_one_of_dvd_one (le_of_lt ha1) hin]
--   rfl

end Subgroup

namespace WithZero

-- class IsCyclic₀ (Γ : Type*) [GroupWithZero Γ] : Prop where
--   cyclicUnits : IsCyclic Γˣ

-- instance (Γ : Type*) [GroupWithZero Γ] [IsCyclic Γˣ] : IsCyclic Γˣ := IsCyclic₀.cyclicUnits

-- **Not PR'd for now: needed only for `ℤₘ₀`?**
instance (G : Type*) [Group G] [IsCyclic G] : IsCyclic (WithZero G)ˣ := by
    apply isCyclic_of_injective (G := (WithZero G)ˣ) (unitsWithZeroEquiv).toMonoidHom
    apply Equiv.injective


end WithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
namespace Valuation

section Field

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

end Field

-- variable {A : Type w₁} [CommRing A]

namespace Integer

-- **not needed anymore**
-- theorem isUnit_iff_valuation_eq_one' {K : Type w₁} [Field K] {Γ₀ : Type w₂}
--     [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (x : v.integer) :
--     IsUnit x ↔ v x = 1 := by
--   apply Integers.isUnit_iff_valuation_eq_one
--   exact integer.integers v
  -- refine ⟨@Integers.one_of_isUnit K Γ₀ _ _ v v.integer _ _ (Valuation.integer.integers v) _,
  --   fun hx ↦ ?_⟩
  -- have hx0 : (x : K) ≠ 0 := by
  --   by_contra h0
  --   rw [h0, map_zero] at hx
  --   exact zero_ne_one hx
  -- have hx' : v (x : K)⁻¹ = (1 : Γ₀) := by rw [map_inv₀, inv_eq_one]; exact hx
  -- rw [isUnit_iff_exists_inv]
  -- use! (x : K)⁻¹, le_of_eq hx'
  -- · ext; simp only [Subring.coe_mul, ne_eq, ZeroMemClass.coe_eq_zero, OneMemClass.coe_one,
  --     mul_inv_cancel₀ hx0]
/- -- **IN PR #23408**
theorem not_isUnit_iff_valuation_lt_one {K : Type*} [Field K] {v : Valuation K Γ} (x : v.integer) :
    ¬IsUnit x ↔ v x < 1 := by
  rw [← not_le, not_iff_not, Integers.isUnit_iff_valuation_eq_one (F := K) (Γ₀ := Γ),
    le_antisymm_iff]
  exacts [and_iff_right x.2, integer.integers v] -/
--
-- protected theorem _root_.ValuationSubring.mem_maximalIdeal
-- {K : Type*} {Γ₀ : Type*} [Field K]
--     [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (a : v.valuationSubring) :
--     a ∈ IsLocalRing.maximalIdeal (v.valuationSubring) ↔ v a < 1 :=
--   Integer.not_isUnit_iff_valuation_lt_one a


end Integer

open Function Set

-- In PR #21371
/-We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `WithZero.multiplicative (- 1) : ℤₘ₀`-/
-- class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
--   one_mem_range : (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) ∈ range v

-- In PR #21371
-- lemma IsDiscrete.surj {K : Type*} [Field K] (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
--     Surjective v := by
--   refine fun c ↦ WithOne.cases_on c ⟨0, map_zero _⟩ (fun a ↦ ?_)
--   obtain ⟨π, hπ⟩ := hv
--   use π ^ (- a.toAdd)
--   rw [map_zpow₀, hπ]
--   simp only [ofAdd_neg, WithZero.coe_inv, zpow_neg, inv_zpow', inv_inv, ← WithZero.ofAdd_zpow]
--   rfl

-- In PR #21371
-- lemma isDiscrete_iff_surjective {K : Type*} [Field K] (v : Valuation K ℤₘ₀) :
--     IsDiscrete v ↔ Surjective v :=
--   ⟨fun _ ↦ IsDiscrete.surj v, fun hv ↦ ⟨hv (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)⟩⟩

open Polynomial

open Valuation Ideal Multiplicative WithZero

-- variable {R : Type w₁} [CommRing R] (vR : Valuation R ℤₘ₀)

-- This seems now (March 25) useless
-- def unitsMap' (h0 : ∀ {x : R}, x ≠ 0 → vR x ≠ 0) : {x : R // x ≠ 0} → Multiplicative ℤ :=
--     fun x ↦ WithZero.unitsMap (h0 x.2)
--
-- def unitsMap'_range [Nontrivial R] [IsDomain R] (h0 : ∀ {x : R}, x ≠ 0 → vR x ≠ 0) :
--     Submonoid (Multiplicative ℤ) where
--   carrier := range (vR.unitsMap' h0)
--   mul_mem' hx hy := by
--     simp only [mem_range, Subtype.exists] at *
--     obtain ⟨a, ha, rfl⟩ := hx
--     obtain ⟨b, hb, rfl⟩ := hy
--     use a * b, mul_ne_zero ha hb
--     simp [unitsMap', _root_.map_mul, unitsMap_mul]
--   one_mem' := by
--     use ⟨(1 : R), one_ne_zero⟩
--     simp only [unitsMap', _root_.map_one, unitsMap_coe]
--     rfl

/- -- **from here... #2**
section IsNontrivial

variable {R : Type*} [Ring R] (v : Valuation R Γ)

/-- A valuation on a ring is nontrivial if there exists an element with valuation
not equal to `0` or `1`. -/
class IsNontrivial : Prop where
  exists_val_ne_one : ∃ x : R, v x ≠ 1 ∧ v x ≠ 0

/-- For fields, being nontrivial is equivalent to the existence of a unit with valuation
not equal to `1`. -/
lemma isNontrivial_iff_exists_unit {K : Type*} [Field K] {w : Valuation K Γ} :
    w.IsNontrivial ↔ ∃ x : Kˣ, w x ≠ 1 :=
  ⟨fun ⟨x, hx1, hx0⟩ ↦ ⟨Units.mk0 x (w.ne_zero_iff.mp hx0), hx1⟩,
    fun ⟨x, hx⟩ ↦ ⟨x, hx, w.ne_zero_iff.mpr (Units.ne_zero x)⟩⟩

end IsNontrivial
-- **to here #2: in PR #23726** -/

-- **from here #3...**
-- section IsDiscrete -- (of course, this has been renamed `IsDiscrete` in the PR)
--
-- variable {R : Type*} [Ring R]
--
-- /-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is cyclic, a valuation
-- `v : R → Γ` on a ring `R` is discrete, if `genLTOne Γˣ` belongs to the image. When `Γ := ℤₘ₀`, the
--   latter is equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to
--   asking that `1 : ℤ` belongs to the image of the corresponding *additive* valuation. -/
-- class IsDiscrete [IsCyclic Γˣ] [Nontrivial Γˣ] (v : Valuation R Γ) : Prop where
--   exists_generator_lt_one : ∃ (γ :Γˣ), Subgroup.zpowers γ = ⊤ ∧ γ < 1 ∧ ↑γ ∈ range v
--   -- glb_generator_mem : ∀ g h : Γ₀ˣ, Subgroup.zpowers g = ⊤ →
--   --   Subgroup.zpowers h = ⊤ → g ≤ h → (g : Γ₀) ∈ range v
--
-- variable {K : Type*} [Field K]
--
-- variable [IsCyclic Γˣ] [Nontrivial Γˣ]
--
-- /-- A discrete valuation on a field `K` is surjective. -/
-- lemma IsDiscrete.surj (w : Valuation K Γ) [hv : IsDiscrete w] : Surjective w := by
--   intro c
--   by_cases hc : c = 0
--   · exact ⟨0, by simp [hc]⟩
--   obtain ⟨π, hπ_gen, hπ_lt_one, a, ha⟩ := hv
--   set u : Γˣ := Units.mk0 c hc with hu
--   obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hπ_gen ▸ Subgroup.mem_top u)
--   use a^k
--   rw [map_zpow₀, ha]
--   norm_cast
--   rw [hk, hu, Units.val_mk0]
--
-- open LinearOrderedCommGroup
--
-- /-- A `Γ`-valued valuation on a field `K` is discrete if and only if it is surjective. -/
-- lemma isDiscrete'_iff_surjective (w : Valuation K Γ) :
--     IsDiscrete w ↔ Surjective w := by
--   refine ⟨fun _ ↦ IsDiscrete.surj w, fun h ↦ ⟨genLTOne Γˣ, by simp, ?_, by apply h⟩⟩
--   simpa using (⊤ : Subgroup Γˣ).genLTOne_lt_one

-- lemma Int.generator_eq_one_or_neg_one {a : ℤ} (ha : AddSubgroup.zmultiples a = ⊤) :
--    a = 1 ∨ a = -1 := sorry
--
-- lemma MulInt.generator_eq_one_or_neg_one {a : Multiplicative ℤ} (ha : Subgroup.zpowers a = ⊤) :
--    a = ofAdd 1 ∨ a = ofAdd (-1 : ℤ) := sorry
--
-- lemma IsDiscrete_of_neg_one_mem_range (w : Valuation R ℤₘ₀) [IsDiscrete w] : IsDiscrete w := by
--   constructor
--   have neg_one_unit : (↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ≠ 0 := by norm_cast
--   use Units.mk0 _ neg_one_unit
--   constructor
--   · sorry -- see below
--   · constructor
--     · sorry--rw [← WithZero.coe_unitsWithZeroEquiv_eq_units_val]
--     · apply IsDiscrete.one_mem_range


  -- intro m n hm hn hmn
  -- have hm' : Subgroup.zpowers (unitsWithZeroEquiv m) = ⊤ := by
  --   erw [← MonoidHom.map_zpowers (unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom m, hm]
  --   rw [Subgroup.map_top_of_surjective (unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom]
  --   apply Equiv.surjective
  -- have hn' : Subgroup.zpowers (unitsWithZeroEquiv n) = ⊤ := by
  --   erw [← MonoidHom.map_zpowers (unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom n, hn]
  --   rw [Subgroup.map_top_of_surjective (unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom]
  --   apply Equiv.surjective
  -- have : (m : ℤₘ₀) = ↑((ofAdd (-1 : ℤ)) : Multiplicative ℤ) := by
  --   -- let φ : Subgroup ℤₘ₀ˣ → Subgroup (Multiplicative ℤ) :=
  --   --     fun H ↦ Subgroup.map (ℤₘ₀ˣ) (unitsWithZeroEquiv).toMonoidHom H
  --   rw [← WithZero.coe_unitsWithZeroEquiv_eq_units_val (γ := m)]
  --   sorry
  -- rw [this]
  -- exact IsDiscrete.one_mem_range


-- end IsDiscrete
-- **to here #3: in PR #23726**

section Field

variable {K : Type*} [Field K] (v : Valuation K Γ)


/-- `Valuation.unitsMap` is the `MonoidHom` obtained by restricting a valuation to the non-zero
  elements of the ring. -/
noncomputable def unitsMap : Kˣ →* Γˣ where
  toFun := fun x ↦ Units.mk0 _ (ne_zero_of_unit v x)
  map_one' := by simp
  map_mul' := fun x y ↦ by simp

@[simp, norm_cast]
lemma unitsMap_apply (x : Kˣ) : v.unitsMap x = v x.1 := by
  simp only [unitsMap, Units.val_mk0, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0]

@[simp, norm_cast]
lemma unitsMap_of_ne_zero {x : K} (hx : x ≠ 0) : v.unitsMap (Units.mk0 x hx) = v x := rfl

/-- The range of `Valuation.unitsMap` as a subgroup of the target. -/
def unitsMapRange : Subgroup Γˣ where
  carrier := range v.unitsMap
  mul_mem' hx hy := by
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    use a * b
    simp
  one_mem' := ⟨1, by simp⟩
  inv_mem' hx := by
    obtain ⟨a, -, rfl⟩ := hx
    use a⁻¹
    simp [eq_inv_iff_mul_eq_one, ← Units.mk0_mul]

lemma unitsMap_mem_unitsMapRange (x : Kˣ) : v.unitsMap x ∈ v.unitsMapRange := by
  simp [unitsMapRange, Subgroup.mem_mk, mem_range, exists_apply_eq_apply]

-- The instance below is in **PR #23727**
-- instance [hv : IsDiscrete v] : IsNontrivial v where
--   exists_val_nontrivial := by
--     obtain ⟨γ, hγ, hγ_le, x, hx_v⟩ := hv
--     exact ⟨x, hx_v ▸ ⟨Units.ne_zero γ, ne_of_lt (by norm_cast)⟩⟩

lemma unitsMapRange_ne_bot [hv : IsNontrivial v] : Nontrivial v.unitsMapRange := by
  obtain ⟨x, hx1⟩ := isNontrivial_iff_exists_unit.mp hv
  rw [Subgroup.nontrivial_iff_ne_bot, Subgroup.ne_bot_iff_exists_ne_one]
  use ⟨unitsMap v x, unitsMap_mem_unitsMapRange _ _⟩
  simp only [ne_eq, Subgroup.mk_eq_one, unitsMap]
  rw [← WithZero.coe_inj]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [WithZero.coe_inj, ← ne_eq]
  intro h
  rw [← Units.val_eq_one] at h
  exact hx1 h

variable [IsNontrivial v] [IsCyclic Γˣ]

section IsNontrivial

open Valuation LinearOrderedCommGroup

/-- An element `π : K` is a pre-uniformizer if `v π` generates `v.unitsMapRange` .-/
def IsPreuniformizer (π : K) : Prop :=
  letI := v.unitsMapRange_ne_bot
  v π = v.unitsMapRange.genLTOne

@[simp]
lemma val_Preuniformizer {π : K} (hπ : v.IsPreuniformizer π) : letI := v.unitsMapRange_ne_bot
    v π = v.unitsMapRange.genLTOne := hπ

variable {v}

lemma isPreuniformizer_val_lt_one {π : K} (hπ : v.IsPreuniformizer π) : v π < 1 :=
  let _ := v.unitsMapRange_ne_bot
  hπ ▸ v.unitsMapRange.genLTOne_lt_one


lemma isPreuniformizer_val_ne_zero {π : K} (hπ : v.IsPreuniformizer π) : v π ≠ 0 := by
  by_contra h0
  simp [IsPreuniformizer, h0, zero_ne_coe] at hπ
  exact (Units.ne_zero _).symm hπ

open Subgroup

lemma isPreuniformizer_val_generates_unitsMapRange {π : K} (hπ : v.IsPreuniformizer π) :
    unitsMapRange v = zpowers (Units.mk0 (v π) (v.isPreuniformizer_val_ne_zero hπ)) := by
  let _ := v.unitsMapRange_ne_bot
  rw [← v.unitsMapRange.genLTOne_zpowers_eq_top]
  congr
  simp_all [val_Preuniformizer, Units.mk0_val]

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

theorem isPreuniformizer_iff {π : K} : letI := v.unitsMapRange_ne_bot
    v.IsPreuniformizer π ↔ v π = v.unitsMapRange.genLTOne := refl _

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
  let _ := v.unitsMapRange_ne_bot
  rw [isPreuniformizer_iff] at hπ ; simp [zero_lt_iff, ne_eq, hπ, coe_ne_zero, not_false_iff]

theorem isPreuniformizer_not_isUnit {π : v.integer} (hπ : IsPreuniformizer v π) : ¬ IsUnit π := by
  intro h
  have h1 : v ((algebraMap (↥v.integer) K) π) = 1 :=
    Valuation.Integers.one_of_isUnit (Valuation.integer.integers v)  h
  exact ne_of_gt (isPreuniformizer_val_lt_one hπ) h1.symm

end IsNontrivial

end Field

open LinearOrderedCommGroup


section Ring

variable {R : Type*} [Ring R] (vR : Valuation R Γ)
variable [Nontrivial Γˣ] [IsCyclic Γˣ]

/-- An element `π : R` is a uniformizer if `v π` generates the range of v and is `< 1`. -/
abbrev IsUniformizer (π : R) : Prop :=
  vR π = (⊤ : Subgroup Γˣ).genLTOne

/-- An element `π : R` is a uniformizer if `v π` generates the range of v and is `< 1`. -/
abbrev IsUniformizer' [Nontrivial (thegrp vR)ˣ] [IsCyclic (thegrp vr)ˣ] (π : R) : Prop :=
  vR π = (⊤ : Subgroup ((thegrp vr)ˣ)).genLTOne

variable {vR}

theorem isUniformizer_iff {π : R} : IsUniformizer vR π ↔ vR π = genLTOne Γˣ := refl _

theorem isUniformizer_ne_zero {π : R} (hπ : IsUniformizer vR π) : π ≠ 0 := by
  intro h0
  rw [h0, IsUniformizer, Valuation.map_zero] at hπ
  exact (Units.ne_zero (⊤ : Subgroup Γˣ).genLTOne).symm hπ

theorem isUniformizer_val_pos {π : R} (hπ : IsUniformizer vR π) : 0 < vR π := by
  rw [isUniformizer_iff] at hπ
  simp only [zero_lt_iff, ne_eq, hπ, coe_ne_zero, not_false_iff]
  apply (Units.ne_zero (⊤ : Subgroup Γˣ).genLTOne)

theorem isUniformizer_val_ne_zero {π : R} (hπ : IsUniformizer vR π) : vR π ≠ 0 :=
  ne_of_gt (isUniformizer_val_pos hπ)

variable (vR) in
/-- The structure `Uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer.-/
@[ext]
structure Uniformizer where
  /-- The integer underlying a `Preuniformizer` -/
  val : vR.integer
  valuation_eq_gen : IsUniformizer vR val

/-- A constructor for uniformizers. -/
def Uniformizer.mk' {x : R} (hx : IsUniformizer vR x) : Uniformizer vR where
  val := ⟨x, by
      rw [mem_integer_iff, isUniformizer_iff.mp hx]
      exact_mod_cast le_of_lt (Subgroup.genLTOne_lt_one ⊤)
      ⟩
  valuation_eq_gen := hx

@[simp]
instance : Coe (Uniformizer vR) vR.integer := ⟨fun π ↦ π.val⟩

theorem uniformizer_ne_zero (π : Uniformizer vR) : π.1.1 ≠ 0 :=
  isUniformizer_ne_zero π.2

theorem uniformizer_val_ne_zero (π : Uniformizer vR) : vR π.1 ≠ 0 :=
  isUniformizer_val_ne_zero π.2

theorem uniformizer_val_eq_genLTOne (π : Uniformizer vR) :
    Units.mk0 (vR π.1) (uniformizer_val_ne_zero π) = genLTOne Γˣ := by simp [π.2]

theorem isDiscrete_of_exists_isUniformizer {K : Type*} [Field K] {v : Valuation K Γ}
    {π : K} (hπ : IsUniformizer v π) : IsDiscrete v := by
  apply IsDiscrete.mk
  use Units.mk0 (v π) (isUniformizer_val_ne_zero hπ)
  simp [hπ, genLTOne_eq_of_top, Units.mk0_val]
  refine ⟨?_, by use π⟩
  simpa [Units.mk0_val, Subgroup.genLTOne_zpowers_eq_top, Subgroup.mem_top]
    using Subgroup.genLTOne_lt_one ⊤

end Ring

section CommRing

variable {R : Type*} [CommRing R] (vR : Valuation R Γ)
variable [Nontrivial Γˣ] [IsCyclic Γˣ]

theorem isUniformizer_val_lt_one {π : R} (hπ : IsUniformizer vR π) : vR π < 1 := by
  rw [isUniformizer_iff.mp hπ]
  norm_cast
  apply Subgroup.genLTOne_lt_one

theorem isUniformizer_not_isUnit {π : vR.integer} (hπ : IsUniformizer vR π) : ¬ IsUnit π := by
  intro h
  have h1 : vR ((algebraMap (↥vR.integer) R) π) = 1 :=
    Valuation.Integers.one_of_isUnit (Valuation.integer.integers vR)  h
  exact ne_of_gt (isUniformizer_val_lt_one vR hπ) h1.symm

end CommRing

open scoped NNReal
section Field

open Valuation Ideal Multiplicative WithZero IsLocalRing

variable {K : Type w₁} [Field K] (v : Valuation K Γ)

/- When the valuation is defined over a field instead that simply on a (commutative) ring, we use
the notion of `valuation_subring` instead of the weaker one of `integer`s to access the
corresponding API. -/
local notation "K₀" => v.valuationSubring

section IsNontrivial

theorem exists_isPreuniformizer_of_isNontrivial [v.IsNontrivial] [IsCyclic Γˣ] :
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


end IsNontrivial

section IsDiscrete

variable [IsDiscrete v]

theorem exists_isUniformizer_of_isDiscrete :
    haveI := IsDiscrete.nontrivial_value_group v
    haveI := IsDiscrete.cyclic_value_group v
    ∃ π : K₀, IsUniformizer v (π : K) := by
  let surj_v : IsDiscrete v := by infer_instance
  have := IsDiscrete.nontrivial_value_group v
  have := IsDiscrete.cyclic_value_group v
  rw [isDiscrete_iff_surjective] at surj_v
  obtain ⟨a, ha⟩ := surj_v (genLTOne Γˣ)
  refine ⟨⟨a, ?_⟩, ha⟩
  rw [mem_valuationSubring_iff, ha]
  norm_cast
  exact le_of_lt <| Subgroup.genLTOne_lt_one ..

lemma unitsMapRange_eq_top : v.unitsMapRange = ⊤ := by
  ext x
  refine ⟨fun h ↦ by trivial, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := IsDiscrete.surj v x.1
  have ha₀ : a ≠ 0 := by
    intro h_abs
    rw [h_abs, map_zero] at ha
    exact Units.ne_zero x ha.symm
  use Units.mk0 a ha₀
  rw [← unitsMap_of_ne_zero v ha₀] at ha
  assumption_mod_cast

end IsDiscrete

section IsNontrivial

variable {v} [IsNontrivial v] [Nontrivial Γˣ] [IsCyclic Γˣ]

theorem IsUniformizer.isPreuniformizer {π : K} (hπ : IsUniformizer v π) :
    IsPreuniformizer v π := by
  have := isDiscrete_of_exists_isUniformizer hπ
  rw [isPreuniformizer_iff, isUniformizer_iff.mp hπ, genLTOne_eq_of_top]
  congr
  exact (unitsMapRange_eq_top v).symm

/-- A constructor for preuniformizers. -/
def Uniformizer.toPreuniformizer (π : Uniformizer v) : Preuniformizer v where
  val := π.val
  valuation_gt_one := IsUniformizer.isPreuniformizer π.2

end IsNontrivial

section IsDiscrete

variable {v} [IsDiscrete v]
--**FAE**: In the following, shuold we assume `[Nontrivial Γˣ] [IsCyclic Γˣ]` instead of `IsDiscrete`?
/- In the following theorem, we don't single out the assumption `IsPreuniformizer v π` to be able to
add the two `haveI` assumptions. -/
theorem IsPreuniformizer.isUniformizer {π : K} :
      haveI := IsDiscrete.nontrivial_value_group v
      haveI := IsDiscrete.cyclic_value_group v
    IsPreuniformizer v π → IsUniformizer v π := by
  intro hπ
  haveI := IsDiscrete.nontrivial_value_group v
  haveI := IsDiscrete.cyclic_value_group v
  rw [isUniformizer_iff, isPreuniformizer_iff.mp hπ, genLTOne_eq_of_top]
  congr
  exact unitsMapRange_eq_top v


theorem isUniformizer_iff_isPreuniformizer {π : K} :
      haveI := IsDiscrete.nontrivial_value_group v
      haveI := IsDiscrete.cyclic_value_group v
    IsUniformizer v π ↔ IsPreuniformizer v π :=
  haveI := IsDiscrete.cyclic_value_group v
  haveI := IsDiscrete.nontrivial_value_group v
  ⟨fun hπ ↦ IsUniformizer.isPreuniformizer hπ, fun hπ ↦ IsPreuniformizer.isUniformizer hπ⟩

/-- A constructor for uniformizers. -/
def Preuniformizer.to_uniformizer :
      haveI := IsDiscrete.nontrivial_value_group v
      haveI := IsDiscrete.cyclic_value_group v
    Preuniformizer v → Uniformizer v := by
  intro π
  haveI := IsDiscrete.nontrivial_value_group v
  haveI := IsDiscrete.cyclic_value_group v
  apply Uniformizer.mk
  exact IsPreuniformizer.isUniformizer π.2

end IsDiscrete

section PreUniformizer

variable {v} [IsNontrivial v] [IsCyclic Γˣ]

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



-- Available in current mathlib
-- @[simp] lemma zpow_le_one_iff_right_of_lt_one₀  {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀]
--     [ZeroLEOneClass G₀] [PosMulReflectLT G₀] {a : G₀} [PosMulStrictMono G₀] {n : ℤ} (ha₀ : 0 < a)
--     (ha₁ : a < 1) : a ^ n ≤ 1 ↔ 0 ≤ n := by
--   simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

theorem pow_preuniformizer {r : K₀} (hr : r ≠ 0) (π : Preuniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1 * u.1 := by
  have hr₀ : v r ≠ 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
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
    mul_inv_cancel₀ (pow_ne_zero _ (preuniformizer_ne_zero π)), one_mul]

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

instance [IsNontrivial v] : Nonempty (Preuniformizer v) :=
  ⟨⟨(exists_isPreuniformizer_of_isNontrivial v).choose,
    (exists_isPreuniformizer_of_isNontrivial v).choose_spec⟩⟩

end PreUniformizer

section IsUniformizer

variable [Nontrivial Γˣ] [IsCyclic Γˣ]

theorem isUniformizer_of_associated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁) (H : Associated π₁ π₂) :
    IsUniformizer v π₂ :=
  have : IsDiscrete v := isDiscrete_of_exists_isUniformizer h1
  IsPreuniformizer.isUniformizer
    (isPreuniformizer_of_associated (IsUniformizer.isPreuniformizer h1) H)

end IsUniformizer

section Uniformizer

variable [Nontrivial Γˣ] [IsCyclic Γˣ]

theorem associated_of_uniformizer (π₁ π₂ : Uniformizer v) : Associated π₁.1 π₂.1 :=
  have : IsDiscrete v := isDiscrete_of_exists_isUniformizer π₁.2
  associated_of_isPreuniformizer (Uniformizer.toPreuniformizer π₁)
    (Uniformizer.toPreuniformizer π₂)

theorem pow_uniformizer {r : K₀} (hr : r ≠ 0) (π : Uniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1  * u.1 :=
    have : IsDiscrete v := isDiscrete_of_exists_isUniformizer π.2
  pow_preuniformizer hr (Uniformizer.toPreuniformizer π)

/-- This lemma does not assume the valuation to be discrete, although the fact
  that a uniformizer exists forces the condition. -/
theorem uniformizer_is_generator (π : Uniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} :=
  have : IsDiscrete v := isDiscrete_of_exists_isUniformizer π.2
  preuniformizer_is_generator (Uniformizer.toPreuniformizer π)

end Uniformizer


theorem isUniformizer_is_generator [Nontrivial Γˣ] [IsCyclic Γˣ] {π : v.valuationSubring}
    (hπ : IsUniformizer v π) : maximalIdeal v.valuationSubring = Ideal.span {π} :=
  have : IsDiscrete v := isDiscrete_of_exists_isUniformizer hπ
  isPreuniformizer_is_generator (IsUniformizer.isPreuniformizer hπ)

theorem pow_uniformizer_is_pow_generator [Nontrivial Γˣ] [IsCyclic Γˣ] (π : Uniformizer v)
    (n : ℕ) : maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  have : IsDiscrete v := isDiscrete_of_exists_isUniformizer π.2
  exact pow_preuniformizer_is_pow_generator (Uniformizer.toPreuniformizer π) n

instance [IsDiscrete v] :
      haveI := IsDiscrete.cyclic_value_group v
      haveI := IsDiscrete.nontrivial_value_group v
    Nonempty (Uniformizer v) :=
  haveI := IsDiscrete.cyclic_value_group v
  haveI := IsDiscrete.nontrivial_value_group v
  ⟨⟨(exists_isUniformizer_of_isDiscrete v).choose,
    (exists_isUniformizer_of_isDiscrete v).choose_spec⟩⟩

theorem not_isField [IsNontrivial v] [IsCyclic Γˣ] : ¬ IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_isPreuniformizer_of_isNontrivial v
  rintro ⟨-, -, h⟩
  have := isPreuniformizer_ne_zero hπ
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact isPreuniformizer_not_isUnit hπ h


theorem _root_.Valuation.isPreuniformizer_of_generator [IsNontrivial v] [IsCyclic Γˣ]
    {r : K₀} (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsPreuniformizer v r := by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isPreuniformizer_of_isNontrivial v
  obtain ⟨n, u, hu⟩ := pow_preuniformizer hr₀ ⟨π, hπ⟩
  rw [preuniformizer_is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact isPreuniformizer_of_associated hπ hr

theorem isUniformizer_of_generator [IsDiscrete v] {r : K₀}
    (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
      haveI := IsDiscrete.cyclic_value_group v
      haveI := IsDiscrete.nontrivial_value_group v
    IsUniformizer v r := by
  rw [isUniformizer_iff_isPreuniformizer]
  have := IsDiscrete.cyclic_value_group v
  exact isPreuniformizer_of_generator v hr


/- **TODO** : reinstate if needed -/
theorem val_le_iff_dvd {L : Type*} [Field L] {w : Valuation L Γ} [IsNontrivial w]
    [IsDiscrete w] [IsDiscreteValuationRing w.valuationSubring] (x : w.valuationSubring) (n : ℕ) :
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
    tauto

-- **FAE** The lemma below is now an `exact` away from the previous one...
-- theorem val_le_iff_dvd (L : Type w₁) [Field L] {w : Valuation L Γ} [IsDiscrete w]
--     [IsDiscreteValuationRing w.valuationSubring] (x : w.valuationSubring) (n : ℕ) :
--       haveI := IsDiscrete.cyclic_value_group w
--       haveI := IsDiscrete.nontrivial_value_group w
--     w x ≤ (genLTOne Γˣ) ^ n ↔ IsLocalRing.maximalIdeal w.valuationSubring ^ n ∣ Ideal.span {x} := by
--   haveI := IsDiscrete.cyclic_value_group w
--   haveI := IsDiscrete.nontrivial_value_group w
--   exact val_le_iff_dvd' x n

section RankOne

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


/- **TODO** : reinstate after fixing the above instance (with updated RHS).
    **FAE** It does not look very nice...-/
--theorem rankOne_hom_def : RankOne.hom v = WithZeroMulInt.toNNReal (base_ne_zero K v) := rfl

end RankOne

theorem ideal_isPrincipal [v.IsNontrivial] [IsCyclic Γˣ] (I : Ideal K₀) : I.IsPrincipal := by
  suffices ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
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
      exact ⟨π.1, preuniformizer_is_generator π⟩

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

instance : IsDiscrete (instAdicValued A).v := by
  apply isDiscrete_of_exists_isUniformizer
    (π := valuation_exists_uniformizer (FractionRing A) (maximalIdeal A)|>.choose)
  convert valuation_exists_uniformizer (FractionRing A) (maximalIdeal A)|>.choose_spec
  rw [← genLTOne_eq_of_top, ← Multiplicative.genLTOne_eq_neg_one]
  norm_cast

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

-- end Field

end Valuation

namespace DiscretelyValued

open Valuation --DiscreteValuation

variable (K : Type w₁) [Field K] [hv : Valued K ℤₘ₀]

/-- The definition of being a preuniformizer for an element of a valued field-/
def IsPreuniformizer [hv.v.IsNontrivial] := Valuation.IsPreuniformizer hv.v

/-- The structure `Preuniformizer` for a valued field-/
def Preuniformizer [hv.v.IsNontrivial] := Valuation.Preuniformizer hv.v

instance [hv : Valued K ℤₘ₀] [IsNontrivial hv.v] : Nonempty (Preuniformizer K) :=
  ⟨⟨(exists_isPreuniformizer_of_isNontrivial hv.v).choose,
    (exists_isPreuniformizer_of_isNontrivial hv.v).choose_spec⟩⟩

/-- The definition of being a uniformizer for an element of a valued field-/
def IsUniformizer := Valuation.IsUniformizer hv.v

/-- The structure `Uniformizer` for a valued field-/
def Uniformizer := Valuation.Uniformizer hv.v

instance [hv : Valued K ℤₘ₀] [IsDiscrete hv.v] : Nonempty (Uniformizer K) :=
  ⟨⟨(exists_isUniformizer_of_isDiscrete hv.v).choose,
    (exists_isUniformizer_of_isDiscrete hv.v).choose_spec⟩⟩

end DiscretelyValued
