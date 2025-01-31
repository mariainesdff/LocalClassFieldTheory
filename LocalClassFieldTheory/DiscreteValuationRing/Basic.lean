/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.ForMathlib.WithZero
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
import Mathlib.RingTheory.Valuation.RankOne

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Discrete Valuation Rings

In this file we prove basic results about Discrete Valuation Rings, building on the main definitions
provided in `RingTheory.DiscreteValuationRing.Basic`. We focus in particular on discrete
valuations and on `Valued` structures on the field of fractions of a DVR, as well as on a DVR
structure on the unit ball of a `Valued` field whose valuation is discrete.

## Main Definitions
* `IsDiscrete`: We define a valuation to be discrete if it is ℤₘ₀-valued and
  `Multiplicative.ofAdd (- 1 : ℤ)` belongs to the image.
  --TODO
* `IsUniformizer`: Given a ℤₘ₀-valued valuation `v` on a ring `R`, an element `π : R` is a
  uniformizer if `v π = multiplicative.of_add (- 1 : ℤ) : ℤₘ₀`.
* `Uniformizer`: A strucure bundling an element of a ring and a proof that it is a uniformizer.
* `base`: Given a valued field `K`, if the residue field of its unit ball (that is a local field)
  is finite, then `valuation_base` is the cardinal of the residue field, and otherwise it takes the
  value `6` which  is not a prime power.
* The `instance dvr_of_is_discrete` is the formalization of Chapter I, Section 1, Proposition 1 in
  Serre's **Local Fields** showing that the unit ball of a discretely-valued field is a DVR.


## Main Results
* `associated_of_Uniformizer` An element associated to a uniformizer is itself a uniformizer
* `Uniformizer_of_associated` If two elements are uniformizers, they are associated.
* `IsUniformizer_is_generator` A generator of the maximal ideal is a uniformizer if the valuation
  is discrete.
* `isDiscreteOfExistsUniformizer` If there exists a uniformizer, the valuation is discrete.
* `exists_Uniformizer_ofDiscrete` Conversely, if the valuation is discrete there exists a
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

open Multiplicative

section Subgroup

theorem AddSubgroup.toSubgroup_closure {A : Type} [AddGroup A] (S : Set A) :
    AddSubgroup.toSubgroup (AddSubgroup.closure S) =
      Subgroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubgroup.toSubgroup.to_galoisConnection.l_le <|
      (AddSubgroup.closure_le _).2 <| Subgroup.subset_closure (G := Multiplicative A))
    ((Subgroup.closure_le _).2 <| AddSubgroup.subset_closure (G := A))

theorem Subgroup.toAddSubgroup_closure {G : Type} [Group G] (S : Set G) :
    Subgroup.toAddSubgroup (Subgroup.closure S) =
      AddSubgroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Subgroup.toAddSubgroup.le_symm_apply.1 <|
      (Subgroup.closure_le _).2 (AddSubgroup.subset_closure (G := Additive G)))
    ((AddSubgroup.closure_le _).2 (Subgroup.subset_closure (G := G)))

theorem Subgroup.toAddSubgroup_toSubgroup' {G : Type*} [Group G] (H : Subgroup G) :
    AddSubgroup.toSubgroup' (Subgroup.toAddSubgroup H) = H := by
  ext x
  simp only [OrderIso.symm_apply_apply]

--TODO: use this in DVR.Extensions.
/- lemma MultInt.subgroup_cyclic (H : Subgroup (Multiplicative ℤ)) :
    IsCyclic H :=  Subgroup.isCyclic H -/

--NOTE: this lemma exists in current Mathlib
@[to_additive]
theorem isCyclic_iff_exists_zpowers_eq_top (α : Type*) [Group α] :
    IsCyclic α ↔ ∃ g : α, Subgroup.zpowers g = ⊤ := by
  sorry


-- But this one is missing
@[to_additive]
theorem Subgroup.isCyclic_iff_exists_zpowers_eq_top {α : Type*} [Group α] (H : Subgroup α) :
    IsCyclic H ↔ ∃ g : α, Subgroup.zpowers g = H := by
    rw [_root_.isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨fun ⟨⟨k, k_mem⟩, hk⟩ ↦ ⟨k, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨⟨k, zpowers_le.mp <| le_of_eq hk⟩, ?_⟩⟩
    · simp [← range_subtype H, ← Subgroup.map_eq_range_iff.mpr, hk,
        ← (coeSubtype H ▸ (H.subtype).map_zpowers ⟨k, k_mem⟩)]
    · apply_fun Subgroup.map H.subtype using Subgroup.map_injective <| subtype_injective H
      simp [(H.subtype).map_zpowers ⟨k, _⟩, coeSubtype, hk, Subgroup.map_eq_range_iff.mpr,
        range_subtype]



  -- rw [_root_.isCyclic_iff_exists_zpowers_eq_top H]
  -- simp only [Subgroup.eq_top_iff']
  -- refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  -- · use g
  --   ext x
  --   simp only [Subgroup.mem_zpowers_iff] at hg ⊢
  --   refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  --   · obtain ⟨k, rfl⟩ := hx
  --     rw [← Subgroup.coe_zpow]
  --     exact SetLike.coe_mem (g ^ k)
  --   · obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
  --     use k
  --     rw [← Subgroup.coe_zpow, hk]
  -- · have hgH : g ∈ H := by rw [← hg]; exact mem_zpowers g
  --   use ⟨g, hgH⟩
  --   intro x
  --   have hx : ↑x ∈ zpowers g := by rw [hg]; exact x.2
  --   simp only [Subgroup.mem_zpowers_iff] at hx ⊢
  --   obtain ⟨k, hk⟩ := hx
  --   use k
  --   ext
  --   simp only [SubgroupClass.coe_zpow, hk]

lemma MultInt.exists_generator_le_one {H : Subgroup (Multiplicative ℤ)} (h : H ≠ ⊥) :
    ∃ (a : Multiplicative ℤ), a < 1 ∧ Subgroup.zpowers a = H := by
  have h_cyc := Subgroup.isCyclic H
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp h_cyc
  by_cases ha1 : a < 1
  · use a, ha1, ha
  · simp only [not_lt, le_iff_eq_or_lt] at ha1
    rcases ha1 with (ha1 | ha1)
    · rw [← ha1, Subgroup.zpowers_one_eq_bot] at ha
      exact absurd ha h.symm
    · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
      rw [Subgroup.zpowers_inv, ha]

/- lemma MultInt.subgroup_cyclic (H : Subgroup (Multiplicative ℤ)) :
    ∃ (a : Multiplicative ℤ), H = Subgroup.closure {a} := by
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic H.toAddSubgroup
  have hg' : H =  AddSubgroup.toSubgroup (AddSubgroup.closure {g}) := by
    erw [← hg, Subgroup.toAddSubgroup_toSubgroup' (G := Multiplicative ℤ)]
  use ofAdd g
  rw [hg', AddSubgroup.toSubgroup_closure]
  congr -/

/- lemma MultInt.exists_generator_le_one {H : Subgroup (Multiplicative ℤ)} (h : H ≠ ⊥) :
    ∃ (a : Multiplicative ℤ), a < 1 ∧ H = Subgroup.closure {a} := by
  obtain ⟨a, ha⟩ := MultInt.subgroup_cyclic H
  by_cases ha1 : a < 1
  · use a, ha1, ha
  · simp only [not_lt, le_iff_eq_or_lt] at ha1
    rcases ha1 with (ha1 | ha1)
    · rw [← ha1, Subgroup.closure_singleton_one] at ha
      exact absurd ha h
    · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
      rw [Subgroup.closure_singleton_inv, ha] -/

end Subgroup

namespace Valuation

variable {A : Type w₁} [CommRing A]
namespace Integer

theorem isUnit_iff_valuation_eq_one {K : Type w₁} [Field K] {Γ₀ : Type w₂}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (x : v.integer) :
    IsUnit x ↔ v x = 1 := by
  refine ⟨@Integers.one_of_isUnit K Γ₀ _ _ v v.integer _ _ (Valuation.integer.integers v) _,
    fun hx ↦ ?_⟩
  have hx0 : (x : K) ≠ 0 := by
    by_contra h0
    rw [h0, map_zero] at hx
    exact zero_ne_one hx
  have hx' : v (x : K)⁻¹ = (1 : Γ₀) := by rw [map_inv₀, inv_eq_one]; exact hx
  rw [isUnit_iff_exists_inv]
  use! (x : K)⁻¹, le_of_eq hx'
  · ext; simp only [Subring.coe_mul, ne_eq, ZeroMemClass.coe_eq_zero, OneMemClass.coe_one,
      mul_inv_cancel₀ hx0]

theorem not_isUnit_iff_valuation_lt_one {K : Type w₁} [Field K] {Γ₀ : Type w₂}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (x : v.integer) :
    ¬IsUnit x ↔ v x < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one, le_antisymm_iff]
  exact and_iff_right x.2

end Integer

open Function Set

/-- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `WithZero.multiplicative (- 1) : ℤₘ₀`-/
class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
  one_mem_range : (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) ∈ range v

lemma IsDiscrete.surj {K : Type*} [Field K] (v : Valuation K ℤₘ₀) [hv : IsDiscrete v] :
    Surjective v := by
  intro c
  refine WithOne.cases_on c ⟨0, map_zero _⟩ ?_
  obtain ⟨π, hπ⟩ := hv
  intro a
  use π ^ (- a.toAdd)
  rw [map_zpow₀, hπ]
  simp only [ofAdd_neg, WithZero.coe_inv, zpow_neg, inv_zpow', inv_inv, ← WithZero.ofAdd_zpow]
  rfl

lemma isDiscrete_iff_surjective {K : Type*} [Field K] (v : Valuation K ℤₘ₀) :
    IsDiscrete v ↔ Surjective v :=
  ⟨fun _ ↦ IsDiscrete.surj v, fun hv ↦ ⟨hv (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)⟩⟩

open Polynomial

-- Example of nontrivial ℤₘ₀-valued valuation with no good notion of uniformizer.
open Classical in
noncomputable example {K : Type*} [Field K] :
    Valuation (K[X]⧸ (Ideal.span {(X^2 : K[X])})) ℤₘ₀ where
  toFun := fun p ↦ if (Ideal.Quotient.mk (Ideal.span {(X^2 : K[X])}) X ∣ p) then 0 else 1
  map_zero' := by
    simp only [dvd_zero, ↓reduceIte]
  map_one' := by
    simp only [ite_eq_right_iff, zero_ne_one, imp_false]
    sorry
  map_mul' := by
    intro p q
    simp only [mul_ite, mul_zero, mul_one]
    split_ifs
    · rfl
    · rfl
    · sorry --contradiction bc X is prime
    · sorry --by contradiction
    · sorry --by contradiction
    · rfl
  map_add_le_max' := by
    intro p q
    simp only [le_sup_iff]
    split_ifs -- 8 trivial cases
    all_goals sorry

open Valuation Ideal Multiplicative WithZero

variable {R : Type w₁} [CommRing R] (vR : Valuation R ℤₘ₀)

def unzero' (h0 : ∀ {x : R}, x ≠ 0 → vR x ≠ 0) : {x : R // x ≠ 0} → Multiplicative ℤ :=
    fun x ↦ WithZero.unzero (h0 x.2)

def unzero_range' [Nontrivial R] [IsDomain R] (h0 : ∀ {x : R}, x ≠ 0 → vR x ≠ 0) :
    Submonoid (Multiplicative ℤ) where
  carrier := range (vR.unzero' h0)
  mul_mem' hx hy := by
    simp only [mem_range, Subtype.exists] at *
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    use a*b, mul_ne_zero ha hb
    simp only [unzero', _root_.map_mul, unzero_mul]
  one_mem' := by
    use ⟨(1 : R), one_ne_zero⟩
    simp only [unzero', _root_.map_one, unzero_coe]
    rfl

section Field

variable {K : Type*} [Field K] (v : Valuation K ℤₘ₀)

def unzero : Kˣ →* Multiplicative ℤ where
  toFun := fun x ↦ WithZero.unzero (ne_zero_of_unit v x)
  map_one' := by simp only [Units.val_one, _root_.map_one, unzero_coe]; rfl
  map_mul' := fun x y ↦ by simp only [Units.val_mul, _root_.map_mul, WithZero.unzero_mul]

def unzero_range : Subgroup (Multiplicative ℤ) where
  carrier := range v.unzero
  mul_mem' hx hy := by
    simp only [mem_range] at *
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    use a*b
    simp only [unzero, Units.val_mul, _root_.map_mul, unzero_mul]
  one_mem' := by
    use 1
    simp only [unzero, Units.val_one, _root_.map_one, unzero_coe]
  inv_mem' hx := by
    simp only [mem_range] at *
    obtain ⟨a, ha, rfl⟩ := hx
    use a⁻¹
    simp only [unzero, Units.val_inv_eq_inv_val, map_inv₀]
    rw [eq_inv_iff_mul_eq_one]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Units.val_inv_eq_inv_val, map_inv₀]
    simp only [isUnit_iff_ne_zero, ne_eq, _root_.map_eq_zero, Units.ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, one_ne_zero, ← unzero_mul, unzero_coe]
    rfl

lemma unzero_mem_unzero_range (x : Kˣ) : v.unzero x ∈ v.unzero_range := by
  simp only [unzero_range, Subgroup.mem_mk, mem_range, exists_apply_eq_apply]

/-- A valuation on a field is nontrivial if there exists a unit with valuation not equal to `1`. -/
class Nontrivial : Prop where
  exists_val_ne_one : ∃ x : Kˣ, v x ≠ 1

instance [hv : IsDiscrete v] : Nontrivial v where
  exists_val_ne_one := by
    obtain ⟨x, hx⟩ := hv
    have hx0 : x ≠ 0 := by rw [← v.ne_zero_iff, hx]; exact coe_ne_zero
    use Units.mk0 x hx0
    rw [Units.val_mk0, hx]
    exact ne_of_beq_false rfl

lemma unzero_range_ne_bot [hv : Nontrivial v] : v.unzero_range ≠ ⊥ := by
  obtain ⟨x, hx1⟩ := hv
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  use ⟨unzero v x, unzero_mem_unzero_range _ _⟩
  simp only [ne_eq, Subgroup.mk_eq_one, unzero]
  rw [← WithZero.coe_inj]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, coe_unzero]
  exact hx1

/-- An element `π : K` is a pre-uniformizer if `v π` generates `v.unzero_range` .-/
def IsPreuniformizer [Nontrivial v] (π : K) : Prop :=
  v π = (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose

lemma IsPreuniformizer_val_lt_one [Nontrivial v] {π : K}
    (hπ : v.IsPreuniformizer π) : v π < 1 := by
  rw [hπ, ← WithZero.coe_one, WithZero.coe_lt_coe]
  exact (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose_spec.1

lemma IsPreuniformizer_val_ne_zero [Nontrivial v] {π : K} (hπ : v.IsPreuniformizer π) :
    v π ≠ 0 := by
  by_contra h0
  simp only [IsPreuniformizer, h0, zero_ne_coe] at hπ

lemma IsPreuniformizer_val_generates_unzero_range [Nontrivial v] {π : K}
    (hπ : v.IsPreuniformizer π) :
    unzero_range v = Subgroup.zpowers (WithZero.unzero (v.IsPreuniformizer_val_ne_zero hπ)) := by
  convert (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose_spec.2.symm
  rw [← WithZero.coe_inj, ← hπ, coe_unzero]

/-- The structure `Preuniformizer` bundles together the term in the ring and a proof that it is a
  preuniformizer.-/
@[ext]
structure Preuniformizer [Nontrivial v] where
  val : v.integer
  valuationEqNegOne : v.IsPreuniformizer val

theorem IsPreuniformizer_iff [Nontrivial v] {π : K} :
    v.IsPreuniformizer π ↔
      v π = (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose := refl _

/-- A constructor for preuniformizers.-/
def Preuniformizer.mk' [Nontrivial v] {x : K} (hx : v.IsPreuniformizer x) :
    v.Preuniformizer where
  val := ⟨x, le_of_lt (v.IsPreuniformizer_val_lt_one hx)⟩
  valuationEqNegOne := hx

@[simp]
instance [Nontrivial v] : Coe v.Preuniformizer v.integer := ⟨fun π ↦ π.val⟩

end Field

/-- An element `π : R` is a uniformizer if `v π = Multiplicative.ofAdd (- 1 : ℤ) : ℤₘ₀`.-/
def IsUniformizer (π : R) : Prop :=
  vR π = (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)

variable {vR}

theorem IsUniformizer_iff {π : R} :
    IsUniformizer vR π ↔ vR π = (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) :=
  refl _

variable (vR)

/-- The structure `Uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer.-/
@[ext]
structure Uniformizer where
  val : vR.integer
  valuationEqNegOne : IsUniformizer vR val

/-- A constructor for uniformizers. -/
def Uniformizer.mk' (x : R) (hx : IsUniformizer vR x) : Uniformizer vR where
  val := ⟨x, by
      rw [mem_integer_iff, IsUniformizer_iff.mp hx]; exact le_of_lt WithZero.ofAdd_neg_one_lt_one⟩
  valuationEqNegOne := hx

@[simp]
instance : Coe (Uniformizer vR) vR.integer := ⟨fun π ↦ π.val⟩

theorem isDiscreteOfExistsUniformizer {K : Type w₁} [Field K] (v : Valuation K ℤₘ₀) {π : K}
    (hπ : IsUniformizer v π) : IsDiscrete v := by
  rw [isDiscrete_iff_surjective]
  intro x
  apply @WithZero.cases_on (x := x)
  · exact ⟨0, Valuation.map_zero v⟩
  · rw [IsUniformizer] at hπ
    intro m
    use π ^ (-Multiplicative.toAdd m)
    rw [map_zpow₀, hπ, ← coe_zpow, coe_inj, ← ofAdd_zsmul, ← zsmul_neg', neg_neg, zsmul_one,
      Int.cast_id, ofAdd_toAdd]

theorem Uniformizer_ne_zero {π : R} (hπ : IsUniformizer vR π) : π ≠ 0 := by
  intro h0
  rw [h0, IsUniformizer, Valuation.map_zero] at hπ
  exact WithZero.zero_ne_coe hπ

theorem Uniformizer_ne_zero' (π : Uniformizer vR) : π.1.1 ≠ 0 :=
  Uniformizer_ne_zero vR π.2

theorem Uniformizer_valuation_pos {π : R} (hπ : IsUniformizer vR π) : 0 < vR π := by
  rw [IsUniformizer_iff] at hπ ; simp only [zero_lt_iff, ne_eq, hπ, coe_ne_zero, not_false_iff]

theorem Uniformizer_not_isUnit {π : vR.integer} (hπ : IsUniformizer vR π) : ¬IsUnit π := by
  intro h
  have h1 :=
    @Valuation.Integers.one_of_isUnit R ℤₘ₀ _ _ vR vR.integer _ _ (Valuation.integer.integers vR) π
      h
  erw [IsUniformizer, h1] at hπ
  exact ne_of_gt ofAdd_neg_one_lt_one hπ

theorem Uniformizer_valuation_lt_one {π : R} (hπ : IsUniformizer vR π) : vR π < 1 := by
  rw [IsUniformizer_iff.mp hπ]; exact ofAdd_neg_one_lt_one

open scoped NNReal

section Field

variable (K : Type w₁) [Field K] (v : Valuation K ℤₘ₀)
/-- If the residue field is finite, then `valuation_base` is the cardinal of the residue field, and
otherwise it takes the value `6` which is not a prime power.-/
noncomputable def base : ℝ≥0 :=
  if 1 < Nat.card (IsLocalRing.ResidueField v.valuationSubring) then
    Nat.card (IsLocalRing.ResidueField v.valuationSubring)
  else 6

theorem one_lt_base : 1 < base K v := by
  rw [base]
  split_ifs with hlt
  · rw [Nat.one_lt_cast]; exact hlt
  · norm_num

theorem base_ne_zero : base K v ≠ 0 :=
  ne_zero_of_lt (one_lt_base K v)

end Field

end Valuation

namespace DiscreteValuation

section Field

open Valuation Ideal Multiplicative WithZero IsLocalRing

variable {K : Type w₁} [Field K] (v : Valuation K ℤₘ₀)

/- When the valuation is defined on a field instead that simply on a (commutative) ring, we use the
notion of `valuation_subring` instead of the weaker one of `integer`s to access the corresponding
API. -/
local notation "K₀" => v.valuationSubring

section IsDiscrete

variable [IsDiscrete v]

theorem exists_Uniformizer_ofDiscrete : ∃ π : K₀, IsUniformizer v (π : K) := by
  let surj_v : IsDiscrete v := by infer_instance
  rw [isDiscrete_iff_surjective] at surj_v
  refine
    ⟨⟨(surj_v (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)).choose, ?_⟩,
      (surj_v (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)).choose_spec⟩
  rw [mem_valuationSubring_iff, (surj_v (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀)).choose_spec]
  exact le_of_lt ofAdd_neg_one_lt_one

lemma unzero_range_eq_top [hv : IsDiscrete v] : v.unzero_range = ⊤ := by
  obtain ⟨x, hx⟩ := hv
  rw [v.unzero_range.eq_top_iff']
  intro n
  have hx0 : x ≠ 0 := by rw [← v.ne_zero_iff, hx]; exact coe_ne_zero
  have hn : n = v.unzero ((Units.mk0 x hx0)^(- n.toAdd)) := by
    have h : v.unzero (Units.mk0 x hx0) = ofAdd (-1) := sorry
    rw [map_zpow, h]
    simp only [Int.reduceNeg, ofAdd_neg, zpow_neg, inv_zpow', inv_inv]
    rw [← Int.ofAdd_mul, one_mul, ofAdd_toAdd]
  rw [hn]
  exact v.unzero_mem_unzero_range ((Units.mk0 x hx0)^(-n.toAdd))

theorem IsUniformizer_iff_isPreuniformizer {π : K} :
    IsUniformizer v π ↔ IsPreuniformizer v π := by
  simp only [IsUniformizer_iff, IsPreuniformizer_iff]
  suffices h_eq : (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) =
    (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose by rw [h_eq]
  set g := (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose with hg
  obtain ⟨h1, htop⟩ := (MultInt.exists_generator_le_one v.unzero_range_ne_bot).choose_spec
  simp only [← hg] at h1 htop ⊢
  rw [unzero_range_eq_top] at htop

  sorry

end IsDiscrete

theorem UniformizerOfAssociated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁) (H : Associated π₁ π₂) :
    IsUniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  rwa [IsUniformizer_iff, ← hu, Subring.coe_mul, Valuation.map_mul,
    (Integer.isUnit_iff_valuation_eq_one u.1).mp u.isUnit, mul_one, ← IsUniformizer_iff]

theorem associatedOfUniformizer {π₁ π₂ : Uniformizer v} : Associated π₁.1 π₂.1 := by
  have hval : v ((π₁.1 : K)⁻¹ * π₂.1) = 1 := by
    simp only [Valuation.map_mul, map_inv₀, IsUniformizer_iff.mp π₁.2,
    IsUniformizer_iff.mp π₂.2, ofAdd_neg, coe_inv, inv_inv, mul_inv_cancel₀, ne_eq, coe_ne_zero,
    not_false_iff]
  let p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩
  use ((Integer.isUnit_iff_valuation_eq_one p).mpr hval).unit
  simp only [IsUnit.unit_spec]
  apply_fun ((↑·) : K₀ → K) using Subtype.val_injective
  simp only [Subring.coe_mul, ← mul_assoc, mul_inv_cancel₀ (Uniformizer_ne_zero v π₁.2), one_mul]

theorem pow_Uniformizer {r : K₀} (hr : r ≠ 0) (π : Uniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1  * u.1 := by
  have hr₀ : v r ≠ 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set m := -(Multiplicative.toAdd (unzero hr₀)) with hm
  have hm₀ : 0 ≤ m := by
    rw [hm, Right.nonneg_neg_iff, ← toAdd_one, toAdd_le, ← coe_le_coe, coe_unzero]
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [Valuation.map_mul, map_zpow₀, IsUniformizer_iff.mp π.2, ofAdd_neg, coe_inv, inv_zpow',
      neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd, coe_inv,
      coe_unzero, inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) ≠ 0 := by
    simp only [ha, neg_neg, ne_eq]
    by_cases h0 : toAdd (unzero hr₀) = 0
    · simp_all only [ne_eq, neg_zero, Nat.cast_eq_zero, CharP.cast_eq_zero, le_refl, zpow_zero,
      one_mul, Subtype.coe_eta, ZeroMemClass.coe_eq_zero, not_false_eq_true]
    · apply mul_ne_zero
      · rw [ne_eq, zpow_eq_zero_iff]
        · exact Uniformizer_ne_zero' v π
        · rwa [hm, neg_neg]
      · rw [ne_eq, Subring.coe_eq_zero_iff]; exact hr
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec, Subring.coe_pow, ha, ← mul_assoc, zpow_neg, hn, zpow_natCast,
    mul_inv_cancel₀, one_mul]
  · apply pow_ne_zero
    exact Uniformizer_ne_zero' _ π


/-- This proof of the lemma does not need the valuation to be discrete, although the fact that a
uniformizer exists forces the condition.-/
theorem Uniformizer_is_generator (π : Uniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} := by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply Uniformizer_not_isUnit v π.2 h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp only [hx₀, Ideal.zero_mem]
    · obtain ⟨n, ⟨u, hu⟩⟩ := pow_Uniformizer v hx₀ π
      rw [← Subring.coe_mul, Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h ↦
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n ≠ 0 := fun h ↦ by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp only [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit,
        dvd_pow_self _ hn]


theorem IsUniformizer_is_generator {π : v.valuationSubring} (hπ : IsUniformizer v π) :
    maximalIdeal v.valuationSubring = Ideal.span {π} :=
  Uniformizer_is_generator _ ⟨π, hπ⟩

theorem pow_Uniformizer_is_pow_generator {π : Uniformizer v} (n : ℕ) :
    maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow, Uniformizer_is_generator]

variable [IsDiscrete v]




instance : Nonempty (Uniformizer v) :=
  ⟨⟨(exists_Uniformizer_ofDiscrete v).choose, (exists_Uniformizer_ofDiscrete v).choose_spec⟩⟩

theorem not_isField : ¬IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_Uniformizer_ofDiscrete v
  rintro ⟨-, -, h⟩
  have := Uniformizer_ne_zero v hπ
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact Uniformizer_not_isUnit v hπ h

theorem IsUniformizerOfGenerator {r : K₀} (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsUniformizer v r := by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_Uniformizer_ofDiscrete v
  obtain ⟨n, u, hu⟩ := pow_Uniformizer v hr₀ ⟨π, hπ⟩
  rw [Uniformizer_is_generator v ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact UniformizerOfAssociated v hπ hr


-- /-The following instance cannot be automatically found, see
-- [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/adding.20imports.20breaks.20class.20inference.3F]-/

-- instance instDVRtoIsNoetherian (A : Type w₁) [CommRing A] [IsDomain A] [DiscreteValuationRing A] :
--   IsNoetherianRing A := IsDedekindRing.toIsNoetherian

theorem val_le_iff_dvd (L : Type w₁) [Field L] {w : Valuation L ℤₘ₀} [IsDiscrete w]
    [IsDiscreteValuationRing w.valuationSubring] (x : w.valuationSubring) (n : ℕ) :
    w x ≤ ofAdd (-(n : ℤ)) ↔ IsLocalRing.maximalIdeal w.valuationSubring ^ n ∣ Ideal.span {x} := by
  by_cases hx : x = 0
  · rw [Ideal.span_singleton_eq_bot.mpr hx, hx, Subring.coe_zero, Valuation.map_zero]
    simp only [WithZero.zero_le, true_iff, ← Ideal.zero_eq_bot, dvd_zero]
  · set r := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal w.valuationSubring) with hr
    have hrn : w (r ^ n) = ofAdd (-(n : ℤ)) := by
      replace hr : IsUniformizer w r := DiscreteValuation.IsUniformizerOfGenerator w ?_
      rw [WithZero.ofAdd_zpow, zpow_neg, ← Nat.cast_one, ← WithZero.ofAdd_neg_one_pow_comm ↑n 1,
          pow_one, zpow_neg, inv_inv, zpow_natCast, Valuation.map_pow]
      congr
      rw [span_singleton_generator]
    have :=
      @Valuation.Integers.le_iff_dvd L ℤₘ₀ _ _ w w.valuationSubring _ _
        (Valuation.integer.integers w) x (r ^ n)
    erw [← hrn, this]
    have DD : IsDedekindDomain w.valuationSubring := by
      apply IsPrincipalIdealRing.isDedekindDomain
    rw [← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal w.valuationSubring), ← hr,
      Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton', dvd_iff_exists_eq_mul_left]
    tauto

section RankOne

open Valuation

noncomputable instance rankOne : RankOne v where
  hom := WithZeroMulInt.toNNReal (base_ne_zero K v)
  strictMono' := WithZeroMulInt.toNNReal_strictMono (one_lt_base K v)
  nontrivial' := by
    obtain ⟨π, hπ⟩ := exists_Uniformizer_ofDiscrete v
    exact
      ⟨π, ne_of_gt (Uniformizer_valuation_pos v hπ), ne_of_lt (Uniformizer_valuation_lt_one v hπ)⟩

theorem rankOne_hom_def : RankOne.hom v = WithZeroMulInt.toNNReal (base_ne_zero K v) := rfl

end RankOne

theorem ideal_isPrincipal (I : Ideal K₀) : I.IsPrincipal :=
  by
  suffices ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := pow_Uniformizer v hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu, Ideal.mul_unit_mem_iff_mem P u.isUnit,
        IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn), ← Ideal.span_singleton_le_iff_mem, ←
        Uniformizer_is_generator v π] at hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, Uniformizer_is_generator v π⟩

theorem integer_isPrincipalIdealRing : IsPrincipalIdealRing K₀ :=
  ⟨fun I ↦ ideal_isPrincipal v I⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
instance dvr_of_isDiscrete : IsDiscreteValuationRing K₀
    where
  toIsPrincipalIdealRing := integer_isPrincipalIdealRing v
  toIsLocalRing  := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact not_isField v

variable (A : Type w₁) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Subring IsDiscreteValuationRing

/-- The maximal ideal of a DVR-/
def maximalIdeal : HeightOneSpectrum A
    where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by
    simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using IsDiscreteValuationRing.not_isField A

variable {A}

noncomputable instance : Valued (FractionRing A) ℤₘ₀ := (maximalIdeal A).adicValued

instance : IsDiscrete (A := FractionRing A) Valued.v :=
  isDiscreteOfExistsUniformizer Valued.v
    (valuation_exists_uniformizer (FractionRing A) (maximalIdeal A)).choose_spec

theorem exists_of_le_one {x : FractionRing A} (H : Valued.v x ≤ (1 : ℤₘ₀)) :
    ∃ a : A, algebraMap A (FractionRing A) a = x :=
  by
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
      rw [← intValuation_apply] at π_lt_one
      have : (maximalIdeal A).intValuation π ≠ 0 := intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← sub_nonneg]
      rw [← coe_unzero this, ← WithZero.coe_one] at H π_lt_one
      rw [div_eq_mul_inv, ← WithZero.coe_pow, ← WithZero.coe_pow, ← WithZero.coe_inv,
        ← zpow_natCast, ← zpow_natCast, ← WithZero.coe_mul, WithZero.coe_le_coe, ← zpow_sub,
        ← ofAdd_zero, ← ofAdd_toAdd (unzero _ ^ ((n : ℤ) - (m))), ofAdd_le, Int.toAdd_zpow] at H
      apply nonneg_of_mul_nonpos_right H
      rwa [← toAdd_one, toAdd_lt, ← WithZero.coe_lt_coe]
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

theorem alg_map_eq_integers :
    Subring.map (algebraMap A (FractionRing A)) ⊤ = Valued.v.valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR and the unit ball in
  its field of fractions endowed with the adic valuation of the maximal ideal.-/
noncomputable def dvrEquivUnitBall :
    A ≃+* (@Valued.v (FractionRing A) _ ℤₘ₀ _ _).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A (FractionRing A))
    (IsFractionRing.injective A _))).trans (RingEquiv.subringCongr alg_map_eq_integers)

end Field

end DiscreteValuation

namespace DiscretelyValued

open Valuation DiscreteValuation

variable (K : Type w₁) [Field K] [hv : Valued K ℤₘ₀]

/-- The definition of being a uniformizer for an element of a valued field-/
def IsUniformizer := Valuation.IsUniformizer hv.v

/-- The structure `uniformizer` for a valued field-/
def Uniformizer := Valuation.Uniformizer hv.v

instance [hv : Valued K ℤₘ₀] [IsDiscrete hv.v] : Nonempty (Uniformizer K) :=
  ⟨⟨(exists_Uniformizer_ofDiscrete hv.v).choose, (exists_Uniformizer_ofDiscrete hv.v).choose_spec⟩⟩

end DiscretelyValued
