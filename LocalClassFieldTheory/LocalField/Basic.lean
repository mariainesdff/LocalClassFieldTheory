/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField
import LocalClassFieldTheory.EqCharacteristic.Valuation
import LocalClassFieldTheory.MixedCharacteristic.Valuation
import LocalClassFieldTheory.ForMathlib.HaarMeasure
import Mathlib.MeasureTheory.Group.ModularCharacter

import Mathlib.Analysis.AbsoluteValue.Equivalence

/-!
# Local fields
In this file we define the `class NALocalField` on a valued field `K`, requiring that it is
* complete (with respect to the uniform structure induced by the valuation)
* that its valuation is discrete
* that the residue field of its unit ball is finite

## Main Definitions
* `NALocalField` is the key definition, see above.

## Main Results
* For an `EqCharLocalField p K` that is separable over `FpX_completion p` we show that `K` is a
local field. The separability assumption is required to use some result in mathlib concerning
the finiteness of the ring of integers.
* For a `MixedCharLocalField p K`, we show that `K` is a local field.

## ToDo:
PR the first two scoped instances to `Mathlib.Topology.Algebra.UniformGroup.Defs` in the `CommGroup`
section (turning it into a `namespace`), and changing the `[local instance]` to a `scoped instance`
and upgrading the theorem `uniformGroup_of_commGroup` to a `scoped instance`; and also add the
theorem `AddSubgroup.uniformity_eq`.

-/

noncomputable section

open DiscreteValuation Multiplicative Valuation

open scoped DiscreteValuation

namespace CommGroupUniformity

/-These two scoped instances automatically update the `TopologicalDivisionRing` structure on any
local field to a uniform group structure, making `uniformContinuous_sub` be found by class
inference-/

-- example {G : Type*} [AddGroup G] [u : UniformSpace G] [hG : UniformAddGroup G] :
--     IsTopologicalAddGroup.toUniformSpace G = u := UniformAddGroup.toUniformSpace_eq

-- @[to_additive]
-- scoped instance (priority := high) instUniformSpaceOnCommGroup (E : Type*) [Group E]
--     [TopologicalSpace E] [IsTopologicalGroup E] : UniformSpace E :=
--   IsTopologicalGroup.toUniformSpace E
--
-- @[to_additive]
-- scoped instance instUniformGroup (E : Type*) [CommGroup E] [TopologicalSpace E]
--     [IsTopologicalGroup E] :
--     @UniformGroup E (IsTopologicalGroup.toUniformSpace E) _ :=
--   @uniformGroup_of_commGroup E ..

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-The class `LocalField`....**Blabla** -/
class _root_.LocalField (K : Type*) [Field K] extends UniformSpace K, IsUniformAddGroup K,
  IsTopologicalDivisionRing K, CompleteSpace K, LocallyCompactSpace K

/-This shows that the topology induced from the uniformity on `K` coincides with that of `K` as
a topological group. -/
-- example (K : Type*) [Field K] [hK : LocalField K] :
--   hK.toTopologicalSpace = (instUniformSpaceOnAddCommGroup K).toTopologicalSpace := rfl

-- @[to_additive AddSubgroup.uniformity_eq]
-- lemma Subgroup.uniformity_eq {L : Type*} [CommGroup L] [TopologicalSpace L]
--     [IsTopologicalGroup L] (E : Subgroup L) :
--     instUniformSpaceOnCommGroup E = instUniformSpaceSubtype := by
--   ext : 1
--   rw [uniformity_eq_comap_nhds_one' E, uniformity_subtype, uniformity_eq_comap_nhds_one' L,
--     Filter.comap_comap]
--   have heq : ((fun (p : L × L) ↦ p.2 / p.1) ∘ fun (q : E × E) ↦ ((q.1 : L), (q.2 :L))) =
--     fun (q : E × E) ↦ (q.2 : L) / (q.1 :L) := rfl
--   rw [heq]
--   ext s
--   simp only [Filter.mem_comap]
--   refine ⟨fun ⟨U, hU0, hU⟩ ↦ ?_, fun ⟨U, hU0, hU⟩ ↦ ?_⟩
--   · simp only [mem_nhds_iff, Set.exists_subset_image_iff, Set.mem_image,
--       ZeroMemClass.coe_eq_zero, exists_eq_right] at hU0 ⊢
--     obtain ⟨t, htU, ⟨V, hV, rfl⟩, ht0⟩ := hU0
--     refine ⟨V, ⟨V, le_refl _, hV, ht0⟩, ?_⟩
--     apply subset_trans _ hU
--     intro x hx
--     simp only [Set.mem_preimage] at hx ⊢
--     exact htU (by simp [hx])
--   · refine ⟨(Subtype.val ⁻¹' U), ?_, hU⟩
--     simp only [mem_nhds_iff] at hU0 ⊢
--     obtain ⟨t, htU, ht, ht0⟩ := hU0
--     exact ⟨Subtype.val ⁻¹' t, Set.preimage_mono htU, isOpen_induced ht, by simp [ht0]⟩


end CommGroupUniformity

-- **from here #1...**
/-- The class `NALocalField`, extending `valued K ℤₘ₀` by requiring that `K` is complete, that
the valuation is discrete, and that the residue field of the unit ball is finite. -/
class NALocalField (K : Type*) [Field K] extends Valued K ℤₘ₀ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete' (@Valued.v K _ ℤₘ₀ _ _)
  finiteResidueField : Finite (IsLocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring)

instance (K : Type*) [Field K] [NALocalField K] : IsDiscrete' (@Valued.v K _ ℤₘ₀ _ _) :=
  NALocalField.isDiscrete

instance (K : Type*) [Field K] [NALocalField K] : CompleteSpace K := NALocalField.complete

instance (K : Type*) [Field K] [NALocalField K] :
    Finite (IsLocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring) :=
  NALocalField.finiteResidueField


instance (K : Type*) [Field K] [NALocalField K] :
    Finite (IsLocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring) :=
  NALocalField.finiteResidueField
-- **...to here #1: in PR 23730**

open CommGroupUniformity MeasureTheory.Measure

variable (K : Type*) [Field K]

-- noncomputable def haarFunction [LocalField K] : K → ℝ :=
--   fun x ↦ MeasureTheory.Measure.addModularCharacterFun x

class NonarchLocalField (K : Type*) [Field K] extends LocalField K where
  isNonarchimedean : IsNonarchimedean (addModularCharacterFun · : K → ℝ)

def IsNonarchLocalField (K : Type*) [Field K] [LocalField K] : Prop :=
  IsNonarchimedean (addModularCharacterFun · : K → ℝ)

/- This would be needed if we define the above using `@[class] structure` instead of `class`-/
--instance [NonarchLocalField K] : LocalField K :=  inferInstance

open scoped NNReal

/- open SerreHaar Classical in
def NonarchLocalField.toValued_Gamma [NonarchLocalField K] : Valued K ℤₘ₀ where
  -- uniformContinuous_sub := by
  --   have := @uniformContinuous_sub K _ _
  v := by
    --let c : K → ℝ≥0 := fun x ↦ if hx : x = 0 then 0 else χ (R := K) (Units.mk0 x hx)
    sorry
  is_topological_valuation := sorry -/

def NonarchLocalField.toValued [NonarchLocalField K] : Valued K ℤₘ₀ where
  v := sorry
  is_topological_valuation := sorry

class ArchLocalField (K : Type*) [Field K] extends LocalField K where
  Archimedean : 1 < (addModularCharacterFun (2 : K))
  -- Archimedean : ¬ IsNonarchimedean (LocalField.haarFunction K)

def IsArchLocalField (K : Type*) [Field K] [LocalField K] : Prop :=
  1 < (addModularCharacterFun (2 : K))
  -- Archimedean : ¬ IsNonarchimedean (LocalField.haarFunction K)

/-A proof that `Nonarch →  LocCompact ↔ Complete ∧ Discrete ∧ FiniteResidueField` see
Bourbaki, Alg Comm, VI, Chap ,§ 5, no 1, Prop 1.-/
def NonarchLocalField.toNALocalField [NonarchLocalField K] :
    NALocalField K where
  __ := NonarchLocalField.toValued K
  complete := inferInstance
  isDiscrete := sorry
  finiteResidueField := sorry

theorem LocalField.isArch_or_isNonarch [LocalField K] :
    IsArchLocalField K ∨ IsNonarchLocalField K := sorry

section Subfield

variable (K L : Type*) [Field K] [NALocalField K] [Field L] [NALocalField L] [Algebra K L]
  [Algebra.IsSeparable K L] (E : IntermediateField K L)

--instance : UniformSpace E := by exact instUniformSpaceSubtype

--instance : TopologicalSpace E := by exact instTopologicalSpaceSubtype

--inferInstance --by exact instUniformSpaceSubtype

/- instance instTopologicalDivisionRingSubtype : TopologicalDivisionRing E where
  continuous_add := sorry --by continuity -- slow
  continuous_mul := sorry --by continuity -- slow
  continuous_neg := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuousAt_inv₀ := by
    intro x hx
    have hxL : ContinuousAt Inv.inv (x : L) := continuousAt_inv₀ (by simp [hx])
    simp only [continuousAt_def] at hxL
    intros U hU
    have hU' : Subtype.val '' U ∈ nhds (x : L)⁻¹ := sorry
    --simp only [Filter.map_inv]
    specialize hxL (Subtype.val '' U) hU'
   -- simp? at hU'

    --apply continuousAt_subtype_val
    sorry


--omit [LocalField K] in
lemma IntermediateField.uniformity_eq (E : IntermediateField K L) :
    instUniformSpaceOnAddCommGroup E = instUniformSpaceSubtype := by
  let E' : AddSubgroup L := {
    carrier := E
    add_mem' := IntermediateField.add_mem E
    zero_mem' := IntermediateField.zero_mem E
    neg_mem' := IntermediateField.neg_mem E }
  exact AddSubgroup.uniformity_eq E' -/

/- structure IntermediateLocalField extends IntermediateField K L where
  unif_eq {E} : instUniformSpace E = instUniformSpaceSubtype (α := L) -/

/- If we use the `complete` field instead of `toCompleteSpace`, we get the following error:
  synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instUniformSpaceSubtype
inferred
  instUniformSpace ↥E.

  We suspect that this is because of the order in which the typeclass inference
  system is working in each case.

  We fixed this by giving high priority to `instUniformSpace`.
   -/

open Valued

/- IMPLEMENTATION REMARK: for the time being, we are assuming the hypothesis
`FiniteDimensional K L`. This should actually follow from the hypotheses above, but it probably
requires to prove the classification theorem for nonarchimedean local fields, which will not be
trivial.

TODO: provide this instance.
instance finiteDimensional : FiniteDimensional K L := by
  sorry -/

--variable [FiniteDimensional K L]

lemma Valued.isOpen_iff  {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    [_i : Valued R Γ₀] {s : Set R} :
    IsOpen s ↔ ∀ x ∈ s, ∃ (γ : Γ₀ˣ), {y : R | v (y - x) < ↑γ} ⊆ s := by
  simp [isOpen_iff_mem_nhds, mem_nhds]

def Valued.absoluteValue {A Γ₀ : Type*} [Field A] [LinearOrderedCommGroupWithZero Γ₀]
    [val : Valued A Γ₀] [hv : val.v.RankOne] : AbsoluteValue A ℝ where
  toFun    := Valued.norm
  map_mul' := sorry
  nonneg'  := sorry
  eq_zero' := sorry
  add_le'  := sorry

instance {R Γ₀ : Type*} [Field R] [LinearOrderedCommGroupWithZero Γ₀] (v₁ : Valuation R Γ₀)
    [h₁ : v₁.RankOne]  : (Valued.mk' v₁).v.RankOne := sorry

/- lemma Valuation.isEquiv_iff {R Γ₀ Γ₁ : Type*} [Field R] [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁] (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ₁)
    [h₁ : v₁.RankOne] [h₂ : v₂.RankOne] :
    v₁.IsEquiv v₂ ↔ AbsoluteValue.IsEquiv
      (Valued.mk' v₁).absoluteValue (Valued.mk' v₂).absoluteValue :=  by
  sorry -/

lemma todo [h : IsValExtension (Valued.v (R := K)) (Valued.v (R := L))] {π : K}
    (hπ : IsUniformizer (Valued.v (R := K)) π) :
    ∃ (n : ℕ) (hn : 0 < n), v (algebraMap K L π) = ofAdd (-(n : ℤ)) := by
  obtain ⟨ω, hω⟩ := exists_isUniformizer_of_isDiscrete' (Valued.v (R := L))
  set x : valuationSubring (Valued.v (R := L)) := by
      use algebraMap K L π
      rw [mem_valuationSubring_iff, IsValExtension.val_map_le_one_iff (Valued.v (R := K)), hπ]
      norm_cast
      sorry
      --exact right_eq_inf.mp rfl -- ???
    with hx_def -- not sure about spacing
  have hx : x ≠ 0 := sorry
  obtain ⟨n, u, hu⟩ := pow_uniformizer (Valued.v (R := L)) hx ⟨ω, hω⟩
  simp only [hx_def, SubmonoidClass.coe_pow] at hu
  have hu1 : v ((u : (Valued.v (R := L)).valuationSubring) : L) = 1 := by
    sorry
  have hn0 : 0 < n := sorry
  use n, hn0
  rw [hu, _root_.map_mul, _root_.map_pow, hω, WithZero.ofAdd_neg_nat, hu1, mul_one]
  sorry

instance [h : IsValExtension (Valued.v (R := K)) (Valued.v (R := L))] : ContinuousSMul K L := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isDiscrete' (Valued.v (R := K))
  obtain ⟨n, hn0, hn⟩ := todo K L hπ
  refine continuousSMul_of_algebraMap K L ?_
  rw [continuous_def]
  intros U hU
  simp only [isOpen_iff, Set.mem_preimage] at hU ⊢
  intros x hx
  obtain ⟨γ, hγ⟩ := hU (algebraMap K L x) hx
  by_cases hγ1 : (γ : ℤₘ₀) < 1
  · obtain ⟨z, hz⟩ : ∃ (z : Kˣ), (Valued.v (algebraMap K L (z : K))) = γ^n := by
      have hγ0 : (γ : ℤₘ₀) ≠ 0 := sorry
      have hunit : IsUnit ((π : K)^(- toAdd (WithZero.unzero hγ0))) := sorry
      have hcoe : (hunit.unit : K) = (π : K)^(- toAdd (WithZero.unzero hγ0)) := rfl
      use hunit.unit
      rw [hcoe]
      simp only [zpow_neg, map_inv₀, map_zpow₀, hn, ofAdd_neg, WithZero.coe_inv, inv_zpow', inv_inv]
      rw [WithZero.ofAdd_zpow, zpow_comm, ← WithZero.ofAdd_zpow,
        ofAdd_toAdd, WithZero.coe_unzero, zpow_natCast]
    have hz' : {y | v (y - (algebraMap K L) x) < (Valued.v (algebraMap K L (z : K)))} ⊆ U := by
      apply le_trans _ hγ
      rw [hz]
      intros y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      apply lt_of_lt_of_le hy
      conv_rhs => rw [← pow_one (γ : ℤₘ₀)]
      exact pow_le_pow_right_of_le_one' (le_of_lt hγ1) hn0
    use (z.isUnit.map v).unit
    intro y hy
    simp only [IsUnit.unit_spec, Set.mem_setOf_eq, Set.mem_preimage] at hy ⊢
    apply hz'
    rw [Set.mem_setOf_eq, ← _root_.map_sub, IsValExtension.val_map_lt_iff (Valued.v (R := K))]
    exact hy
  · use 1
    intros y hy
    have h1 : {y | v (y - (algebraMap K L) x) < 1} ⊆ U :=
      le_trans (fun _ hy ↦ lt_of_lt_of_le hy (not_lt.mp hγ1)) hγ
    apply h1
    simp only [Units.val_one, Set.mem_setOf_eq] at hy ⊢
    rw [← _root_.map_sub, IsValExtension.val_map_lt_one_iff (Valued.v (R := K))]
    exact hy

variable [IsValExtension (Valued.v (R := K)) (Valued.v (R := L))] [FiniteDimensional K L]

instance foo : Valued E ℤₘ₀ := by
  apply Valued.mk (extendedValuation K E)
  intros U
  sorry


/- Wrong

 def Valuation.isEquiv_iff {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ₀) :
    v₁.IsEquiv v₂ ↔ ∃ (γ : Γ₀ˣ), ∀ (r : R) (δ : Γ₀ˣ), v₁ r ≤ δ ↔ v₂ r ≤ δ * γ := by
  simp only [IsEquiv]
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · sorry
  · intros r s
    by_cases hs : s = 0
    · sorry
    · have hunit : IsUnit (v₁ s) := sorry
      specialize hγ r hunit.unit
      sorry -/

instance : NALocalField E := {
  complete := FiniteDimensional.complete K E
  isDiscrete := Extension.isDiscrete_of_finite K E
  finiteResidueField := finiteResidueFieldOfUnitBall K E NALocalField.finiteResidueField }

instance : LocalField E where
  toIsTopologicalDivisionRing := sorry
  complete := sorry
  local_compact_nhds := sorry

instance : NonarchLocalField E where
  isNonarchimedean := sorry


end Subfield


namespace EqCharLocalField

open FpXCompletion

variable (p : outParam ℕ) [Fact (Nat.Prime p)]

variable (K : Type _) [Field K] [EqCharLocalField p K]

/-- An `EqCharLocalField p K` that is separable over `FpX_completion` is a local field.
  The separability assumption is required to use some result in mathlib concerning
  the finiteness of the ring of integers.-/
noncomputable def localField [Fact (Algebra.IsSeparable (FpXCompletion p) K)] : NALocalField K :=
  { EqCharLocalField.WithZero.valued p K with
    complete := EqCharLocalField.completeSpace p K
    isDiscrete := EqCharLocalField.valuation.isDiscrete p K
    finiteResidueField := by
      have : Algebra.IsSeparable (FpXCompletion p) K := @Fact.out _ _
      apply finiteResidueFieldOfUnitBall
      apply FpXIntCompletion.residueFieldFiniteOfCompletion }

end EqCharLocalField

namespace MixedCharLocalField

open Padic

variable (p : outParam ℕ) [Fact (Nat.Prime p)]

variable (K : Type*) [Field K] [MixedCharLocalField p K]

instance : Algebra.IsSeparable (Padic'.Q_p p) K :=
  Algebra.IsSeparable.of_integral (Padic'.Q_p p) K

-- /-- A `MixedCharLocalField` is a local field. -/
noncomputable def localField : NALocalField K :=
  { MixedCharLocalField.WithZero.valued p K with
    complete := MixedCharLocalField.completeSpace p K
    isDiscrete := MixedCharLocalField.valuation.isDiscrete p K
    finiteResidueField := by
      apply finiteResidueFieldOfUnitBall
      apply RingOfIntegers.residueFieldFiniteOfCompletion }

end MixedCharLocalField

-- section Metrizable
--
-- variable {K}
-- variable [UniformSpace K]
-- -- variable [TopologicalSpace K] [TopologicalDivisionRing K]
-- variable [(uniformity K).IsCountablyGenerated] [T0Space K]
--
-- noncomputable
-- def distK : K → K → ℝ := (UniformSpace.metricSpace K).dist
--
-- abbrev IsPowerBdd (x : K) : Prop := ∀ n : ℕ, distK x (x ^ n) ≤ 1
--
-- variable (K) in
-- def PowerBddSubring (H : IsNonarchimedean (fun x ↦ distK x 0)) : ValuationSubring K where
--   carrier := {x | IsPowerBdd x}
--   mul_mem' := by
--     intro a b ha hb
--     simp at ha hb ⊢
--     intro n
--     replace ha := ha n
--     replace hb := hb n
--
--   one_mem' := sorry
--   add_mem' := sorry
--   zero_mem' := sorry
--   neg_mem' := sorry
--   mem_or_inv_mem' := sorry
--
-- theorem powerBddSubring_eq_integers [hv : NALocalField K] :
--   PowerBddSubring K = hv.toValued.v.valuationSubring := sorry
--
-- end Metrizable
