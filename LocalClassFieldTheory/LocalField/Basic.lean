/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField
import LocalClassFieldTheory.EqCharacteristic.Valuation
import LocalClassFieldTheory.MixedCharacteristic.Valuation
import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Local fields
In this file we define the `class ValuedLocalField` on a valued field `K`, requiring that it is
* complete (with respect to the uniform structure induced by the valuation)
* that its valuation is discrete
* that the residue field of its unit ball is finite

## Main Definitions
* `ValuedLocalField` is the key definition, see above.


## Main Results
* For an `EqCharLocalField p K` that is separable over `FpX_completion p` we show that `K` is a
local field. The separability assumption is required to use some result in mathlib concerning
the finiteness of the ring of integers.
* For a `MixedCharLocalField p K`, we show that `K` is a local field.
-/

open DiscreteValuation Multiplicative Valuation


open scoped DiscreteValuation


namespace AddCommGroupUniformity

/-These two scoped instances automatically update the `TopologicalDivisionRing` structure on any
local field to a uniform group structure, making `uniformContinuous_sub` be found by class
inference-/

example {G : Type*} [AddGroup G] [u : UniformSpace G] [hG : UniformAddGroup G] :
    IsTopologicalAddGroup.toUniformSpace G = u := UniformAddGroup.toUniformSpace_eq

def instUniformSpace (E : Type*) [AddGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] :
  UniformSpace E := IsTopologicalAddGroup.toUniformSpace E

scoped instance instUniformAddGroup (E : Type*) [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] :
  @UniformAddGroup E (instUniformSpace E) _ := @uniformAddGroup_of_addCommGroup E ..

scoped instance (E : Type*) [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] : UniformSpace E := IsTopologicalAddGroup.toUniformSpace E

class _root_.LocalField (K : Type*) [Field K] extends TopologicalSpace K, TopologicalDivisionRing K,
    CompleteSpace K, LocallyCompactSpace K where
  toUniformSpace : UniformSpace K := inferInstance --:= instUniformSpace K
  toUniformAddGroup : UniformAddGroup K := inferInstance
 -- toUniformSpace_eq : toUniformSpace = instUniformSpace K
  --toUniformGroup : @UniformAddGroup K (instUniformSpace K) _
  --toUniformGroup_eq : toUniformGroup = instUniformGroup K

end AddCommGroupUniformity

section ValuedLocalField

/-- The class `local_field`, extending `valued K ℤₘ₀` by requiring that `K` is complete, that the
valuation is discrete, and that the residue field of the unit ball is finite. -/
class ValuedLocalField (K : Type*) [Field K] extends Valued K ℤₘ₀ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete (@Valued.v K _ ℤₘ₀ _ _)
  finiteResidueField : Finite (IsLocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring)

end ValuedLocalField

namespace LocalField

open AddCommGroupUniformity

variable (K : Type*) [Field K]

noncomputable def haarFunction [LocalField K] : K → ℝ :=
  fun x ↦ MeasureTheory.Measure.addModularCharacterFun x

class NonarchLocalField (K : Type*) [Field K] extends LocalField K where
  isNonarchimedean : IsNonarchimedean (haarFunction K)

/- This would be needed if we define the above using `@[class] structure` instead of `class`-/
--instance [NonarchLocalField K] : LocalField K :=  inferInstance

def NonarchLocalField.toValued [NonarchLocalField K] : Valued K ℤₘ₀ where
  --uniformContinuous_sub := uniformContinuous_sub
  v := sorry
  is_topological_valuation := sorry

class ArchLocalField (K : Type*) [Field K] extends LocalField K where
  Archimedean : ¬ IsNonarchimedean (LocalField.haarFunction K)

/-A proof that `Nonarch →  LocCompact ↔ Complete ∧ Discrete ∧ FiniteResidueField` see
Bourbaki, Alg Comm, VI, Chap ,§ 5, no 1, Prop 1.-/
def NonarchLocalField.toValuedLocalField [NonarchLocalField K] :
    ValuedLocalField K where
  __ := NonarchLocalField.toValued K
  complete := inferInstance
  isDiscrete := sorry
  finiteResidueField := sorry

namespace EqCharLocalField

open FpXCompletion

variable (p : outParam ℕ) [Fact (Nat.Prime p)]

variable (K : Type _) [Field K] [EqCharLocalField p K]

/-- An `EqCharLocalField p K` that is separable over `FpX_completion` is a local field.
  The separability assumption is required to use some result in mathlib concerning
  the finiteness of the ring of integers.-/
noncomputable def localField [Fact (Algebra.IsSeparable (FpXCompletion p) K)] : ValuedLocalField K :=
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
noncomputable def localField : ValuedLocalField K :=
  { MixedCharLocalField.WithZero.valued p K with
    complete := MixedCharLocalField.completeSpace p K
    isDiscrete := MixedCharLocalField.valuation.isDiscrete p K
    finiteResidueField := by
      apply finiteResidueFieldOfUnitBall
      apply RingOfIntegers.residueFieldFiniteOfCompletion }

end MixedCharLocalField

section Subfield

variable (K L : Type*) [Field K] [LocalField K] [Field L] [LocalField L] [Algebra K L]
  (E : IntermediateField K L)

instance : UniformSpace E := inferInstance --by exact instUniformSpaceSubtype

instance : TopologicalDivisionRing E where
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

instance : LocalField E where
  --__ := instUniformSpace E
  toTopologicalDivisionRing := inferInstance
  complete := sorry
  local_compact_nhds := sorry

variable (K : Type*) [Field K] [Valued K ℤₘ₀] (E : Subfield K)

instance foo : Valued E ℤₘ₀ where
  __ := E.toAddSubgroup.uniformAddGroup
  v := Valuation.comap (algebraMap E K) Valued.v
  is_topological_valuation := by
    refine fun S ↦ ⟨fun hS ↦ ?_, ?_⟩
    · obtain ⟨_, hU_nhds, hU_map⟩ := (mem_nhds_induced (algebraMap E K) _ _).mp hS
      obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation _).mp hU_nhds
      refine ⟨γ, fun _ hx ↦ hU_map (by simp [Set.mem_preimage, hγ hx])⟩
    · rw [mem_nhds_induced]
      exact fun ⟨γ, _⟩ ↦ ⟨_, (Valued.is_topological_valuation _).mpr ⟨γ, (by rfl)⟩,
        by simpa only [Set.preimage_setOf_eq]⟩

end Subfield
