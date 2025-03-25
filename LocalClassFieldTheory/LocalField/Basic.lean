/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField
import LocalClassFieldTheory.EqCharacteristic.Valuation
import LocalClassFieldTheory.MixedCharacteristic.Valuation
-- import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Local fields
In this file we define the `class local_field` on a valued field `K`, requiring that it is
* complete (with respect to the uniform structure induced by the valuation)
* that its valuation is discrete
* that the residue field of its unit ball is finite

## Main Definitions
* `local_field` is the key definition, see above.


## Main Results
* For an `eq_char_local_field p K` that is separable over `FpX_completion p` we show that `K` is a
local
field. The separability assumption is required to use some result in mathlib concerning
the finiteness of the ring of integers.
* For a `mixed_char_local_field p K`, we show that `K` is a local field.
-/


open DiscreteValuation Multiplicative Valuation


open scoped DiscreteValuation

namespace LocalField
/-These two local instances automatically update the `TopologicalDivisionRing` structure on any
local field to a uniform group structure, making `uniformContinuous_sub` be found by class
inference-/
-- attribute [local instance] /- IsTopologicalAddGroup.toUniformSpace -/ uniformAddGroup_of_addCommGroup

scoped instance (E : Type*) [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] :
  UniformSpace E := IsTopologicalAddGroup.toUniformSpace E

scoped instance (E : Type*) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] :
  UniformAddGroup E := @uniformAddGroup_of_addCommGroup E ..

class _root_.LocalField (K : Type*) [Field K] extends TopologicalSpace K, TopologicalDivisionRing K,
  CompleteSpace K, LocallyCompactSpace K

variable (K : Type*) [Field K] [LocalField K]


noncomputable
def LocalField.haarFunction : K → ℝ := fun x ↦ MeasureTheory.Measure.addModularCharacterFun x

@[class]
structure NonarchLocalField (K : Type*) [Field K] extends LocalField K where
  isNonarchimedean : IsNonarchimedean (LocalField.haarFunction K)

-- #synth IsTopologicalRing K

-- local instance (L : Type*) /- [Field L]  -/[LocalField L] : UniformAddGroup L := by
--   convert @uniformAddGroup_of_addCommGroup L _ _ _
--   ext
--   rw [uniformity_eq_comap_nhds_zero']


#synth UniformAddGroup K

def NonarchLocalField.toValued [NonarchLocalField K] : Valued K ℤₘ₀ where
  --uniformContinuous_sub := uniformContinuous_sub
  v := sorry
  is_topological_valuation := sorry

@[class]
structure ArchLocalField (K : Type*) [Field K] extends LocalField K where
  Archimedean : ¬ IsNonarchimedean (LocalField.haarFunction K)


/-- The class `local_field`, extending `valued K ℤₘ₀` by requiring that `K` is complete, that the
valuation is discrete, and that the residue field of the unit ball is finite. -/
structure ValuedLocalField (K : Type*) [Field K] extends Valued K ℤₘ₀ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete (@Valued.v K _ ℤₘ₀ _ _)
  finiteResidueField : Finite (IsLocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring)

/-A proof that `Nonarch →  LocCompact ↔ Complete ∧ Discrete ∧ FiniteResidueField` see
Bourbaki, Alg Comm, VI, Chap ,§ 5, no 1, Prop 1.-/
def NonarchLocalField.toValuedLocalField [NonarchLocalField K] : ValuedLocalField K where
  __ := NonarchLocalField.toValued K
  complete := sorry
  isDiscrete := sorry
  finiteResidueField := sorry

-- attribute [instance] LocalField.complete LocalField.isDiscrete LocalField.finiteResidueField
-- NOTE: instances added on 15/4/24
-- instance (K : Type*) [Field K] [LocalField K] : Valuation.IsDiscrete (@Valued.v K _ ℤₘ₀ _ _) :=
--   LocalField.isDiscrete

-- instance (K : Type*) [Field K] [LocalField K] : CompleteSpace K := LocalField.complete

-- instance (K : Type*) [Field K] [LocalField K] :
--     Finite (LocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring) :=
--   LocalField.finiteResidueField

/-instance of_intermediateField [NumberField K] [NumberField L] [Algebra K L]
    (E : IntermediateField K L) : NumberField E :=
  of_module_finite K E-/
variable (K : Type*) [Field K] [Valued K ℤₘ₀] (E : Subfield K)

-- example : True := by
  -- have : AddSubgroup K := E.toAddSubgroup
  -- have : UniformAddGroup E := E.toAddSubgroup.uniformAddGroup

#synth TopologicalSpace E

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

-- instance : LocalField E where
--   complete := sorry
--   isDiscrete := sorry
--   finiteResidueField := sorry















namespace EqCharLocalField

open FpXCompletion

variable (p : outParam ℕ) [Fact (Nat.Prime p)]

variable (K : Type _) [Field K] [EqCharLocalField p K]

/-- An `eq_char_local_field p K` that is separable over `FpX_completion` is a local field.
  The separability assumption is required to use some result in mathlib concerning
  the finiteness of the ring of integers.-/
noncomputable def localField [Fact (Algebra.IsSeparable (FpXCompletion p) K)] : ValuedLocalField K :=
  { EqCharLocalField.WithZero.valued p K with
    complete := EqCharLocalField.completeSpace p K
    isDiscrete := valuation.IsDiscrete p K
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

-- /-- A `mixed_char_local_field` is a local field. -/
noncomputable def localField : ValuedLocalField K :=
  { MixedCharLocalField.WithZero.valued p K with
    complete := MixedCharLocalField.completeSpace p K
    isDiscrete := valuation.IsDiscrete p K
    finiteResidueField := by
      apply finiteResidueFieldOfUnitBall
      apply RingOfIntegers.residueFieldFiniteOfCompletion }

end MixedCharLocalField
