/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField
import LocalClassFieldTheory.EqCharacteristic.Valuation
import LocalClassFieldTheory.MixedCharacteristic.Valuation

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

/-- The class `local_field`, extending `valued K ℤₘ₀` by requiring that `K` is complete, that the
valuation is discrete, and that the residue field of the unit ball is finite. -/
class LocalField (K : Type*) [Field K] extends Valued K ℤₘ₀ where
  complete : CompleteSpace K
  isDiscrete : IsDiscrete (@Valued.v K _ ℤₘ₀ _ _)
  finiteResidueField : Finite (IsLocalRing.ResidueField (@Valued.v K _ ℤₘ₀ _ _).valuationSubring)

attribute [instance] LocalField.complete LocalField.isDiscrete LocalField.finiteResidueField
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

instance : Valued E ℤₘ₀ where
  __ := E.toAddSubgroup.uniformAddGroup
  v := Valuation.comap (algebraMap E K) Valued.v
  is_topological_valuation := by
    intro S
    constructor
    · intro hS
      obtain ⟨U, hU_nhds, hU_map⟩ := (mem_nhds_induced (algebraMap E K) 0 S).mp hS
      simp at hU_nhds
      obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation U).mp hU_nhds
      use γ
      simp only [comap_apply]
      intro x hx
      simp at hx
      have : (algebraMap (↥E) K) x ∈ U := hγ hx
      apply hU_map
      simpa
    · rintro ⟨γ, hγ⟩
      simp only [comap_apply] at hγ
      rw [mem_nhds_induced]
      simp only [ZeroMemClass.coe_zero]
      use {x | Valued.v x < γ}
      constructor
      · apply (Valued.is_topological_valuation _).mpr
        use γ
      · simp
        aesop















namespace EqCharLocalField

open FpXCompletion

variable (p : outParam ℕ) [Fact (Nat.Prime p)]

variable (K : Type _) [Field K] [EqCharLocalField p K]

/-- An `eq_char_local_field p K` that is separable over `FpX_completion` is a local field.
  The separability assumption is required to use some result in mathlib concerning
  the finiteness of the ring of integers.-/
noncomputable def localField [Fact (Algebra.IsSeparable (FpXCompletion p) K)] : LocalField K :=
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

/-- A `mixed_char_local_field` is a local field. -/
noncomputable def localField : LocalField K :=
  { MixedCharLocalField.WithZero.valued p K with
    complete := MixedCharLocalField.completeSpace p K
    isDiscrete := valuation.IsDiscrete p K
    finiteResidueField := by
      apply finiteResidueFieldOfUnitBall
      apply RingOfIntegers.residueFieldFiniteOfCompletion }

end MixedCharLocalField
