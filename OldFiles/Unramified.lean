/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import LocalClassFieldTheory.DiscreteValuationRing.Ramification
import LocalClassFieldTheory.LocalField.Basic
import Mathlib.Algebra.Algebra.Equiv

open BigOperators DiscreteValuation Extension Multiplicative Valued Valuation

noncomputable section
namespace LocalField

variable (K : Type*) [hK : Field K] [hv : LocalField K]
  (L : Type*) [hL : Field L] [halg : Algebra K L] [hfin : FiniteDimensional K L]  /- [LocalField L] -/

local notation "vK" => (@Valued.v K _ ℤₘ₀ _ _)
local notation "K₀" => Valuation.valuationSubring v


instance : Valued K ℤₘ₀ := inferInstance
instance : CompleteSpace K := inferInstance

#check FiniteDimensional.complete

def valued_L : Valued L ℤₘ₀ := DiscreteValuation.Extension.valued K L

set_option quotPrecheck false
local notation "w" => (valued_L K L).v
local notation "L₀" => Valuation.valuationSubring w

def uniformSpace_L : UniformSpace L := by
  apply @Valued.toUniformSpace L _ ℤₘ₀ _ (valued_L K L)

/-
cannot find synthesization order for instance localField_L with type
  (K : Type u_1) →
    [hK : Field K] →
      [hv : LocalField K] →
        (L : Type u_2) → [hL : Field L] → [halg : Algebra K L] → [hfin : FiniteDimensional K L] → LocalField L
all remaining arguments have metavariables:
  Field ?K
  @LocalField ?K ?hK
  @Algebra ?K L Semifield.toCommSemiring DivisionSemiring.toSemiring
  @FiniteDimensional ?K L NormedDivisionRing.toDivisionRing Ring.toAddCommGroup Algebra.toModule-/
def localField_L : LocalField L :=
  letI : Valued L ℤₘ₀ := valued_L K L
  { complete := DiscreteValuation.Extension.completeSpace K L
    isDiscrete := DiscreteValuation.Extension.isDiscrete_of_finite K L
    finiteResidueField := sorry }

lemma foo : (valued_L K L).v.valuationSubring = (extendedValuation K L).valuationSubring := rfl

-- Why is the proof below taken from `DVR.Extensions` broken?
-- MI: It is because the `L₀` in `DVR.Extensions` is defined as
-- `(extendedValuation K L).valuationSubring`
instance : Algebra K₀ L₀ := by
  rw [foo K L]
  haveI h : Algebra v.valuationSubring (extendedValuation K L).valuationSubring.toSubring := by
    rw [← integralClosure_eq_integer]
    exact (integralClosure (↥Valued.v.valuationSubring) L).algebra
  exact h

scoped notation "e("L","K")" => Ideal.ramificationIdx
  (algebraMap (Valuation.valuationSubring (@Valued.v K _ ℤₘ₀ _ _))
    (Valuation.valuationSubring (@Valued.v L _ ℤₘ₀ _ _)))
  (IsLocalRing.maximalIdeal (Valuation.valuationSubring (@Valued.v K _ ℤₘ₀ _ _)))
  (IsLocalRing.maximalIdeal (Valuation.valuationSubring (@Valued.v L _ ℤₘ₀ _ _)))

end LocalField

namespace LocalField

open scoped LocalField

open Valued

variable (K : Type*) [Field K] [LocalField K] {n : ℕ} (hn : 0 < n)

local notation "v" => (@Valued.v K _ ℤₘ₀ _ _)

local notation "K₀" => Valuation.valuationSubring v

/-- The unique unramified extension of `K` of degree `n`. -/
def Kn (K : Type*) [Field K] [LocalField K] {n : ℕ} (hn : 0 < n) : Type* := sorry

-- Q: does this allow to speak about maximal unramified subextensions easily?

instance Kn_field : Field (Kn K hn) := sorry

instance Kn_valued : Valued (Kn K hn) ℤₘ₀ := sorry

instance Kn_localField : LocalField (Kn K hn) := sorry

instance Kn_algebra : Algebra K (Kn K hn) := sorry

instance Kn_algebra' : Algebra K₀ (Kn_valued K hn).v.valuationSubring := sorry

lemma Kn_unramified : e(Kn K hn, K) = 1 := sorry

local instance (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] :
    Algebra K₀ (extendedValuation K L).valuationSubring := by
  --convert ValuationSubring.algebra v L
  --sorry
  sorry

/-- The extension `Kn K hn` of `K` is the unique unramified extension of degree `n`. -/
def Kn_unique (L : Type*) [Field L] [LocalField L] [Algebra K L]
  --[FiniteDimensional K L] replaced by `LocalField L`
  (hn' : Module.finrank K L = n)
  (he : e(L, K) = 1) :
    (Kn K hn) ≃ₐ[K] L  :=
  sorry

/-- The Galois group of the extension `Kn K hn` of `K` is isomorphic to "ℤ/n". -/
def Kn_galoisGroup : ((Kn K hn) ≃ₐ[K] (Kn K hn)) ≃* (ZMod n) := sorry

end LocalField

section Etale

/- By `Algebra.FormallyUnramified.of_map_maximalIdeal` or
  `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`, our condition is equivalent to `𝒪 L/𝓞 K`
  being formally etale. Since it is finite and everything is noetherian,
  `Algebra.FinitePresentation.of_finiteType` guarantees that it is of finite presentation and thus
  it is `Algebra.Etale`. All the previous ones are moreover iff.

-/

end Etale
