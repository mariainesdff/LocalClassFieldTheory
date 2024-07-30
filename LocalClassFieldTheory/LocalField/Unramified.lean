/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import LocalClassFieldTheory.DiscreteValuationRing.Ramification
import LocalClassFieldTheory.LocalField.Basic
import Mathlib.Algebra.Algebra.Equiv

open BigOperators DiscreteValuation

open Valued Valuation Extension
namespace LocalField

variable (K : Type*) [Field K] [LocalField K]
  (L : Type*) [Field L] [LocalField L] [Algebra K L] -- use FiniteDimensional K L

local notation "v" => (@Valued.v K _ ℤₘ₀ _ _)
local notation "K₀" => Valuation.valuationSubring v
local notation "w" => (@Valued.v L _ ℤₘ₀ _ _)
local notation "L₀" => Valuation.valuationSubring w

instance : FiniteDimensional K L := by
  sorry

lemma foo : L₀ = (extendedValuation K L).valuationSubring := by
  ext x
  simp only [mem_valuationSubring_iff]
  rw [Extension.apply]
  split_ifs with h
  · simp only [h, _root_.map_zero, zero_le']
  · sorry

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
  (LocalRing.maximalIdeal (Valuation.valuationSubring (@Valued.v K _ ℤₘ₀ _ _)))
  (LocalRing.maximalIdeal (Valuation.valuationSubring (@Valued.v L _ ℤₘ₀ _ _)))

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
  convert ValuationSubring.algebra v L
  sorry
  sorry

/-- The extension `Kn K hn` of `K` is the unique unramified extension of degree `n`. -/
def Kn_unique (L : Type*) [Field L] [LocalField L] [Algebra K L]
  --[FiniteDimensional K L] replaced by `LocalField L`
  (hn' : FiniteDimensional.finrank K L = n)
  (he : e(L, K) = 1) :
    (Kn K hn) ≃ₐ[K] L  :=
  sorry

/-- The Galois group of the extension `Kn K hn` of `K` is isomorphic to "ℤ/n". -/
def Kn_galoisGroup : ((Kn K hn) ≃ₐ[K] (Kn K hn)) ≃* (ZMod n) := sorry

end LocalField
