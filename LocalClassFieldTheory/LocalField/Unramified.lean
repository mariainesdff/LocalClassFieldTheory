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

/- Note: I was trying to set up a ramification index notation for local fields, but I get errors. -/
namespace LocalField

variable (K : Type*) [Field K] [LocalField K]
  (L : Type*) [Field L] [LocalField L] [Algebra K L]

local notation "v" => (@Valued.v K _ ℤₘ₀ _ _)

local notation "K₀" => Valuation.valuationSubring v

local notation "w" => (@Valued.v L _ ℤₘ₀ _ _)

local notation "L₀" => Valuation.valuationSubring w

instance : Algebra K₀ L₀ := by sorry -- Why the proof below taken from `DVR.Extensions` broken?
  -- convert @ValuationSubring.algebra K _ v L _ _
  -- by
--     haveI h : Algebra hv.v.valuationSubring (extendedValuation K L).valuationSubring.toSubring := by
  -- rw [← integralClosure_eq_integer] at this
--       exact (integralClosure (↥Valued.v.valuationSubring) L).algebra
--   h--- cannot be found

local notation "ee(" L "," K ")" => (⟨(1 : L), (1 : K)⟩ : L × K)

#check ee(L, K) -- this shows that the syntax of the notation is OK

example : Ideal.ramificationIdx (algebraMap K₀ L₀)
  (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal L₀) = Ideal.ramificationIdx (algebraMap K₀ L₀)
  (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal L₀) := by rfl
  -- this shows that the ramificationIdx seems OK with the above instance

-- notation "e(" L "," K ")" => Ideal.ramificationIdx (algebraMap K₀ L₀)
--   (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal L₀)

-- #check

end LocalField

namespace LocalField

open scoped DiscreteValuationRing

open Valued

variable (K : Type*) [Field K] [LocalField K] {n : ℕ} (hn : 0 < n)

/- local instance hv : Valued K ℤₘ₀ := inferInstance

set_option quotPrecheck false
local notation "K₀" => (hv K).v.valuationSubring -/

local notation "v" => (@Valued.v K _ ℤₘ₀ _ _)

local notation "K₀" => Valuation.valuationSubring v

/-- The unique unramified extension of `K` of degree `n`. -/
def Kn (K : Type*) [Field K] [LocalField K] {n : ℕ} (hn : 0 < n) : Type* := sorry

instance Kn_field : Field (Kn K hn) := sorry

instance Kn_valued : Valued (Kn K hn) ℤₘ₀ := sorry

instance Kn_localField : LocalField (Kn K hn) := sorry

instance Kn_algebra : Algebra K (Kn K hn) := sorry

instance Kn_algebra' : Algebra K₀ (Kn_valued K hn).v.valuationSubring := sorry

lemma Kn_unramified : e((Kn_valued K hn).v.valuationSubring, K₀) = 1 := sorry

local instance (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] :
    Algebra K₀ (extendedValuation K L).valuationSubring := by
  convert ValuationSubring.algebra v L
  sorry
  sorry

/-- The extension `Kn K hn` of `K` is the unique unramified extension of degree `n`. -/
def Kn_unique (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  (hn' : FiniteDimensional.finrank K L = n)
  (he : e((extendedValuation K L).valuationSubring, K₀) = 1)  :
    (Kn K hn) ≃ₐ[K] L  :=
  sorry

/-- The Galois group of the extension `Kn K hn` of `K` is isomorphic to "ℤ/n". -/
def Kn_galoisGroup : ((Kn K hn) ≃ₐ[K] (Kn K hn)) ≃* (ZMod n) := sorry

end LocalField
