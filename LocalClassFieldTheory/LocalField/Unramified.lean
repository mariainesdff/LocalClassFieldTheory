/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Ramification
import LocalClassFieldTheory.LocalField.Basic
import Mathlib.Algebra.Algebra.Equiv

open BigOperators DiscreteValuation

open Valued

/- Note: I was trying to set up a ramification index notation for local fields, but I get errors. -/
namespace LocalField

variable (K : Type*) [Field K] [LocalField K]
  (L : Type*) [Field L] [LocalField L] [Algebra K L]

local notation "v" => (@Valued.v K _ ℤₘ₀ _ _)

local notation "K₀" => @Valued.v.valuationSubring -- This gives an error here, but works in line 41 (?)
-- `FAE` One needs to open `Valued`, which I kind of did above.

--#check K₀ -- invalid use of field notation with `@` modifier

local notation "w" => (@Valued.v K _ ℤₘ₀ _ _)

--local notation "L₀" => w.valuationSubring -- Same error

/- local notation "e("L","K")" => Ideal.ramificationIdx (algebraMap K₀ L₀)
  (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal L₀) -/

end LocalField

namespace LocalField

open scoped DiscreteValuationRing

open Valued

variable (K : Type*) [Field K] [LocalField K] {n : ℕ} (hn : 0 < n)

local instance hv : Valued K ℤₘ₀ := inferInstance

set_option quotPrecheck false
local notation "K₀" => (hv K).v.valuationSubring

/-
local notation "v" => (@Valued.v K _ ℤₘ₀ _ _)

local notation "K₀" => v.valuationSubring

#check K₀ -- Valuation.valuationSubring v : ValuationSubring ?m.5083 (doesn't remember K)

-/

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
  convert ValuationSubring.algebra (hv K).v L
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
