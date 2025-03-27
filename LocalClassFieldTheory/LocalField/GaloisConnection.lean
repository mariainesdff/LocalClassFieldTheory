/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
-- import LocalClassFieldTheory.DiscreteValuationRing.Ramification
import LocalClassFieldTheory.LocalField.Basic
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.RingTheory.Valuation.ValExtension

noncomputable section

namespace NonarchLocalField

open scoped Multiplicative NNReal /- Valued -/

open Valuation

variable (K : Type*) {L : Type*} [Field K] [Field L] [ValuedLocalField K]
variable [Algebra K L]
variable {Γ₀ Γ₁: outParam Type*} [LinearOrderedCommGroupWithZero Γ₁]
-- Cannot ask for `Valued L Γ₀` because this does not work if `l/K` is simply algebraic but infinite

variable (vL : Valuation L Γ₁) [IsValExtension ((@Valued.v K _ ℤₘ₀ _ _)) vL]

local notation "vK" => (@Valued.v K _ ℤₘ₀ _ _)

/-Re-open `Valued` if this is needed -/
-- def normedF : NormedField L := by
--   exact spectralNorm.normedField (Valued.isNonarchimedean_norm K ℤₘ₀)

local notation "K₀" => Valuation.valuationSubring vK
local notation "L₀" => Valuation.valuationSubring vL

section Algebra

-- Probably `ValuedLocalField K` is too much, `Valued K Γ₀` should be enough
lemma algebraMap_mem (x : K₀) : algebraMap K L x ∈ L₀ := by
  simp only [mem_valuationSubring_iff]
  have h1 : vL ((algebraMap K L) 1) = 1 := by simp only [_root_.map_one]
  rw [← h1]
  rw [IsValExtension.val_map_le_iff (vR := vK)]
  simp only [_root_.map_one]
  exact x.2

instance : Algebra K₀ L₀ := by
  apply RingHom.toAlgebra
  sorry


structure IntegrallyClosedSubalgebra extends Subalgebra K₀ L₀ where
  is_int_closed : IsIntegrallyClosed toSubalgebra

#synth Preorder (Subalgebra K₀ L₀)
#synth CompleteLattice (IntermediateField K L)

-- probably better to put a `CompleteLattice` instance as for `IntermediateField`
instance : Preorder (IntegrallyClosedSubalgebra K vL) where
  le := ( ·.1 ≤ ·.1)
  le_refl := by simp
  le_trans := by
    intro A B C hAB hAC
    simp only at hAB hAC ⊢
    exact hAB.trans hAC

lemma IntegrallyClosed_of_IntegrallyClosedSubalgebra (A : IntegrallyClosedSubalgebra K vL) :
  IsIntegrallyClosed A.toSubalgebra := IntegrallyClosedSubalgebra.is_int_closed ..

open IsLocalRing

-- Probably `ValuedLocalField K` is too much, `Valued K Γ₀` should be enough
lemma maximalIdeal_mem (x : maximalIdeal K₀) : algebraMap K₀ L₀ x.1 ∈ (maximalIdeal L₀) := by
  sorry
  -- simp only [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  -- have h1 : vL ((algebraMap K L) 1) = 1 := by simp only [_root_.map_one]
  -- rw [← h1]
  -- rw [IsValExtension.val_map_le_iff (vR := vK)]
  -- simp only [_root_.map_one]
  -- exact x.2

instance : Algebra (ResidueField K₀) (ResidueField L₀) := by
  apply RingHom.toAlgebra
  sorry

end Algebra


variable [Algebra.IsSeparable K L] [Valuation.RankOne vL]

def fracField : (IntegrallyClosedSubalgebra K vL) → (IntermediateField K L) := by
  intro A
  sorry

def unitBall : (IntermediateField K L) → (IntegrallyClosedSubalgebra K vL) := by
  intro E
  let E₀ : Subring E := Valued.v.integer
  sorry

theorem fracField_gc : GaloisConnection (fracField K vL) (unitBall K vL) := sorry

def fracField_gi : GaloisInsertion (fracField K vL) (unitBall K vL) := by
  apply (fracField_gc K vL).toGaloisInsertion
  sorry

def fracField_gci : GaloisCoinsertion (fracField K vL) (unitBall K vL) := by
  apply (fracField_gc K vL).toGaloisCoinsertion
  sorry

open IsLocalRing


def wittRing : (IntermediateField (ResidueField K₀) (ResidueField L₀)) →
    (IntegrallyClosedSubalgebra K vL) := by
  intro k
  sorry

def resField : (IntegrallyClosedSubalgebra K vL) →
    (IntermediateField (ResidueField K₀) (ResidueField L₀)) := by
  intro A
  have hA : IsLocalRing A.1 := sorry
  let k := ResidueField A.1
  sorry

theorem wittRing_gc : GaloisConnection (wittRing K vL) (resField K vL) := sorry

def wittRing_gi : GaloisInsertion (wittRing K vL) (resField K vL) := by
  apply (wittRing_gc K vL).toGaloisInsertion
  sorry

def wittRing_gci : GaloisCoinsertion (wittRing K vL) (resField K vL) := by
  apply (wittRing_gc K vL).toGaloisCoinsertion
  sorry


end NonarchLocalField
