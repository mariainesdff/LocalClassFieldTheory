/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
-- import LocalClassFieldTheory.DiscreteValuationRing.Ramification
import LocalClassFieldTheory.LocalField.Basic
import Mathlib.Order.GaloisConnection.Basic
import LocalClassFieldTheory.ForMathlib.IsValExtensionInstances

noncomputable section

namespace NonarchLocalField

open scoped Multiplicative NNReal /- Valued -/

open Valuation

variable (K : Type*) {L : Type*} [Field K] [Field L] [ValuedLocalField K]
variable [Algebra K L]
variable {Γ₀ Γ₁: outParam Type*} [LinearOrderedCommGroupWithZero Γ₁]
-- Cannot ask for `Valued L Γ₀` because this does not work if `L/K` is simply algebraic but infinite

variable (vL : Valuation L Γ₁) [IsValExtension ((@Valued.v K _ ℤₘ₀ _ _)) vL]

local notation "vK" => (@Valued.v K _ ℤₘ₀ _ _)

/-Re-open `Valued` if this is needed -/
-- def normedF : NormedField L := by
--   exact spectralNorm.normedField (Valued.isNonarchimedean_norm K ℤₘ₀)

local notation "K₀" => Valuation.valuationSubring vK
local notation "L₀" => Valuation.valuationSubring vL

section Algebra

structure IntegrallyClosedSubalgebra extends Subalgebra K₀ L₀ where
  is_int_closed : IsIntegrallyClosed toSubalgebra

--#synth Preorder (Subalgebra K₀ L₀)
--#synth CompleteLattice (IntermediateField K L)

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

/- -- Probably `ValuedLocalField K` is too much, `Valued K Γ₀` should be enough
lemma maximalIdeal_mem (x : maximalIdeal K₀) : algebraMap K₀ L₀ x.1 ∈ (maximalIdeal L₀) := by
  sorry
  -- simp only [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  -- have h1 : vL ((algebraMap K L) 1) = 1 := by simp only [_root_.map_one]
  -- rw [← h1]
  -- rw [IsValExtension.val_map_le_iff (vR := vK)]
  -- simp only [_root_.map_one]
  -- exact x.2 -/

/- instance : Algebra (ResidueField K₀) (ResidueField L₀) := by
  apply RingHom.toAlgebra
  sorry -/

end Algebra


variable [Algebra.IsSeparable K L] [Valuation.RankOne vL]

def fracField : (IntegrallyClosedSubalgebra K vL) → (IntermediateField K L) := by
  intro A

/-   have f : L₀ →ₐ[K₀] L := {
    toFun := (fun (x : L₀) ↦ (x : L))
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry
    commutes' := sorry }

  have := Subalgebra.map f A.1

  have := (fun (x : L₀) ↦ (x : L)) '' (A.1)
  have B : Subalgebra K L := {
    carrier := sorry
    mul_mem' := sorry
    add_mem' := sorry
    algebraMap_mem' := sorry
  }
  use B -/
  sorry

example (E : IntermediateField K L) (S : Set E.carrier) : Set L :=  S

def unitBall : (IntermediateField K L) → (IntegrallyClosedSubalgebra K vL) := by
  intro E
  let E₀ : ValuationSubring E := Valued.v.valuationSubring -- TODO: this is not the right valuation,
  -- we should instead use the restriction of `vL`.
  have : IsValExtension (Valued.v (R := E)) vL := sorry
 -- have : Algebra E L := inferInstance
  let A : Subalgebra K₀ L₀ := {
    __ := (algebraMap E₀ L₀).range
    algebraMap_mem' := by
      intro x
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, RingHom.coe_range,
        Set.mem_range, Subtype.exists]
      use algebraMap K L x, IntermediateField.algebraMap_mem E ↑x
      have b : (algebraMap K L) ↑x ∈ E := IntermediateField.algebraMap_mem E ↑x
      have b_1 : ⟨(algebraMap K L) ↑x, b⟩ ∈ E₀ := by
        rw [mem_valuationSubring_iff]
        -- TODO: complete when the valuation on E is the correct one.
        sorry
      use b_1
      ext
      rw [coe_algebraMap_valuationSubring_eq]
      simp only [IntermediateField.algebraMap_apply,
        DiscreteValuation.coe_algebraMap_valuationSubring_eq] }
  letI hE₀ : IsIntegrallyClosed E₀ := inferInstance
  use A
  change IsIntegrallyClosed (algebraMap E₀ L₀).range
  simp only [IsIntegrallyClosed]
  let _ : Algebra ↥(algebraMap ↥E₀ ↥L₀).range E₀ := sorry
  rw [AlgEquiv.isIntegrallyClosedIn (R := (algebraMap E₀ L₀).range) (B := FractionRing E₀)
    (A := FractionRing (algebraMap E₀ L₀).range)]
  simp only [isIntegrallyClosedIn_iff]

  sorry

  /- change IsIntegrallyClosed (algebraMap E₀ L₀).range
  simp only [IsIntegrallyClosed]
  let _ : Algebra ↥(algebraMap ↥E₀ ↥L₀).range E₀ := sorry
  rw [AlgEquiv.isIntegrallyClosedIn (R := (algebraMap E₀ L₀).range) (B := FractionRing E₀)
     (A := FractionRing (algebraMap E₀ L₀).range)] -/

  /-
  refine AlgHom.isIntegrallyClosedIn (R := E₀) (A := E₀) (B := (algebraMap E₀ L₀).range)
    ?_ ?_ ?_ -/
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
