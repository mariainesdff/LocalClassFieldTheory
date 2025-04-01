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

import Mathlib.RingTheory.Henselian

noncomputable section

namespace NonarchLocalField

open scoped Multiplicative NNReal /- Valued -/

open Valuation

variable (K : Type*) [Field K] [ValuedLocalField K]

scoped notation "w_["K"]" => (@Valued.v K _ ℤₘ₀ _ _)

/-Re-open `Valued` if this is needed -/
-- def normedF : NormedField L := by
--   exact spectralNorm.normedField (Valued.isNonarchimedean_norm K ℤₘ₀)

scoped notation "["K"]₀" => Valuation.valuationSubring w_[K]

--#check [K]₀

section InfiniteExtension

variable {L : Type*} [Field L] [Algebra K L]
variable {Γ₀ Γ₁: outParam Type*} [LinearOrderedCommGroupWithZero Γ₁]
-- Cannot ask for `Valued L Γ₀` because this does not work if `L/K` is simply algebraic but infinite

variable (vL : Valuation L Γ₁) [IsValExtension ((@Valued.v K _ ℤₘ₀ _ _)) vL]

local notation "L₀" => Valuation.valuationSubring vL

section Algebra

structure IntegrallyClosedSubalgebra extends Subalgebra [K]₀ L₀ where
  is_int_closed : IsIntegrallyClosed toSubalgebra

--#synth Preorder (Subalgebra [K]₀ L₀)
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
lemma maximalIdeal_mem (x : maximalIdeal [K]₀) : algebraMap [K]₀ L₀ x.1 ∈ (maximalIdeal L₀) := by
  sorry
  -- simp only [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  -- have h1 : vL ((algebraMap K L) 1) = 1 := by simp only [_root_.map_one]
  -- rw [← h1]
  -- rw [IsValExtension.val_map_le_iff (vR := vK)]
  -- simp only [_root_.map_one]
  -- exact x.2 -/

/- instance : Algebra (ResidueField [K]₀) (ResidueField L₀) := by
  apply RingHom.toAlgebra
  sorry -/

end Algebra


variable [Algebra.IsSeparable K L] [Valuation.RankOne vL]

def fracField : (IntegrallyClosedSubalgebra K vL) → (IntermediateField K L) := by
  intro A

/-   have f : L₀ →ₐ[[K]₀] L := {
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
  letI : Valued E ℤₘ₀ := sorry
 -- let E₀ : ValuationSubring E := Valued.v.valuationSubring -- TODO: this is not the right valuation,
  -- we should instead use the restriction of `vL`.
  have : IsValExtension (Valued.v (R := E)) vL := sorry
 -- have : Algebra E L := inferInstance
  let A : Subalgebra [K]₀ L₀ := {
    __ := (algebraMap [E]₀ L₀).range
    algebraMap_mem' := by
      intro x
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, RingHom.coe_range,
        Set.mem_range, Subtype.exists]
      use algebraMap K L x, IntermediateField.algebraMap_mem E ↑x
      have b : (algebraMap K L) ↑x ∈ E := IntermediateField.algebraMap_mem E ↑x
      have b_1 : ⟨(algebraMap K L) ↑x, b⟩ ∈ [E]₀ := by
        rw [mem_valuationSubring_iff]
        -- TODO: complete when the valuation on E is the correct one.
        sorry
      use b_1
      ext
      rw [coe_algebraMap_valuationSubring_eq]
      simp only [IntermediateField.algebraMap_apply,
        DiscreteValuation.coe_algebraMap_valuationSubring_eq] }
  letI hE₀ : IsIntegrallyClosed [E]₀ := sorry --inferInstance
  use A
  change IsIntegrallyClosed (algebraMap [E]₀ L₀).range
  simp only [IsIntegrallyClosed]
  let _ : Algebra ↥(algebraMap ↥[E]₀ ↥L₀).range [E]₀ := sorry
  rw [AlgEquiv.isIntegrallyClosedIn (R := (algebraMap [E]₀ L₀).range) (B := FractionRing [E]₀)
    (A := FractionRing (algebraMap [E]₀ L₀).range)]
  simp only [isIntegrallyClosedIn_iff]

  sorry

  /- change IsIntegrallyClosed (algebraMap [E]₀ L₀).range
  simp only [IsIntegrallyClosed]
  let _ : Algebra ↥(algebraMap ↥[E]₀ ↥L₀).range [E]₀ := sorry
  rw [AlgEquiv.isIntegrallyClosedIn (R := (algebraMap [E]₀ L₀).range) (B := FractionRing [E]₀)
     (A := FractionRing (algebraMap [E]₀ L₀).range)] -/

  /-
  refine AlgHom.isIntegrallyClosedIn (R := [E]₀) (A := [E]₀) (B := (algebraMap [E]₀ L₀).range)
    ?_ ?_ ?_ -/
  sorry

theorem fracField_gc : GaloisConnection (fracField K vL) (unitBall K vL) := sorry

def fracField_gi : GaloisInsertion (fracField K vL) (unitBall K vL) := by
  apply (fracField_gc K vL).toGaloisInsertion
  sorry

def fracField_gci : GaloisCoinsertion (fracField K vL) (unitBall K vL) := by
  apply (fracField_gc K vL).toGaloisCoinsertion
  sorry

end InfiniteExtension

open IsLocalRing

section Henselian

variable {E : Type*} [Field E] [ValuedLocalField E] [Algebra K E] [FiniteDimensional K E]

--local notation "vE" => (@Valued.v E _ ℤₘ₀ _ _)
--local notation "[E]₀" => Valuation.valuationSubring vE

instance henselianRing : HenselianRing [E]₀ (maximalIdeal [E]₀) := sorry

variable [IsValExtension (@Valued.v K _ ℤₘ₀ _ _) (@Valued.v E _ ℤₘ₀ _ _)]

--instance : Algebra [K]₀ [E]₀ := inferInstance

variable (k' : IntermediateField (ResidueField [K]₀) (ResidueField [E]₀))

instance : Finite (ResidueField k') := sorry -- by use (ResidueField )

open Polynomial

def resPoly : Polynomial (ResidueField [K]₀) := X ^ (Nat.card k') - X

def poly : Polynomial [K]₀ := X ^ (Nat.card k') - X

lemma poly_mod_eq_resPoly :
  Polynomial.map (Ideal.Quotient.mk (maximalIdeal [K]₀)) (poly K k') = resPoly K k' := sorry

def resPoly_root : k' := by
  have h0 : (resPoly K k').degree ≠ 0 := sorry
  have hsplits : Splits (algebraMap (ResidueField [K]₀) k') (resPoly K k') := sorry
  exact Polynomial.rootOfSplits (algebraMap (ResidueField [K]₀) k') hsplits h0

def lift_resPoly_root₀ :
    [E]₀ := Quotient.out (resPoly_root K k' : ResidueField [E]₀)

lemma lift_root₀_mod_is_root :
    aeval (IsLocalRing.residue [E]₀ (lift_resPoly_root₀ K k')) (resPoly K k') = 0 :=
  sorry

def poly_root : [E]₀ := by
  have := (henselianRing (E := E)).is_henselian (Polynomial.map (algebraMap [K]₀ [E]₀)
    (poly K k')) (by sorry) (lift_resPoly_root₀ K k') ?_ ?_
  · sorry
  · sorry
  · sorry

variable (E)

def unramifiedSubalgebra : (IntermediateField (ResidueField [K]₀) (ResidueField [E]₀)) →
    (IntegrallyClosedSubalgebra K w_[E]) := by
  intro k
  use Algebra.adjoin [K]₀ {poly_root K k}
  sorry -- Chapter 1, Prop. 15 (Local Fields)

def resField : (IntegrallyClosedSubalgebra K w_[E]) →
    (IntermediateField (ResidueField [K]₀) (ResidueField [E]₀)) := by
  intro A
  have hA : IsLocalRing A.1 := sorry
  let k := ResidueField A.1
  sorry

theorem unramifiedSubalgebra_gc : GaloisConnection (unramifiedSubalgebra K E) (resField K E) :=
  sorry

def unramifiedSubalgebra_gi : GaloisInsertion (unramifiedSubalgebra K E) (resField K E) := by
  apply (unramifiedSubalgebra_gc K E).toGaloisInsertion
  sorry

def unramifiedSubalgebra_gci : GaloisCoinsertion (unramifiedSubalgebra K E) (resField K E) := by
  apply (unramifiedSubalgebra_gc K E).toGaloisCoinsertion
  sorry

end Henselian


end NonarchLocalField
