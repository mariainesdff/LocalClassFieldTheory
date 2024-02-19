import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.RingTheory.Valuation.ValuationSubring

#align_import for_mathlib.ring_theory.valuation.algebra_instances

/-!
# Algebra instances

This file contains several `algebra` and `is_scalar_tower` instances related to extensions
of a field with a valuation, as well as their unit balls.

# Main Definitions
* `valuation_subring_algebra` : Given an algebra between two field extensions `L` and `E` of a
  field `K` with a valuation, create an algebra between their two rings of integers.

# Main Results

* `integral_closure_algebra_map_injective` : the unit ball of a field `K` with respect to a
  valuation injects into its integral closure in a field extension `L` of `K`.
-/


open Function Valuation

open scoped DiscreteValuation

variable {K : Type _} [Field K] (v : Valuation K ℤₘ₀) (L : Type _) [Field L] [Algebra K L]

namespace ValuationSubring

instance algebra' : Algebra v.valuationSubring L :=
  Algebra.ofSubring v.valuationSubring.toSubring

--Porting note: In Lean3 the following was already found as an instance, now it has to be specified
instance : Algebra (v.valuationSubring) (integralClosure v.valuationSubring L) :=
    Subalgebra.algebra (integralClosure (↥(valuationSubring v)) L)

-- Porting note : this instance was automatic in Lean3
instance : SMul v.valuationSubring (integralClosure v.valuationSubring L) := Algebra.toSMul


@[simp]
theorem algebraMap_def :
    algebraMap v.valuationSubring L = (ValuationSubring.algebra' v L).toRingHom := rfl

instance : IsScalarTower v.valuationSubring K L :=
  IsScalarTower.subsemiring v.valuationSubring.toSubsemiring


theorem algebraMap_injective : Injective (algebraMap v.valuationSubring L) := by
  exact (NoZeroSMulDivisors.algebraMap_injective K L).comp (IsFractionRing.injective _ _)

theorem isIntegral_of_mem_ring_of_integers {x : L} (hx : x ∈ integralClosure v.valuationSubring L) :
    IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.valuationSubring L) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine' ⟨P, hPm, _⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]

variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

instance int_isScalarTower : IsScalarTower v.valuationSubring L E where smul_assoc x y z := by
  {nth_rw 1 [← one_smul K y]
   rw [← one_smul K (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc]}

/-- Given an algebra between two field extensions `L` and `E` of a field `K` with a valuation `v`,
  create an algebra between their two rings of integers. For now, this is not an instance by
  default as it creates an equal-but-not-defeq diamond with `algebra.id` when `L = E`.
  This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. It will be an instance when
  ported to Lean 4, since the above will not be an issue. -/
def valuationSubringAlgebra :
    Algebra (integralClosure v.valuationSubring L) (integralClosure v.valuationSubring E) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
        Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_zero, _root_.map_zero]
      map_one' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_one, _root_.map_one]
      map_add' := fun x y =>
        Subtype.ext <| by simp only [_root_.map_add, Subalgebra.coe_add, Subtype.coe_mk]
      map_mul' := fun x y =>
        Subtype.ext <| by simp only [Subalgebra.coe_mul, _root_.map_mul, Subtype.coe_mk] }


/-- A ring equivalence between the integral closure of the valuation subring of `K` in `L`
  and a ring `R` satisfying `is_integral_closure R ↥(v.valuation_subring) L`. -/
protected noncomputable def equiv (R : Type _) [CommRing R] [Algebra v.valuationSubring R]
  [Algebra R L] [IsScalarTower v.valuationSubring R L]
  [IsIntegralClosure R v.valuationSubring L] : integralClosure v.valuationSubring L ≃+* R := by
  use (@IsIntegralClosure.equiv v.valuationSubring R L _ _ _ _ _ _
    (integralClosure v.valuationSubring L) _ _ _ _ _ _ ?_).symm
  sorry
  sorry
  sorry

theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.valuationSubring (integralClosure v.valuationSubring L)) :=
  by
  have hinj : Injective ⇑(algebraMap v.valuationSubring L) :=
    ValuationSubring.algebraMap_injective v L
  rw [injective_iff_map_eq_zero
      (algebraMap v.valuationSubring ↥(integralClosure v.valuationSubring L))]
  intro x hx
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hx
  rw [injective_iff_map_eq_zero (algebraMap v.valuationSubring L)] at hinj
  exact hinj x hx

end ValuationSubring
