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

instance algebra' : Algebra v.ValuationSubring L :=
  Algebra.ofSubring v.ValuationSubring.toSubring

@[simp]
theorem algebraMap_def :
    algebraMap v.ValuationSubring L = (ValuationSubring.algebra' v L).toRingHom :=
  rfl

instance : IsScalarTower v.ValuationSubring K L :=
  IsScalarTower.subsemiring v.ValuationSubring.toSubsemiring

theorem algebraMap_injective : Injective (algebraMap v.ValuationSubring L) :=
  Injective.comp (algebraMap K L).Injective (IsFractionRing.injective v.ValuationSubring K)

theorem isIntegral_of_mem_ring_of_integers {x : L} (hx : x ∈ integralClosure v.ValuationSubring L) :
    IsIntegral v.ValuationSubring (⟨x, hx⟩ : integralClosure v.ValuationSubring L) :=
  by
  obtain ⟨P, hPm, hP⟩ := hx
  refine' ⟨P, hPm, _⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]

variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

instance int_isScalarTower : IsScalarTower v.ValuationSubring L E
    where smul_assoc x y z := by
    nth_rw 1 [← one_smul K y]
    rw [← one_smul K (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc]

/-- Given an algebra between two field extensions `L` and `E` of a field `K` with a valuation `v`,
  create an algebra between their two rings of integers. For now, this is not an instance by
  default as it creates an equal-but-not-defeq diamond with `algebra.id` when `L = E`.
  This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. It will be an instance when
  ported to Lean 4, since the above will not be an issue. -/
def valuationSubringAlgebra :
    Algebra (integralClosure v.ValuationSubring L) (integralClosure v.ValuationSubring E) :=
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
protected noncomputable def equiv (R : Type _) [CommRing R] [Algebra v.ValuationSubring R]
    [Algebra R L] [IsScalarTower v.ValuationSubring R L]
    [IsIntegralClosure R v.ValuationSubring L] : integralClosure v.ValuationSubring L ≃+* R :=
  (IsIntegralClosure.equiv v.ValuationSubring R L
        (integralClosure v.ValuationSubring L)).symm.toRingEquiv

theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.ValuationSubring (integralClosure v.ValuationSubring L)) :=
  by
  have hinj : injective ⇑(algebraMap v.valuation_subring L) :=
    ValuationSubring.algebraMap_injective v L
  rw [injective_iff_map_eq_zero
      (algebraMap v.valuation_subring ↥(integralClosure v.valuation_subring L))]
  intro x hx
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hx
  rw [injective_iff_map_eq_zero (algebraMap v.valuation_subring L)] at hinj
  exact hinj x hx

end ValuationSubring
