/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.AlgebraInstances
import LocalClassFieldTheory.PadicCompare
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Mixed characteristic local fields

In this file we define a mixed characteristic local field as a finite extension of
the field of `p`-adic numbers, defined as the completion `Q_p` of `ℚ` with respect to the adic
valuation associated with the maximal ideal `pℤ ⊆ ℤ`. See `padic_compare.lean` for more details
about the comparison between this type and the type `ℚ_[p]` as defined in `mathlib`.

## Main Definitions
* `mixed_char_local_field` defines a mixed characteristic local field as a finite dimensional
`Q_p`-algebra for some prime number `p`, where `Q_p` is defined in `padic_compare.lean`

##  Main Theorems
* The instance of `mixed_char_local_field` on `Q_p`.
* `ring_of_integers_equiv` proves that `Z_p`, defined as the unit ball inside `Q_p` coincides with
its ring of integers when seeing `Q_p` as a mixed characteristic local field.
* `residue_field_fintype_of_completion` proves that the residue field of the ring of integers of a
mixed characteristic local field is finite.
-/


noncomputable section

open Padic PadicComparison DiscreteValuation Valuation Padic'

open scoped DiscreteValuation

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- A mixed characteristic local field is a field which has characteristic zero and is finite
dimensional over `Q_p p`, for some prime `p`. -/
class MixedCharLocalField (p : outParam ℕ) [Fact (Nat.Prime p)] (K : Type _) [Field K] extends
    Algebra (Q_p p) K where
  [to_finiteDimensional : FiniteDimensional (Q_p p) K]

namespace MixedCharLocalField

--@[nolint dangerous_instance] --Porting note: Linter not found
instance (priority := 100) to_charZero (p : outParam ℕ) [Fact (Nat.Prime p)] (K : Type _) [Field K]
    [MixedCharLocalField p K] : CharZero K :=
  ⟨fun n m h => by
    rwa [← map_natCast (algebraMap (Q_p p) K), ← map_natCast (algebraMap (Q_p p) K),
      (algebraMap (Q_p p) K).injective.eq_iff, Nat.cast_inj] at h ⟩

attribute [instance] to_finiteDimensional

variable (K : Type _) [Field K] [MixedCharLocalField p K]

variable (L : Type _) [Field L] [MixedCharLocalField p L]

protected theorem isAlgebraic : Algebra.IsAlgebraic (Q_p p) K :=
  Algebra.IsAlgebraic.of_finite _ _

/-- The ring of integers of a mixed characteristic local field is the integral closure of ℤ_[p]
  in the local field. -/
def ringOfIntegers := integralClosure (Z_p p) K

scoped notation "𝓞" => MixedCharLocalField.ringOfIntegers

theorem mem_ringOfIntegers (x : K) : x ∈ 𝓞 p K ↔ IsIntegral (Z_p p) x := Iff.rfl

-- Porting note: needed to add this
instance : Algebra ↥(Z_p p) ↥(𝓞 p K) := Subalgebra.algebra _

theorem isIntegral_of_mem_ringOfIntegers {x : K} (hx : x ∈ 𝓞 p K) :
    IsIntegral (Z_p p) (⟨x, hx⟩ : 𝓞 p K) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P, hPm, ?_⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]

/-- Given an algebra between two local fields over Q_p, create an algebra between their two rings
of integers. For now, this is not an instance by default as it creates an equal-but-not-defeq
diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on
subtypes. It will be an instance when ported to Lean 4, since the above will not be an issue. -/
def ringOfIntegersAlgebra [Algebra K L] [IsScalarTower (Q_p p) K L] : Algebra (𝓞 p K) (𝓞 p L) :=
  ValuationSubring.algebra _ K L

namespace RingOfIntegers

variable {K}

noncomputable instance : IsFractionRing (𝓞 p K) K :=
  integralClosure.isFractionRing_of_finite_extension (Q_p p) _

instance : IsIntegralClosure (𝓞 p K) (Z_p p) K :=
  integralClosure.isIntegralClosure _ _

noncomputable instance : IsIntegrallyClosed (𝓞 p K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (Q_p p)

theorem isIntegral_coe (x : 𝓞 p K) : IsIntegral (Z_p p) (x.1 : K) :=
  x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `Z_p` in `K` -/
protected noncomputable def equiv (R : Type _) [CommRing R] [Algebra (Z_p p) R] [Algebra R K]
    [IsScalarTower (Z_p p) R K] [IsIntegralClosure R (Z_p p) K] : 𝓞 p K ≃+* R :=
  ValuationSubring.equiv _ K R

variable (K)

instance : CharZero (𝓞 p K) :=
  CharZero.of_module _ K

-- Porting note: needed to add this for the `IsNoetherian` instance to work.
instance : Module ↥(Z_p p) ↥(𝓞 p K) := Algebra.toModule

-- Porting note: I needed to add this for the `IsNoetherian` instance to work.
instance sMul : SMul (Z_p p) (𝓞 p K) := Algebra.toSMul

-- Porting note: I needed to add this for the `IsNoetherian` instance to work.
instance isScalarTower : IsScalarTower (Z_p p) (𝓞 p K) K :=
  IsScalarTower.subalgebra' (↥(Z_p p)) K K (𝓞 p K)

instance : IsNoetherian (Z_p p) (𝓞 p K) :=
  IsIntegralClosure.isNoetherian (Z_p p) (Q_p p) K (𝓞 p K)

theorem algebraMap_injective : Function.Injective ⇑(algebraMap (Z_p p) (ringOfIntegers p K)) :=
  ValuationSubring.integralClosure_algebraMap_injective _ K

end RingOfIntegers

end MixedCharLocalField

namespace Padic

open MixedCharLocalField

instance mixedCharLocalField (p : ℕ) [Fact (Nat.Prime p)] : MixedCharLocalField p (Q_p p)
    where to_finiteDimensional := inferInstance

-- Porting note: I needed to add this for `ringOfIntegersEquiv` to work.
instance :  SMul ↥(Z_p p) ↥(Z_p p) := Algebra.toSMul

-- Porting note: I needed to add this for `ringOfIntegersEquiv` to work.
instance isScalarTower : IsScalarTower (Z_p p) (Z_p p) (Q_p p):= IsScalarTower.left _

/-- The ring of integers of `Q_p p` as a mixed characteristic local field is just `Z_p`. -/
noncomputable def ringOfIntegersEquiv (p : ℕ) [Fact (Nat.Prime p)] :
    ringOfIntegers p (Q_p p) ≃+* Z_p p :=
  RingOfIntegers.equiv p (Z_p p)

namespace RingOfIntegers

open DiscreteValuation

instance : Fintype (IsLocalRing.ResidueField (Z_p p)) :=
  Fintype.ofEquiv _ (PadicComparison.residueField p).toEquiv.symm

/-- The `fintype` structure on the residue field of `Z_p`. -/
def residueFieldFintypeOfCompletion : Fintype (IsLocalRing.ResidueField (Z_p p)) :=
  inferInstance

lemma residueFieldFiniteOfCompletion : Finite (IsLocalRing.ResidueField (Z_p p)) :=
  Finite.of_fintype _

end RingOfIntegers

end Padic
