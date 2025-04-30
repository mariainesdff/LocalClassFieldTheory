/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
--import LocalClassFieldTheory.ForMathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # The residue field of a DVR
In this file we consider a finite extension `L/K` of a discretely valued field `K`. By the results
in `discrete_valuation_ring.basic`, the unit ball `K₀` is a DVR and the main result we prove is that
(under the assumption that `L/K` is separable, currently needed to ensure that the integral closure
of `K₀` in `L` is finite over `K₀`, but that should potentially be removed), the residue field of
the integral closure of `K₀` in `L` is finite dimensional over the residue field of `K₀`. As a
consequence, when the residue field of `K₀` is finite, so is the residue field of `L₀`

## Main definitions
* `ExtendedMaxIdeal` The ideal in `L` extending the maximal ideal of `K₀.
* `quotient_linear_iso` The equivalence as vector spaces over the residue field of the base of
  * the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below;
    and
  * the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
  induced by the equality of the two ideals proved in `Extended_eq_powE`
* `finite_residue_field_of_integral_closure` and `finite_residue_field_of_unit_ball` are the proofs
  that whenever `L/K` is separable, and the residue field of `K₀` is finite, so is also the residue
  field both of the integral closure of `K₀` in `L` and of the unit ball `L₀`.

## Main results
* `ramification_idx_maximal_ne_zero` The ramification index of the maximal ideal in the integral
  closure of `K₀` in `L` over the maximal ideal of `K₀` is non zero.
* `ramification_idx_Extended_ne_zero` The ramification index of the extension of the maximal ideal
  of `K₀` to the ring of integers of `L`, over the maximal ideal of `K₀` is non zero.
* `Extended_eq_powE` The equality between the the extension of the maximal ideal
  of `K₀` to the ring of integers of `L` and the `e`-th power of the maximal ideal in this integral
  closure, where `e ≠ 0` is the ramification index.
* `finite_dimensional_residue_field_of_integral_closure` When `L/K` is (finite and) separable, the
  residue field of the integral closure of `K₀` in `L` (or, equivalently, of `L₀` in view of the
  declaration `integral_closure_eq_integer`  proven in `discrete_valuation_ring.extensions`) is
  finite dimensional over the residue field of `K₀`.


## Implementation details
* `algebra_mod_power_e` is an `instance` while `algebra_mod_Extended` is only a `definition`, turned
  into a `local instance`. This is because the type-class inference mechanism seems unable to find
  the second instance automatically even if it is marked as such, so it has sometimes to be called
  explicitely.
* To prove that the residue field of `L₀` is finite (under suitable assumptions) we first prove that
  the residue field of the integral closure of `K₀` in `L` is finite, and then we use
  `integral_closure_eq_integer` proven in `discrete_valuation_ring.extensions` to transfer this
  finiteness to `L₀`.
-/

open IsLocalRing Valuation Ideal DiscreteValuation Multiplicative Integer Extension

noncomputable section

universe u w

namespace DiscreteValuation

variable (K : Type*) [Field K] [hv : Valued K ℤₘ₀] [IsDiscrete' hv.v] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

local notation3 "K₀" => hv.v.valuationSubring

local notation3 "S" => (integralClosure K₀ L)

-- Porting note: needed to add this to avoid timeouts *FAE*: Re-check
instance : Module K₀ S := Algebra.toModule

instance : IsDiscreteValuationRing S :=
  DiscreteValuation.integralClosure.discreteValuationRing_of_finite_extension K L

instance [Algebra.IsSeparable K L] : IsNoetherian K₀ S := IsIntegralClosure.isNoetherian K₀ K L S

instance : IsLocalHom (algebraMap K₀ S) := by
  constructor
  intro _ ha
  obtain ⟨Q, hQ_max, hQ⟩ := exists_ideal_over_maximal_of_isIntegral _
    (le_maximalIdeal (RingHom.ker_ne_top (algebraMap K₀ S)))
  rw [← @not_not (IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal] at ha ⊢
  rwa [← hQ, mem_comap, eq_maximalIdeal hQ_max]

-- NOTE: probably this is not needed anymore.
theorem FiniteDimensional_residueField_of_integralClosure [Algebra.IsSeparable K L] :
    FiniteDimensional (ResidueField K₀) (ResidueField (integralClosure K₀ L)) :=
  ResidueField.finite_of_module_finite

theorem finiteResidueFieldOfIntegralClosure [Algebra.IsSeparable K L]
    (hfin : Finite (ResidueField K₀)) : Finite (ResidueField S) :=
  ResidueField.finite_of_finite hfin

lemma finiteResidueFieldOfUnitBall [Algebra.IsSeparable K L]
    (hfin : Finite (ResidueField K₀)) :
    Finite (ResidueField (extendedValuation K L).valuationSubring) :=
  let _ : IsLocalRing (extendedValuation K L).valuationSubring := inferInstance -- Needed to avoid error
  let _ : IsLocalRing ↥(Subalgebra.toSubring (integralClosure (↥K₀) L)) :=
    inferInstanceAs (IsLocalRing (integralClosure (↥K₀) L))
  @Finite.of_equiv _ _ (finiteResidueFieldOfIntegralClosure K L hfin)
    (ResidueField.mapEquiv
        (RingEquiv.subringCongr
          (DiscreteValuation.Extension.integralClosure_eq_integer K L))).toEquiv

-- This should probably be omitted, since we are shifting from `Finite` to `Fintype`.
def fintypeResidueFieldOfIntegralClosure [Algebra.IsSeparable K L]
    (hfin : Fintype (ResidueField K₀)) : Fintype (ResidueField S) := by
  let _ := @Finite.of_fintype _ hfin
  exact @Fintype.ofFinite (ResidueField S) (finiteResidueFieldOfIntegralClosure K L inferInstance)

def fintypeResidueFieldOfUnitBall [Algebra.IsSeparable K L]
    (hfin : Fintype (ResidueField K₀)) :
    Fintype (ResidueField (extendedValuation K L).valuationSubring) :=
  let _ : IsLocalRing (extendedValuation K L).valuationSubring := inferInstance -- Needed to avoid error
  let _ : IsLocalRing ↥(Subalgebra.toSubring (integralClosure (↥K₀) L)) :=
    inferInstanceAs (IsLocalRing (integralClosure (↥K₀) L))
  @Fintype.ofEquiv _ _ (fintypeResidueFieldOfIntegralClosure K L hfin)
    (ResidueField.mapEquiv
        (RingEquiv.subringCongr
          (DiscreteValuation.Extension.integralClosure_eq_integer K L))).toEquiv


end DiscreteValuation
