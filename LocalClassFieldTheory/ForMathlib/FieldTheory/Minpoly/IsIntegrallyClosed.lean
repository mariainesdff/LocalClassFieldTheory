/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomials

This file contains lemmas about minimal polynomials, to be added to the mathlib file
`field_theory.minpoly.is_integrally_closed`.


# Main Results

* `degree_dvd` : if `x : L` is an integral element in a field extension `L` over `K`, then
  the degree of the minimal polynomial of `x` over `K` divides `[L : K]`.
* `minpoly_of_subring` : If `R` is an integrally closed subring of `K`, `K` is a fraction ring of
  `R` and `x` belongs to the integral closure of `R` in `L`, then the minimal polynomial of `x`
  over `K` agrees with its minimal polynomial over `R` (applying the appropriate algebra map).
-/


namespace minpoly

open scoped IntermediateField

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

/-- If `x : L` is an integral element in a field extension `L` over `K`, then the degree of the
  minimal polynomial of `x` over `K` divides `[L : K]`.-/
theorem degree_dvd [FiniteDimensional K L] {x : L} (hx : IsIntegral K x) :
    (minpoly K x).natDegree ∣ FiniteDimensional.finrank K L := by
  rw [dvd_iff_exists_eq_mul_left, ← IntermediateField.adjoin.finrank hx]
  use FiniteDimensional.finrank K⟮x⟯ L
  rw [eq_comm, mul_comm]
  exact FiniteDimensional.finrank_mul_finrank _ _ _

variable (K L)
variable (R : Subring K) [IsIntegrallyClosed R] [IsFractionRing R K]

--Porting note: inferInstance does not work for these
instance : AddCommMonoid ↥(integralClosure (↥R) L) := by apply
  AddSubmonoidClass.toAddCommMonoid
instance : Algebra R (integralClosure (R) L) := Subalgebra.algebra (integralClosure (↥R) L)
instance : SMul R (integralClosure R L) := Algebra.toSMul
instance : IsScalarTower R ((integralClosure R L)) L :=
  IsScalarTower.subalgebra' (↥R) L L (integralClosure (↥R) L)

/-- The minimal polynomial of `x` over `K` agrees with its minimal polynomial over `R`. -/
theorem minpoly_ofSubring (x : integralClosure R L) :
    Polynomial.map (algebraMap R K) (minpoly R x) = minpoly K (x : L) := by
  rw [eq_comm]
  apply minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral R L x)

end minpoly
