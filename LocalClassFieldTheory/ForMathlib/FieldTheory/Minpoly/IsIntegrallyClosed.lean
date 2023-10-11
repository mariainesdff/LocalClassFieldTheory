import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

#align_import for_mathlib.field_theory.minpoly.is_integrally_closed

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

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- If `x : L` is an integral element in a field extension `L` over `K`, then the degree of the
  minimal polynomial of `x` over `K` divides `[L : K]`.-/
theorem degree_dvd [FiniteDimensional K L] {x : L} (hx : IsIntegral K x) :
    (minpoly K x).natDegree ∣ FiniteDimensional.finrank K L :=
  by
  rw [dvd_iff_exists_eq_mul_left, ← IntermediateField.adjoin.finrank hx]
  use FiniteDimensional.finrank (↥K⟮x⟯) L
  rw [eq_comm, mul_comm]
  exact FiniteDimensional.finrank_mul_finrank _ _ _

variable (K L)
variable (R : Subring K) [IsIntegrallyClosed R] [IsFractionRing R K]

/-- The minimal polynomial of `x` over `K` agrees with its minimal polynomial over `R`. -/
theorem minpoly_ofSubring (x : integralClosure R L) :
    Polynomial.map (algebraMap R K) (minpoly R x) = minpoly K (x : L) := by
  rw [eq_comm] <;>
    apply minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral R L x)

end minpoly

