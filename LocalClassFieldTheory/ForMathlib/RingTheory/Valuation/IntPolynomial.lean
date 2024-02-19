import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.AlgebraInstances

#align_import for_mathlib.ring_theory.valuation.int_polynomial

/-!
# Polynomials over the valuation subring.

Given a field `K` with a valuation `v`, in this file we construct a map from polynomials in `K[X]`
with integer coefficients to `v.valuation_subring[X]`. We provide several lemmas to deal with
coefficients, degree, and evaluation of `int_polynomial`.
This is useful when dealing with integral elements in an extension of fields.

# Main Definitions
* `valuation.int_polynomial` : given a polynomial in `K[X]` with coefficients in a field `K` with a
  valuation `v` such that all coefficients belong to `v.valuation_subring`, `int_polynomial` is the
  corresponding polynomial in `v.valuation_subring[X]`.
-/


open scoped DiscreteValuation

variable {K : Type _} [Field K] (v : Valuation K ℤₘ₀)

namespace Valuation

open Polynomial

open scoped Polynomial

/-- Given a polynomial in `K[X]` such that all coefficients belong to `v.valuation_subring`,
  `int_polynomial` is the corresponding polynomial in `v.valuation_subring[X]`. -/
def intPolynomial {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ v.valuationSubring) : v.valuationSubring[X]
    where toFinsupp :=
    { support := P.support
      toFun := fun n => ⟨P.coeff n, hP n⟩
      mem_support_toFun := fun n => by
        rw [Ne.def, ← Subring.coe_eq_zero_iff, mem_support_iff] }

namespace IntPolynomial

theorem coeff_eq {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ v.valuationSubring) (n : ℕ) :
    ↑((intPolynomial v hP).coeff n) = P.coeff n :=
  rfl

theorem leadingCoeff_eq {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ v.valuationSubring) :
    ↑(intPolynomial v hP).leadingCoeff = P.leadingCoeff :=
  rfl

theorem monic_iff {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ v.valuationSubring) :
    (intPolynomial v hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← leadingCoeff_eq, OneMemClass.coe_eq_one]

theorem natDegree {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ v.valuationSubring) :
    (intPolynomial v hP).natDegree = P.natDegree :=
  rfl

variable {L : Type _} [Field L] [Algebra K L]

theorem eval₂_eq {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ v.valuationSubring) (x : L) :
    eval₂ (algebraMap (↥v.valuationSubring) L) x (intPolynomial v hP) = aeval x P :=
  by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [Algebra.smul_def]
  rfl

end IntPolynomial

end Valuation
