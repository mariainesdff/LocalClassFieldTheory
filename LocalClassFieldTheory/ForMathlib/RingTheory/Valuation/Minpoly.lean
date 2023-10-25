import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Valuation.ValuationSubring

#align_import for_mathlib.ring_theory.valuation.minpoly

/-!
# Minimal polynomials.

We prove some results about valuations of zero coefficients of minimal polynomials.

Let `K` be a field with a valuation `v` and let `L` be a field extension of `K`.

# Main Results
* `coeff_zero` : for `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
  of `algebra_map K L x` over `K` is equal to the valuation of `x`.
* `unit_pow_ne_zero` : for any unit `x : Lˣ`, we prove that a certain power of the valuation of
  zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful
  for defining the valuation on `L` inducing `v`.
-/


open FiniteDimensional minpoly Polynomial

open scoped DiscreteValuation

variable {K : Type _} [Field K] {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) {L : Type _} [Field L] [Algebra K L]

namespace Valuation

/- For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebra_map K L x` over `K` is equal to the valuation of `x`.-/
theorem coeff_zero (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg]

theorem unit_ne_zero (x : Kˣ) : v x ≠ (0 : Γ₀) := by
  simp only [Ne.def, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

/- For any unit `x : Lˣ`, we prove that a certain power of the valuation of
  zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful
  for defining the valuation on `L` inducing `v`.-/
theorem unit_pow_ne_zero [FiniteDimensional K L] (x : Lˣ) :
    v ((minpoly K x.1).coeff 0) ^ (finrank K L / (minpoly K x.1).natDegree) ≠ (0 : Γ₀) :=
  by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.isAlgebraic_of_finite K L
  have hdeg : 0 < finrank K L / (minpoly K x.val).natDegree :=
    Nat.div_pos (nat_degree_le (is_algebraic_iff_is_integral.mp (h_alg x.val)))
      (nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x.val)))
  rw [Ne.def, pow_eq_zero_iff hdeg, Valuation.zero_iff]
  exact coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg x.val)) (Units.ne_zero x)
  infer_instance

end Valuation
