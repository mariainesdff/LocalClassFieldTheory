/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Valuation.ValuationRing

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

-- In PR #15736

open FiniteDimensional minpoly Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L]

namespace Valuation

-- TODO: minpoly namespace
/- For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebra_map K L x` over `K` is equal to the valuation of `x`.-/
theorem coeff_zero (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg]

-- TODO: move to Mathlib.RingTheory.Valuation.ValuationRing
theorem unit_ne_zero (x : Kˣ) : v x ≠ (0 : Γ₀) := by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

variable {L}

-- TODO: minpoly namespace, rename
/- For any unit `x : Lˣ`, we prove that a certain power of the valuation of
  zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful
  for defining the valuation on `L` inducing `v`.-/
theorem unit_pow_ne_zero [FiniteDimensional K L] (x : Lˣ) :
    v ((minpoly K x.1).coeff 0) ^ (finrank K L / (minpoly K x.1).natDegree) ≠ (0 : Γ₀) := by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx : IsIntegral K x.val := (Algebra.IsAlgebraic.isAlgebraic x.val).isIntegral
  have hdeg := Nat.div_pos (natDegree_le x.val) (natDegree_pos hx)
  rw [ne_eq, pow_eq_zero_iff hdeg.ne.symm, Valuation.zero_iff]
  exact coeff_zero_ne_zero hx (Units.ne_zero x)

end Valuation
