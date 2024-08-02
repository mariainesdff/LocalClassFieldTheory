/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.Basic
import LocalClassFieldTheory.ForMathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import LocalClassFieldTheory.SpectralNorm

/-!
# Extensions of discrete norms

Let `K` be a field complete with respect to a discrete valuation, and let `L/K` be an algebraic
field extension. We endow `K` with the `norm` induced by its discrete valuation and construct
the unique norm on `L` extending the norm on `K`.

##  Main Definitions
* `discretelyNormedField` : the normed field structure on `K` induced by its discrete valuation.
* `nontrivially_discretelyNormedField` : the nontrivially normed field structure on `K` induced
  by its discrete valuation.
* `discreteNormExtension` : the unique norm on `L` extending the norm on `K`.

##  Main Theorems
* `eq_root_zero_coeff` : for any `x : L`, `discrete_norm_extension h_alg x` is equal to the norm of
  the zeroth coefficient of the minimal polynomial of `x` over `K`, raised to the
  `(1/(minpoly K x).nat_degree` power.

## Implementation Remarks

Note that in Lean 3 it is not possible to turn `discretelyNormedField K` into a global instance,
since this together with `valued K ℤₘ₀` leads to an infinite type class inference loop. This
will not be the case in Lean 4 (the Lean 4 type class algorithm can detect and get out of simple
loops like this one), so we will turn it into an instance when we port the project to Lean 4.
In the meantime, we create definitions for all of the needed structures on `K` (like `has_norm K`,
`semi_normed_comm_ring K`, etc) which can be derived from `discretelyNormedField K`.
-/


noncomputable section

open DiscreteValuation Multiplicative FiniteDimensional minpoly Polynomial Valuation WithZero

open scoped DiscreteValuation NNReal

section AuxLemma

variable {K : Type _} [Field K] {v : Valuation K ℤₘ₀} {L : Type _} [Field L] [Algebra K L]

theorem map_pow_div [FiniteDimensional K L] (x : Lˣ) :
    (withZeroMultIntToNNReal (base_ne_zero K v))
        (v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).natDegree)) =
      ((withZeroMultIntToNNReal (base_ne_zero K v)) (v ((minpoly K (x : L)).coeff 0)) ^
          (1 / ((minpoly K (x : L)).natDegree : ℝ))) ^
        (finrank K L : ℝ) := by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  rw [_root_.map_pow, ← NNReal.rpow_natCast,
    Nat.cast_div (minpoly.degree_dvd (h_alg.isAlgebraic _).isIntegral)
      (Nat.cast_ne_zero.mpr (ne_of_gt (minpoly.natDegree_pos (h_alg.isAlgebraic _).isIntegral))),
    div_eq_mul_inv, mul_comm (finrank K L : ℝ), NNReal.rpow_mul, ← one_div]

end AuxLemma

namespace DiscreteValuation

variable (K : Type _) [Field K] [hv : Valued K ℤₘ₀] [IsDiscrete hv.v]

section DiscreteNorm

/-- The normed field structure on `K` induced by its discrete valuation. -/
def discretelyNormedField : NormedField K := Valued.toNormedField K ℤₘ₀

/-- The nontrivially normed field structure on `K` induced by its discrete valuation. -/
@[reducible]
def nontriviallyDiscretelyNormedField : NontriviallyNormedField K :=
  { @Valued.toNormedField K _ ℤₘ₀ _ _ (DiscreteValuation.rankOne _) with
    non_trivial := by
      obtain ⟨x, hx⟩ := exists_Uniformizer_ofDiscrete hv.v
      use x.1⁻¹
      erw [@norm_inv K (@NormedField.toNormedDivisionRing K (discretelyNormedField K)),
        one_lt_inv_iff, RankOneValuation.norm_lt_one_iff_val_lt_one,
        RankOneValuation.norm_pos_iff_val_pos]
      exact ⟨Uniformizer_valuation_pos hv.v hx, Uniformizer_valuation_lt_one hv.v hx⟩ }

/-- The norm on `K` induced by its discrete valuation. -/
def hasDiscreteNorm : Norm K := by
  let _ : NontriviallyNormedField K := nontriviallyDiscretelyNormedField K
  infer_instance

/-- The seminormed commutative ring structure on `K` induced by its discrete valuation. -/
def discretelySemiNormedCommRing : SeminormedCommRing K := by
  let _ : NontriviallyNormedField K := nontriviallyDiscretelyNormedField K
  infer_instance

/-- The seminormed ring structure on `K` induced by its discrete valuation. -/
def discretelySemiNormedRing : SeminormedRing K := by
  let _ : NontriviallyNormedField K := nontriviallyDiscretelyNormedField K
  infer_instance

theorem norm_isNonarchimedean : IsNonarchimedean (@norm K (hasDiscreteNorm K)) := fun x y ↦
  Valued.norm_add_le x y

theorem norm_le_one_iff_val_le_one (x : K) :
    (@norm K (hasDiscreteNorm K)) x ≤ 1 ↔ Valued.v x ≤ (1 : ℤₘ₀) :=
  RankOneValuation.norm_le_one_iff_val_le_one x

variable [CompleteSpace K] {L : Type _} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

variable {K}
/-- The unique norm on `L` extending the norm on `K`. -/
def discreteNormExtension : @MulAlgebraNorm K (discretelySemiNormedCommRing K) L _ _ :=
  @spectralMulAlgNorm K (nontriviallyDiscretelyNormedField K) L _ _ _ _ (norm_isNonarchimedean K)

/-- The `normed_field` structure on `L` induced by `discrete_norm_extension h_alg` -/
def discretelyNormedFieldExtension : NormedField L :=
  @spectralNormToNormedField K (nontriviallyDiscretelyNormedField K) L _ _ _ _
    (norm_isNonarchimedean K)

/-- The `uniform_space` structure on `L` induced by `discrete_norm_extension h_alg` -/
def discretelyNormedFieldExtensionUniformSpace :
    UniformSpace L := by
  have := @discretelyNormedFieldExtension K _ _ _ _ L _ _ _
  infer_instance

namespace DiscreteNormExtension

theorem zero : discreteNormExtension (K := K) (L := L) 0 = 0 :=
  @spectralNorm_zero K (discretelyNormedField K) L _ _

/-- For any `x : L`, `discrete_norm_extension h_alg x` is equal to the norm of the zeroth
  coefficient of the minimal polynomial of `x` over `K`, raised to the
  `(1/(minpoly K x).nat_degree` power. -/
theorem eq_root_zero_coeff (x : L) : discreteNormExtension (K := K) (L := L) x =
      withZeroMultIntToNNReal (base_ne_zero K hv.v) (Valued.v ((minpoly K x).coeff 0)) ^
        (1 / (minpoly K x).natDegree : ℝ) :=
  @spectralNorm_eq_root_zero_coeff K (nontriviallyDiscretelyNormedField K) _ L _ _ _
    (norm_isNonarchimedean K) x

theorem pow_eq_pow_root_zero_coeff' (x : L) (n : ℕ) :
    discreteNormExtension (K := K) (L := L) x ^ n =
      withZeroMultIntToNNReal (base_ne_zero K hv.v) (Valued.v ((minpoly K x).coeff 0)) ^
        (n / (minpoly K x).natDegree : ℝ) := by
  rw [div_eq_inv_mul, Real.rpow_mul NNReal.zero_le_coe, eq_root_zero_coeff, inv_eq_one_div,
    Real.rpow_natCast]

theorem pow_eq_pow_root_zero_coeff (x : L) {n : ℕ} (hn : (minpoly K x).natDegree ∣ n) :
    discreteNormExtension (K := K) (L := L) x ^ n =
      withZeroMultIntToNNReal (base_ne_zero K hv.v) (Valued.v ((minpoly K x).coeff 0)) ^
        (n / (minpoly K x).natDegree) := by
  nth_rw 2 [← Real.rpow_natCast]
  rw [Nat.cast_div hn (Nat.cast_ne_zero.mpr
    (ne_of_gt (minpoly.natDegree_pos (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)))]
  exact pow_eq_pow_root_zero_coeff' x n

theorem nonneg (x : L) : 0 ≤ discreteNormExtension (K := K) (L := L) x :=
  @spectralNorm_nonneg K (discretelyNormedField K) L _ _ _

theorem isNonarchimedean : IsNonarchimedean (discreteNormExtension (K := K) (L := L)) :=
  @spectralNorm_isNonarchimedean K (discretelyNormedField K) L _ _ _ (norm_isNonarchimedean K)

theorem mul (x y : L) : discreteNormExtension (K := K) (x * y) =
      discreteNormExtension (K := K) x * discreteNormExtension (K := K) y :=
  @spectral_norm_is_mul K (nontriviallyDiscretelyNormedField K) L _ _ _ _
    (norm_isNonarchimedean K) x y

theorem le_one_iff_integral_minpoly (x : L) :
    discreteNormExtension (K := K) x ≤ 1 ↔ ∀ n : ℕ, hv.v ((minpoly K x).coeff n) ≤ 1 := by
  let _ := nontriviallyDiscretelyNormedField K
  have h : spectralMulAlgNorm (K := K) (norm_isNonarchimedean _) x = spectralNorm K L x := by
    rfl
  rw [discreteNormExtension, h, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)]
  simp_rw [norm_le_one_iff_val_le_one]

theorem of_integer [fr : IsFractionRing hv.v.valuationSubring.toSubring K]
    (x : integralClosure hv.v.valuationSubring.toSubring L) :
    discreteNormExtension (K := K) (L := L) x =
    @spectralValue K (discretelySemiNormedRing K)
    (Polynomial.map (algebraMap hv.v.valuationSubring.toSubring K)
      (minpoly hv.v.valuationSubring.toSubring x)) := by
  letI := nontriviallyDiscretelyNormedField K
  have is_minpoly : minpoly K (x : L) =
    Polynomial.map (algebraMap hv.v.valuationSubring.toSubring K)
        (minpoly hv.v.valuationSubring.toSubring x) := by
    rw [eq_comm]
    exact minpoly_ofSubring K L hv.v.valuationSubring.toSubring x
  rw [discreteNormExtension, ← is_minpoly]
  rfl

theorem le_one_of_integer [fr : IsFractionRing hv.v.valuationSubring.toSubring K]
    (x : integralClosure hv.v.valuationSubring.toSubring L) :
    discreteNormExtension (K := K) (L := L) x ≤ 1 := by
  letI := nontriviallyDiscretelyNormedField K
  let min_int := minpoly hv.v.valuationSubring.toSubring x
  let min_x : Polynomial K := Polynomial.map (algebraMap _ _) min_int
  rw [of_integer]
  refine ciSup_le ?_
  intro n
  simp only [spectralValueTerms]
  split_ifs with hn
  · have coeff_coe : ∀ n : ℕ, min_x.coeff n = min_int.coeff n := fun n ↦ by
      rw [Polynomial.coeff_map]; rfl
    rw [coeff_coe n]
    apply Real.rpow_le_one (norm_nonneg _)
    rw [norm_le_one_iff_val_le_one K]
    exact (min_int.coeff n).property
    · simp only [one_div, inv_nonneg, sub_nonneg, Nat.cast_le]
      exact le_of_lt hn
  · exact zero_le_one

end DiscreteNormExtension

end DiscreteNorm

end DiscreteValuation
