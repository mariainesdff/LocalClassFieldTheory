import LocalClassFieldTheory.DiscreteValuationRing.Basic
import LocalClassFieldTheory.ForMathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import LocalClassFieldTheory.SpectralNorm

#align_import discrete_valuation_ring.discrete_norm

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
  rw [_root_.map_pow, ← NNReal.rpow_nat_cast,
    Nat.cast_div (minpoly.degree_dvd (isAlgebraic_iff_isIntegral.mp (h_alg ↑x)))
      (Nat.cast_ne_zero.mpr
        (ne_of_gt (minpoly.natDegree_pos (isAlgebraic_iff_isIntegral.mp (h_alg ↑x))))),
    div_eq_mul_inv, mul_comm (finrank K L : ℝ), NNReal.rpow_mul, ← one_div]

end AuxLemma

namespace DiscreteValuation

variable (K : Type _) [Field K] [hv : Valued K ℤₘ₀] [IsDiscrete hv.v]

section DiscreteNorm

/-- The normed field structure on `K` induced by its discrete valuation. -/
def discretelyNormedField : NormedField K :=
  RankOneValuation.ValuedField.toNormedField K ℤₘ₀

/-- The nontrivially normed field structure on `K` induced by its discrete valuation. -/
@[reducible]
def nontriviallyDiscretelyNormedField : NontriviallyNormedField K :=
  { @RankOneValuation.ValuedField.toNormedField K _ ℤₘ₀ _ _ (DiscreteValuation.isRankOne _) with
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

theorem norm_isNonarchimedean : IsNonarchimedean (@norm K (hasDiscreteNorm K)) := fun x y =>
  RankOneValuation.normDef_add_le x y

theorem norm_le_one_iff_val_le_one (x : K) :
    (@norm K (hasDiscreteNorm K)) x ≤ 1 ↔ Valued.v x ≤ (1 : ℤₘ₀) :=
  RankOneValuation.norm_le_one_iff_val_le_one x

variable [CompleteSpace K] {L : Type _} [Field L] [Algebra K L]

variable {K}
/-- The unique norm on `L` extending the norm on `K`. -/
def discreteNormExtension (h_alg : Algebra.IsAlgebraic K L) :
    @MulAlgebraNorm K (discretelySemiNormedCommRing K) L _ _ :=
  @spectralMulAlgNorm K (nontriviallyDiscretelyNormedField K) L _ _ h_alg _
    (norm_isNonarchimedean K)

/-- The `normed_field` structure on `L` induced by `discrete_norm_extension h_alg` -/
def discretelyNormedFieldExtension (h_alg : Algebra.IsAlgebraic K L) : NormedField L :=
  @spectralNormToNormedField K (nontriviallyDiscretelyNormedField K) L _ _ _ h_alg
    (norm_isNonarchimedean K)

/-- The `uniform_space` structure on `L` induced by `discrete_norm_extension h_alg` -/
def discretelyNormedFieldExtensionUniformSpace (h_alg : Algebra.IsAlgebraic K L) :
  UniformSpace L := by
  have := discretelyNormedFieldExtension h_alg
  infer_instance

namespace DiscreteNormExtension

theorem zero (h_alg : Algebra.IsAlgebraic K L) : discreteNormExtension h_alg 0 = 0 :=
  @spectralNorm_zero K (discretelyNormedField K) L _ _

/-- For any `x : L`, `discrete_norm_extension h_alg x` is equal to the norm of the zeroth
  coefficient of the minimal polynomial of `x` over `K`, raised to the
  `(1/(minpoly K x).nat_degree` power. -/
theorem eq_root_zero_coeff (h_alg : Algebra.IsAlgebraic K L) (x : L) :
    discreteNormExtension h_alg x =
      withZeroMultIntToNNReal (base_ne_zero K hv.v) (Valued.v ((minpoly K x).coeff 0)) ^
        (1 / (minpoly K x).natDegree : ℝ) :=
  @spectralNorm_eq_root_zero_coeff K (nontriviallyDiscretelyNormedField K) _ L _ _ h_alg
    (norm_isNonarchimedean K) x

theorem pow_eq_pow_root_zero_coeff' (h_alg : Algebra.IsAlgebraic K L) (x : L) (n : ℕ) :
    discreteNormExtension h_alg x ^ n =
      withZeroMultIntToNNReal (base_ne_zero K hv.v) (Valued.v ((minpoly K x).coeff 0)) ^
        (n / (minpoly K x).natDegree : ℝ) := by
  rw [div_eq_inv_mul, Real.rpow_mul NNReal.zero_le_coe, eq_root_zero_coeff, inv_eq_one_div,
    Real.rpow_nat_cast]

theorem pow_eq_pow_root_zero_coeff (h_alg : Algebra.IsAlgebraic K L) (x : L) {n : ℕ}
    (hn : (minpoly K x).natDegree ∣ n) : discreteNormExtension h_alg x ^ n =
      withZeroMultIntToNNReal (base_ne_zero K hv.v) (Valued.v ((minpoly K x).coeff 0)) ^
        (n / (minpoly K x).natDegree) := by
  nth_rw 2 [← Real.rpow_nat_cast]
  rw [Nat.cast_div hn (Nat.cast_ne_zero.mpr
    (ne_of_gt (minpoly.natDegree_pos (isAlgebraic_iff_isIntegral.mp (h_alg x)))))]
  exact pow_eq_pow_root_zero_coeff' h_alg x n

theorem nonneg (h_alg : Algebra.IsAlgebraic K L) (x : L) : 0 ≤ discreteNormExtension h_alg x :=
  @spectralNorm_nonneg K (discretelyNormedField K) L _ _ _

theorem isNonarchimedean (h_alg : Algebra.IsAlgebraic K L) :
    IsNonarchimedean (discreteNormExtension h_alg) :=
  @spectralNorm_isNonarchimedean K (discretelyNormedField K) L _ _ h_alg (norm_isNonarchimedean K)

theorem hMul (h_alg : Algebra.IsAlgebraic K L) (x y : L) :
    discreteNormExtension h_alg (x * y) =
      discreteNormExtension h_alg x * discreteNormExtension h_alg y :=
  @spectral_norm_is_mul K (nontriviallyDiscretelyNormedField K) L _ _ h_alg _
    (norm_isNonarchimedean K) x y

theorem le_one_iff_integral_minpoly (h_alg : Algebra.IsAlgebraic K L) (x : L) :
    discreteNormExtension h_alg x ≤ 1 ↔ ∀ n : ℕ, hv.v ((minpoly K x).coeff n) ≤ 1 := by
  let _ := nontriviallyDiscretelyNormedField K
  have h : spectralMulAlgNorm h_alg (norm_isNonarchimedean _) x = spectralNorm K L x := by
    rfl
  rw [discreteNormExtension, h, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (isAlgebraic_iff_isIntegral.mp (h_alg x)))]
  simp_rw [norm_le_one_iff_val_le_one]

theorem of_integer [fr : IsFractionRing hv.v.valuationSubring.toSubring K]
  (h_alg : Algebra.IsAlgebraic K L) (x : integralClosure hv.v.valuationSubring.toSubring L) :
  discreteNormExtension h_alg x =
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
    (h_alg : Algebra.IsAlgebraic K L) (x : integralClosure hv.v.valuationSubring.toSubring L) :
    discreteNormExtension h_alg x ≤ 1 := by
  letI := nontriviallyDiscretelyNormedField K
  let min_int := minpoly hv.v.valuationSubring.toSubring x
  let min_x : Polynomial K := Polynomial.map (algebraMap _ _) min_int
  rw [of_integer]
  refine' ciSup_le _
  intro n
  simp only [spectralValueTerms]
  split_ifs with hn
  · have coeff_coe : ∀ n : ℕ, min_x.coeff n = min_int.coeff n := fun n => by
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
