/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.FromMathlib.SpectralNormUnique
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# A formula for the spectral norm

Let `K` be a field complete with respect to the topology induced by a nontrivial nonarchimedean
norm, and let `L` be an algebraic field extension of `K`. We prove an explicit formula for the
spectral norm of an element `x : L`.

##  Main Theorems
* `spectral_value_le_one_iff` : the spectral value of a monic polynomial `P` is `≤ 1` if and only
  if all of its coefficients have norm `≤ 1`.
* `spectralNorm_pow_natDegree_eq_prod_roots` : given an algebraic tower of fields `E/L/K` and an
  element `x : L` whose minimal polynomial `f` over `K` splits into linear factors over `E`, the
  `degree(f)`th power of the spectral norm of `x` is equal to the product of the `E`-valued roots
  of `f`.
* `spectral_norm_eq_root_zero_coeff` : given `x : L` with minimal polynomial
  `f(X) := X^n + a_{n-1}X^{n-1} + ... + a_0` over `K`, the spectral norm of `x` is equal to
  `‖ a_0 ‖^(1/(degree(f(X))))`.
-/


open scoped NNReal Polynomial

open NNReal Polynomial

section spectralValue

variable {S : Type*} [NormedDivisionRing S]

/- NOTE TO FILIPPO: This was in #23178 but did not make it to the final version, which ended up
being only about pow lemmas. I think we should PR it again, but in the meantime I am adding it
here to fix the following proof. -/
theorem lt_ciSup_of_lt {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
   {f : ι → α} (H : BddAbove (Set.range f)) (i : ι) {a : α} (h : a < f i) :
    a < iSup f :=
  lt_of_lt_of_le h (le_ciSup H i)

-- [LocalClassFieldTheory.FromMathlib.SpectralNorm] (corresponding Mathlib file)
/-- The spectral value of a monic polynomial `P` is less than or equal to one if and only
  if all of its coefficients have norm less than or equal to 1. -/
theorem spectralValue_le_one_iff {P : S[X]} (hP : Monic P) :
    spectralValue P ≤ 1 ↔ ∀ n : ℕ, ‖P.coeff n‖ ≤ 1 := by
  rw [spectralValue]
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · by_contra hn
    rw [not_le] at hn
    have hsupr : 1 < iSup (spectralValueTerms P) :=
      haveI hn' : 1 < spectralValueTerms P n := by
        simp only [spectralValueTerms]
        split_ifs with hPn
        · exact Real.one_lt_rpow hn
            (by simp only [one_div, inv_pos, sub_pos, Nat.cast_lt, hPn])
        · rw [not_lt, le_iff_lt_or_eq] at hPn
          rcases hPn with hlt | heq
          · simpa [coeff_eq_zero_of_natDegree_lt hlt, norm_zero] using hn
          · rw [Monic, leadingCoeff, heq] at hP
            rw [hP, norm_one] at hn
            linarith
      lt_ciSup_of_lt (spectralValueTerms_bddAbove P) n hn'
    linarith
  · apply ciSup_le (fun n ↦ ?_)
    rw [spectralValueTerms]
    split_ifs with hn
    · apply Real.rpow_le_one (norm_nonneg _) (h n)
      rw [one_div_nonneg, sub_nonneg, Nat.cast_le]
      exact le_of_lt hn
    · exact zero_le_one

end spectralValue

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [hu : IsUltrametricDist K] {L : Type*} [Field L] [Algebra K L]

/- Inlined
theorem Real.eq_rpow_one_div_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {z : ℝ} (hz : z ≠ 0) :
    x = y ^ (1 / z) ↔ x ^ z = y := by
  rw [one_div, Real.eq_rpow_inv hx hy hz] -/

-- [Mathlib.Algebra.Polynomial.Lifts]
theorem Polynomial.mapAlg_comp {A : Type*} (B C : Type*) [CommSemiring A] [CommSemiring B]
    [Semiring C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (p : A[X]) :
    (mapAlg A C) p = (mapAlg B C) (mapAlg A B p) := by
  simp [mapAlg_eq_map, map_map, IsScalarTower.algebraMap_eq A B C]

-- [Mathlib.Algebra.Polynomial.Lifts]
theorem Polynomial.coeff_zero_of_isScalarTower {A : Type*} (B C : Type*) [CommSemiring A]
    [CommSemiring B] [Semiring C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (p : A[X]) : (algebraMap B C) ((algebraMap A B) (p.coeff 0)) = (mapAlg A C p).coeff 0 := by
  have h : algebraMap A C = (algebraMap B C).comp (algebraMap A B) := by
    ext a
    simp [Algebra.algebraMap_eq_smul_one, RingHom.coe_comp, Function.comp_apply]
  rw [mapAlg_eq_map, coeff_map, h, RingHom.comp_apply]

-- [Mathlib.FieldTheory.SplittingField.IsSplittingField]
theorem IsScalarTower.splits {F L E: Type*} [CommRing F] [Field L] [Algebra F L] (x : L) [Field E]
    [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    (hE : IsSplittingField L E (mapAlg F L (minpoly F x))) :
    Splits (RingHom.id E) (mapAlg F E (minpoly F x)) := by
  rw [Polynomial.mapAlg_comp L E (minpoly F x), mapAlg_eq_map, splits_map_iff,
    RingHomCompTriple.comp_eq]
  exact IsSplittingField.splits _ _

-- [Mathlib.FieldTheory.SplittingField.IsSplittingField]
theorem IsScalarTower.isAlgebraic {F L E: Type*} [CommRing F] [Field L] [Algebra F L] (x : L)
    [Field E] [Algebra F E] [Algebra L E] [IsScalarTower F L E] [Algebra.IsAlgebraic F L]
    [IsSplittingField L E (mapAlg F L (minpoly F x))] : Algebra.IsAlgebraic F E := by
  let _ : FiniteDimensional L E := IsSplittingField.finiteDimensional _ (mapAlg F L (minpoly F x))
  exact Algebra.IsAlgebraic.trans F L E

-- [LocalClassFieldTheory.FromMathlib.SpectralNormUnique]
/-- Given an algebraic tower of fields `E/L/K` and an element `x : L` whose minimal polynomial `f`
  over `K` splits into linear factors over `E`, the `degree(f)`th power of the spectral norm of `x`
  is equal to the product of the `E`-valued roots of `f`. -/
theorem spectralNorm_pow_natDegree_eq_prod_roots (x : L)
  {E : Type*} [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
  (hE : IsSplittingField L E (mapAlg K L (minpoly K x))) [Algebra.IsAlgebraic K E] :
    (spectralMulAlgNorm K E) ((algebraMap L E) x) ^ (minpoly K x).natDegree =
    (spectralMulAlgNorm K E) ((mapAlg K E) (minpoly K x)).roots.prod := by
  have h_deg : (minpoly K x).natDegree = Multiset.card ((mapAlg K E) (minpoly K x)).roots:= by
    have h_deg' : (minpoly K x).natDegree = (mapAlg K E (minpoly K x)).natDegree := by
      rw [mapAlg_eq_map, natDegree_map]
    rw [h_deg', eq_comm, ← splits_iff_card_roots]
    exact IsScalarTower.splits _ hE
  rw [map_multiset_prod, ← Multiset.prod_replicate]
  apply congr_arg
  ext r
  rw [Multiset.count_replicate]
  split_ifs with hr
  · have h : ∀ s : ℝ, s ∈ Multiset.map (spectralMulAlgNorm K E)
        ((mapAlg K E) (minpoly K x)).roots → r = s := by
      intro s hs
      simp only [Multiset.mem_map, mem_roots', ne_eq, IsRoot.def] at hs
      obtain ⟨a, ha_root, has⟩ := hs
      rw [← hr, ← has]
      simp only [spectralMulAlgNorm_def, spectralNorm]
      rw [← minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic ((algebraMap L E) x))]
      rw [← ha_root.2, mapAlg_eq_map, minpoly.algebraMap_eq (algebraMap L E).injective, aeval_def,
        eval_map]
    rw [Multiset.count_eq_card.mpr h, Multiset.card_map]
    exact h_deg
  · rw [Multiset.count_eq_zero_of_notMem]
    intro hr_mem
    simp only [Multiset.mem_map, mem_roots', ne_eq, IsRoot.def] at hr_mem
    obtain ⟨e, he_root, her⟩ := hr_mem
    have heq : (spectralMulAlgNorm K E) e =
      (spectralMulAlgNorm K E) ((algebraMap L E) x) := by
      change spectralNorm K E e = spectralNorm K E (algebraMap L E x)
      simp only [spectralNorm]
      rw [minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic ((algebraMap L E) x))]
      rw [← he_root.2, mapAlg_eq_map, minpoly.algebraMap_eq (algebraMap L E).injective, aeval_def,
        eval_map]
    rw [heq] at her
    exact hr her

-- [LocalClassFieldTheory.FromMathlib.SpectralNormUnique]
/-- For `x : L` with minimal polynomial `f(X) := X^n + a_{n-1}X^{n-1} + ... + a_0` over `K`,
  the spectral norm of `x` is equal to `‖ a_0 ‖^(1/(degree(f(X))))`. -/
theorem spectralNorm_eq_root_zero_coeff [Algebra.IsAlgebraic K L] (x : L) :
    spectralNorm K L x = ‖(minpoly K x).coeff 0‖ ^ (1 / (minpoly K x).natDegree : ℝ) := by
  by_cases hx0 : x = 0
  · simp only [hx0, minpoly.zero, coeff_X_zero, norm_zero, natDegree_X, div_self, ne_eq,
      one_ne_zero, not_false_iff, spectralNorm_zero, Nat.cast_one, div_self, Real.rpow_one]
  · set E := (mapAlg K L (minpoly K x)).SplittingField
    have h_alg_E : Algebra.IsAlgebraic K E := IsScalarTower.isAlgebraic x
    have hspl : Splits (RingHom.id E) (mapAlg K E (minpoly K x)) :=
      IsScalarTower.splits _ (IsSplittingField.splittingField (mapAlg K L (minpoly K x)))
    rw [one_div, Real.eq_rpow_inv (spectralNorm_nonneg x) (norm_nonneg ((minpoly K x).coeff 0)),
      Real.rpow_natCast, @spectralNorm.eq_of_tower K _ E, ←
      @spectralNorm_extends K _ L _ _ ((minpoly K x).coeff 0),
      @spectralNorm.eq_of_tower K _ E _ _ L, ← spectralMulAlgNorm_def,
      ← spectralMulAlgNorm_def, Polynomial.coeff_zero_of_isScalarTower,
      Polynomial.prod_roots_eq_coeff_zero_of_monic_of_splits _ hspl, map_mul, map_pow,
      map_neg_eq_map, map_one, one_pow, one_mul, spectralNorm_pow_natDegree_eq_prod_roots x]
    exact IsSplittingField.splittingField _
    · have h_monic : (minpoly K x).leadingCoeff = 1 := by
        exact minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
      simp only [mapAlg_eq_map, Monic, leadingCoeff, coeff_map, natDegree_map]
      -- merging the `simp only` below with the previous one makes `lean` crash.
      simp only [coeff_natDegree, h_monic, map_one]
    · rw [ne_eq, Nat.cast_eq_zero]
      exact ne_of_gt (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x))

/-
-- Seems unused

theorem spectral_value_term_le [Algebra.IsAlgebraic K L]
    (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) {n : ℕ} (hn : n < (minpoly K x).natDegree) :
    ‖(minpoly K x).coeff n‖ ^ (1 / (((minpoly K x).natDegree : ℝ) - n)) ≤
      ‖(minpoly K x).coeff 0‖ ^ (1 / ((minpoly K x).natDegree : ℝ)) := by
  rw [← spectralNorm_eq_root_zero_coeff hna]
  simp only [spectralNorm, spectralValue, spectralValueTerms]
  apply le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K x)) n
  simp [spectralValueTerms, if_pos hn, one_div, le_refl]
 -/
