/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.WithZero
import LocalClassFieldTheory.DiscreteValuationRing.Basic
import LocalClassFieldTheory.ForMathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.UniformSpace.AbstractCompletion

import LocalClassFieldTheory.ForMathlib.DiscreteUniformity -- Porting note : added
import LocalClassFieldTheory.ForMathlib.Polynomial -- Porting note : added

#align_import laurent_series_equiv_adic_completion

/-! # Isomorphism between Laurent series and the adic completion of rational functions

In this file we construct an isomorphism between the ring of Laurent series with coefficients in a
field and the `X`-adic completion of the field of rational functions. In the process of doing so we
establish a series of results concerning the `X`-adic valuation on rational functions, on power
series and on Laurent series (for instance, relations between the valuation of a power series or a
Laurent series, and the vanishing of certain coefficients). The valuation we consider is the
`ℤₘ₀`-valued, multiplicative valuation associated to `X` as an element of the height-one spectrum.
The additive valuation on the power series, that is related to their order (as term of `part_enat`)
is not used.

Once the preliminaries concerning the `X`-adic valuation on `power_series K` and on
`laurent_series K` are established, the strategy consists in proving that `laurent_series K`, when
endowed with the `X`-adic valuation coming from the DVR `power_series K`,
* is complete; and
* contains `ratfunc K` as a dense subspace
It then follows from the general theory developed in `topology.uniform_space.abstract_completion`
that an isomorphism (as uniform spaces) exists, that it is unique and that it extends to a ring
isomorphism. It is then easy to derive from the above isomorphism an isomorphism between the unit
ball inside the `X`-adic completion and `power_series K` by identifying power series with those
Laurent series that have valuation bounded by `(1 : ℤₘ₀)`.

## Main definitions
* `power_series.ideal_X` is the prime ideal `(X)` of of `power_series K`, as a term of the
`height_one_spectrum`.
* `cauchy.mk_laurent_series` To any Cauchy filter ℱ of `laurent_series K`, we can attach a Laurent
  series that is the limit of the filter. Its `d`-th coefficient is defined as the limit of
  `ℱ.coeff d`, which is again Cauchy but valued in the discrete space `K`, so basically constant.
  That sufficiently negative coefficients vanish follows from `cauchy.coeff_support_bdd`
* `ratfunc_adic_compl_pkg` is the abstract completion of `ratfunc K` whose underlying space
  `ratfunc_adic_compl_pkg.1` is (definitionally) equal to `adic_completion (ratfunc K) (ideal_X K)`.
* `laurent_series_pkg` : once we prove that the Laurent series are complete and contain `ratfunc K`
  densely, they are a completion and therefore give rise to the term
  `laurent_series_pkg K : abstract_completion (ratfunc K)`
* `laurent_series_ring_equiv` This is the main result of the file, and is the ring equivalence
 `(laurent_series K)  ≃+* (ratfunc_adic_compl K)`
* `ratfunc_adic_compl_ring_equiv` This is the inverse of `laurent_series_ring_equiv`, and is the
  ring equivalence `(ratfunc_adic_compl K) ≃+* (laurent_series K)`.
* `power_series_ring_equiv` This is the ring equivalence at integral level, namely
  `(power_series K) ≃+* ((ideal_X K).adic_completion_integers (ratfunc K))` .


## Main results
* `pol_int_valuation_eq_power_series` This is the first of a series of related results comparing the
` X`-adic valuation on `polynomial K` (*resp* on `ratfunc K`) with the `X`-adic valuation on
  `power_series K` (*resp.* `laurent_series K`).
* `valuation_le_iff_coeff_zero_of_lt` This is the first of a series of related results comparing
  the vanishing behaviour of coefficients of polynomials, rational functions, power series and
  Laurent series with their `X`-adic valuation.
* `val_le_one_iff_eq_coe` A Laurent series is the coercion of a power series if and only if its
  valuation is less or equal than 1.
* `uniform_continuous_coeff` This is the main technical result needed to prove that the ring
  `laurent_series K` is complete: it states that for every `d : ℤ`, the coefficient
  `coeff.d : laurent_series K → K` is uniformly continuous. As a consequence, it maps Cauchy
  filters to Cauchy filters.
* `coeff_support_bdd` In order to define a Laurent series we also need to check that for
  sufficiently negative `d : ℤ`, the coefficient vanishes. This provides the proof of the fact.
* `complete_space (laurent_series K)` As a consequence of the above results we can define (see the
  previous section) the function `cauchy.mk_laurent_series` and by proving that the Cauchy filter
  we started with actually converges to the principal filter `𝓟 (cauchy.mk_laurent_series)` we
  accomplish the proof that `laurent_series K` is complete.
* `exists_ratfunc_val_lt` This is the key result to prove that `ratfunc K` is dense inside
  `laurent_series K`: it shows that given arbitrary `f : laurent_series K` and `γ : ℤₘ₀ˣ` there is
  a `Q : ratfunc K` such that `v (f - ↑Q) < γ`.
* `valuation_compare` Starting with a Laurent series, its `power_series.X`-adic valuation coincides
  with the extension of the `polynomial.X`-adic valuation (modulo the isomorphism).


## Implementation details
* To prove `val_le_one_iff_eq_coe` we cannot rely on `alg_map_eq_integers` from
  `discrete_valuation_ring.basic` because there the field `K` needs to be *the* fraction field of the
  DVR instead of a field together with a `[is_fraction_field]` instance (see the Implementation
  details there), and although there is an instance of `discrete_valuation_ring (power_series K)` in
  `for_mathlib.power_series`, the types `laurent_series K` and `fraction_field (power_series K))` do
  not coincide
* The definition of the main isomorphism `laurent_series_ring_equiv` is as the *inverse* of the map
  `ratfunc_adic_compl_ring_equiv K :  (ratfunc_adic_compl K) ≃+* (laurent_series K)`. The reason
  is that the construction is done by first establishing the existence of an equivalence of the two
  uniform spaces `(ratfunc_adic_compl K)` and `(laurent_series K)` (and this is symmetric in the
  two variables), and then showing that the underlying map is actually a ring homomorphism. To prove
  this part, we use that the extension of `coe : ratfunc K →+* laurent_series K` is again a ring
  homomorphism, and this would be more cumbersome in the other direction.
-/


noncomputable section

open Polynomial PowerSeries IsDedekindDomain.HeightOneSpectrum

open scoped DiscreteValuation

variable (K : Type _) [Field K]

--from here `*1`...
-- namespace Polynomial

-- open scoped Classical

-- theorem normUnit_X : normUnit (Polynomial.X : Polynomial K) = 1 := by
--   have := @coe_normUnit K _ _ _ Polynomial.X
--   rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

-- theorem X_eq_normalize : (Polynomial.X : Polynomial K) = normalize Polynomial.X := by
--   simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

-- end Polynomial
---`*1` to here is in PR #11720
namespace PowerSeries
--from here `*2`...
-- theorem normUnit_X : normUnit (PowerSeries.X : PowerSeries K) = 1 := by
--   dsimp only [normUnit];
--   rw [inv_eq_one, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero,
--     divided_by_X_pow_order_of_X_eq_one]

-- theorem X_eq_normalizeX : (PowerSeries.X : PowerSeries K) = normalize PowerSeries.X := by
--   simp only [normalize_apply, PowerSeries.normUnit_X, Units.val_one, mul_one]
---`*2` to here is in PR #13063

--from here `*3`...
/-- The prime ideal `(X)` of `PowerSeries K`, as a term of the `HeightOneSpectrum`. -/
def idealX (K : Type _) [Field K] : IsDedekindDomain.HeightOneSpectrum (PowerSeries K) where
  asIdeal := Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot  := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

open multiplicity UniqueFactorizationMonoid RatFunc Classical

variable {K}

theorem foo {P : K[X]} (hP : P ≠ 0) :
  Multiset.count PowerSeries.X (normalizedFactors (↑P : K⟦X⟧)) =
    Multiset.count Polynomial.X (normalizedFactors P) := by
  apply eq_of_forall_le_iff
  simp only [← PartENat.coe_le_coe]
  rw [X_eq_normalize, PowerSeries.X_eq_normalizeX, ← multiplicity_eq_count_normalizedFactors
    irreducible_X hP, ← multiplicity_eq_count_normalizedFactors X_irreducible (coe_ne_zero hP)]
  simp only [← multiplicity.pow_dvd_iff_le_multiplicity, Polynomial.X_pow_dvd_iff,
    PowerSeries.X_pow_dvd_iff, Polynomial.coeff_coe P, implies_true]


-- **FAE** To golf a bit
theorem pol_intValuation_eq_powerSeries (P : Polynomial K) :
    (Polynomial.idealX K).intValuation P =
      (PowerSeries.idealX K).intValuation (↑P : PowerSeries K) := by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  · simp only [intValuation_apply]
    rw [intValuationDef_if_neg _ hP, intValuationDef_if_neg _ <| coe_ne_zero hP]
    simp only [idealX_span, ofAdd_neg, inv_inj, WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq,
      Nat.cast_inj]
    have span_ne_zero :
      (Ideal.span {P} : Ideal (Polynomial K)) ≠ 0 ∧
        (Ideal.span {Polynomial.X} : Ideal (Polynomial K)) ≠ 0 :=
      by
      simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hP, Polynomial.X_ne_zero,
        not_false_iff, and_self_iff]
    have span_ne_zero' :
      (Ideal.span {↑P} : Ideal (PowerSeries K)) ≠ 0 ∧
        ((PowerSeries.idealX K).asIdeal : Ideal (PowerSeries K)) ≠ 0 := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, coe_eq_zero_iff]
      exact ⟨hP, (PowerSeries.idealX K).3⟩
    have uno := foo hP
    have due := count_associates_factors_eq (Ideal.span {P}) (Ideal.span {Polynomial.X})
      (span_ne_zero).1 ?_ (span_ne_zero).2
    have tre := count_associates_factors_eq (Ideal.span {↑(P : K⟦X⟧)}) (idealX K).asIdeal
      ?_ ?_ ?_
    rw [due, tre]
    convert uno.symm
    · exact count_span_normalizedFactors_eq_of_normUnit hP Polynomial.normUnit_X prime_X
    · refine count_span_normalizedFactors_eq_of_normUnit (coe_ne_zero hP) PowerSeries.normUnit_X
        X_prime
    · exact span_ne_zero'.1
    · exact (idealX K).isPrime
    · exact span_ne_zero'.2
    · exact Ideal.span_singleton_prime Polynomial.X_ne_zero|>.mpr prime_X



theorem intValuation_of_X :
    (PowerSeries.idealX K).intValuation X = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
  classical
  rw [intValuation_apply, intValuationDef_if_neg (PowerSeries.idealX K) PowerSeries.X_ne_zero]
  congr
  have hX : Irreducible (Associates.mk (PowerSeries.idealX K).asIdeal) := by
    rw [Associates.irreducible_mk]
    apply Prime.irreducible
    apply Ideal.prime_of_isPrime
    apply Ideal.span_singleton_eq_bot.mp.mt
    apply PowerSeries.X_ne_zero
    apply PowerSeries.span_X_isPrime
  convert Associates.count_self hX

end PowerSeries
---`*3` to here is in PR #13064
namespace LaurentSeries

section Valuation

open PowerSeries

instance : Valued (LaurentSeries K) ℤₘ₀ :=
  Valued.mk' (PowerSeries.idealX K).valuation

theorem valuation_of_X_zpow (s : ℕ) :
    Valued.v ((↑(PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ s) =
      ↑(Multiplicative.ofAdd (-(s : ℤ))) := by
  have : Valued.v ((PowerSeries.X : PowerSeries K) : LaurentSeries K) =
     (↑(Multiplicative.ofAdd (-(1 : ℤ))) : ℤₘ₀) := by
    erw [@valuation_of_algebraMap (PowerSeries K) _ _ (LaurentSeries K) _ _ _
        (PowerSeries.idealX K) PowerSeries.X]
    apply intValuation_of_X
  rw [map_pow, this, ← one_mul (s : ℤ), ← neg_mul (1 : ℤ) ↑s, Int.ofAdd_mul, WithZero.coe_zpow,
    ofAdd_neg, WithZero.coe_inv, zpow_natCast]

-- Porting note : This lemma has been removed from `Mathlib.RingTheory.LaurentSeries`.
-- lemma coe_powerSeries {R : Type*} [Semiring R] (x : PowerSeries R) : (x : LaurentSeries R) =
--   HahnSeries.ofPowerSeries ℤ R x := rfl

theorem valuation_of_single_zpow (s : ℤ) :
    Valued.v (HahnSeries.single s (1 : K) : LaurentSeries K) =
      ↑(Multiplicative.ofAdd (-(s : ℤ))) := by
  have aux_mul :
    HahnSeries.single s (1 : K) * HahnSeries.single (-s) (1 : K) = (1 : LaurentSeries K) := by
    rw [HahnSeries.single_mul_single, ← sub_eq_add_neg, sub_self, one_mul]
    rfl
  have H : Valued.v (1 : LaurentSeries K) = (1 : ℤₘ₀) := Valued.v.map_one
  rw [← aux_mul, map_mul, mul_eq_one_iff_eq_inv₀] at H
  · rw [H]
    induction' s with s s
    · rw [Int.ofNat_eq_coe, ← HahnSeries.ofPowerSeries_X_pow] at H
      rw [Int.ofNat_eq_coe, ← H, PowerSeries.coe_pow, valuation_of_X_zpow]
    · simp only [Int.negSucc_coe, neg_neg, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
        valuation_of_X_zpow, ofAdd_neg, WithZero.coe_inv, inv_inv]
  · rw [Valuation.ne_zero_iff]
    simp only [ne_eq, one_ne_zero, not_false_iff, HahnSeries.single_ne_zero]

theorem coeff_zero_of_lt_int_valuation {n d : ℕ} {f : PowerSeries K}
    (H : Valued.v (f : LaurentSeries K) ≤ ↑(Multiplicative.ofAdd (-d : ℤ))) :
    n < d → coeff K n f = 0 := by
  intro hnd
  convert (@PowerSeries.X_pow_dvd_iff K _ d f).mp _ n hnd
  have := @valuation_of_algebraMap (PowerSeries K) _ _ (LaurentSeries K) _ _ _
    (PowerSeries.idealX K) f
  erw [this] at H
  have dvd_val_int :=
    (@int_valuation_le_pow_iff_dvd (PowerSeries K) _ _ (PowerSeries.idealX K) f d).mp H
  rw [← span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow]
  apply dvd_val_int

theorem int_valuation_le_iff_coeff_zero_of_lt {d : ℕ} (f : PowerSeries K) :
    Valued.v (f : LaurentSeries K) ≤ ↑(Multiplicative.ofAdd (-d : ℤ)) ↔
      ∀ n : ℕ, n < d → coeff K n f = 0 := by
  have : PowerSeries.X ^ d ∣ f ↔ ∀ n : ℕ, n < d → (PowerSeries.coeff K n) f = 0 :=
    ⟨fun hd n hnd => PowerSeries.X_pow_dvd_iff.mp hd n hnd, fun H =>
      PowerSeries.X_pow_dvd_iff.mpr H⟩
  erw [← this, valuation_of_algebraMap (PowerSeries.idealX K) f, ←
    span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow]
  apply int_valuation_le_pow_iff_dvd

theorem coeff_zero_of_lt_valuation {n D : ℤ} {f : LaurentSeries K}
    (H : Valued.v f ≤ ↑(Multiplicative.ofAdd (-D))) : n < D → f.coeff n = 0 := by
  intro hnd
  by_cases h_n_ord : n < f.order
  · exact HahnSeries.coeff_eq_zero_of_lt_order h_n_ord
  · rw [not_lt] at h_n_ord
    set F := powerSeriesPart f with hF
    by_cases ord_nonpos : f.order ≤ 0
    · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
      rw [hs] at h_n_ord
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp h_n_ord)
      have hD : 0 ≤ D + s := by linarith
      obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hD
      have F_coeff := powerSeriesPart_coeff f m
      rw [hs, add_comm, ← eq_add_neg_of_add_eq hm, ← hF] at F_coeff
      rw [← F_coeff]
      refine' (@int_valuation_le_iff_coeff_zero_of_lt K _ d F).mp _ m (by linarith)
      have F_mul := ofPowerSeries_powerSeriesPart f
      rw [← hF, hs, neg_neg, ← HahnSeries.ofPowerSeries_X_pow s] at F_mul
      rwa [F_mul, map_mul, ← hd, PowerSeries.coe_pow, neg_add_rev, ofAdd_add, WithZero.coe_mul,
        valuation_of_X_zpow K s, mul_le_mul_left₀]
      simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff]
    · rw [not_le] at ord_nonpos
      obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos))
      rw [neg_inj] at hs
      rw [hs, ← sub_nonneg] at h_n_ord
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h_n_ord
      rw [sub_eq_iff_eq_add] at hm
      have hD : 0 ≤ D - s := by linarith
      obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hD
      have F_coeff := powerSeriesPart_coeff f m
      rw [hs, add_comm, ← hF, ← hm] at F_coeff
      rw [← F_coeff]
      refine' (@int_valuation_le_iff_coeff_zero_of_lt K _ d F).mp _ m (by linarith)
      have F_mul := ofPowerSeries_powerSeriesPart f
      rw [← hF] at F_mul
      rwa [F_mul, map_mul, ← hd, hs, neg_sub, sub_eq_add_neg, ofAdd_add, valuation_of_single_zpow,
        neg_neg, WithZero.coe_mul, mul_le_mul_left₀]
      simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff]

theorem valuation_le_iff_coeff_zero_of_lt {D : ℤ} {f : LaurentSeries K} :
    Valued.v f ≤ ↑(Multiplicative.ofAdd (-D : ℤ)) ↔ ∀ n : ℤ, n < D → f.coeff n = 0 := by
  refine' ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => _⟩
  set F := powerSeriesPart f with hF
  by_cases ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    have h_F_mul := f.single_order_mul_powerSeriesPart
    rw [hs, ← hF] at h_F_mul
    rw [← h_F_mul, map_mul, valuation_of_single_zpow, neg_neg, mul_comm, ← le_mul_inv_iff₀,
      ofAdd_neg, WithZero.coe_inv, ← mul_inv, ← WithZero.coe_mul, ← ofAdd_add, ← WithZero.coe_inv, ←
      ofAdd_neg]
    by_cases hDs : D + s ≤ 0
    · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
      rwa [← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, Multiplicative.ofAdd_le,
        Left.nonneg_neg_iff]
    · rw [not_le] at hDs
      obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hDs)
      rw [hd]
      apply (int_valuation_le_iff_coeff_zero_of_lt K F).mpr
      intro n hn
      rw [powerSeriesPart_coeff f n, hs]
      apply h_val_f
      linarith
    simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff]
  · rw [not_le] at ord_nonpos
    obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos))
    rw [neg_inj] at hs
    have h_F_mul := f.single_order_mul_powerSeriesPart
    rw [hs, ← hF] at h_F_mul
    rw [← h_F_mul, map_mul, valuation_of_single_zpow, mul_comm, ← le_mul_inv_iff₀, ofAdd_neg,
      WithZero.coe_inv, ← mul_inv, ← WithZero.coe_mul, ← ofAdd_add, ← WithZero.coe_inv, ← ofAdd_neg,
      neg_add, neg_neg]
    by_cases hDs : D - s ≤ 0
    · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
      rw [← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
      linarith
    · rw [not_le] at hDs
      obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hDs)
      rw [← neg_neg (-D + ↑s)]
      rw [← sub_eq_neg_add]
      rw [neg_sub]
      rw [hd]
      apply (int_valuation_le_iff_coeff_zero_of_lt K F).mpr
      intro n hn
      rw [powerSeriesPart_coeff f n, hs]
      apply h_val_f (s + n)
      linarith
    simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff]

theorem valuation_le_of_coeff_eventually_eq {f g : LaurentSeries K} {D : ℤ}
    (H : ∀ d, d < D → g.coeff d = f.coeff d) : Valued.v (f - g) ≤ ↑(Multiplicative.ofAdd (-D)) := by
  apply (valuation_le_iff_coeff_zero_of_lt K).mpr
  intro n hn
  rw [HahnSeries.sub_coeff, sub_eq_zero]
  exact (H n hn).symm

theorem eq_coeff_of_valuation_sub_lt {d n : ℤ} {f g : LaurentSeries K}
    (H : Valued.v (g - f) ≤ ↑(Multiplicative.ofAdd (-d))) : n < d → g.coeff n = f.coeff n := by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    erw [← HahnSeries.sub_coeff]
    apply coeff_zero_of_lt_valuation K H hn

theorem bounded_supp_of_valuation_le (f : LaurentSeries K) (d : ℤ) :
    ∃ N : ℤ,
      ∀ g : LaurentSeries K,
        Valued.v (g - f) ≤ ↑(Multiplicative.ofAdd (-d)) → ∀ n < N, g.coeff n = 0 := by
  by_cases hf : f = 0
  · refine' ⟨d, fun _ hg _ hn => _⟩
    simpa only [eq_coeff_of_valuation_sub_lt K hg hn, hf] using HahnSeries.zero_coeff
  · refine' ⟨min (f.2.isWF.min (HahnSeries.support_nonempty_iff.mpr hf)) d - 1, fun _ hg n hn => _⟩
    have hn' : f.coeff n = 0 := Function.nmem_support.mp fun h =>
      Set.IsWF.not_lt_min f.2.isWF (HahnSeries.support_nonempty_iff.mpr hf) h
        (lt_trans hn (Int.sub_one_lt_iff.mpr (Int.min_le_left _ _)))
    rwa [eq_coeff_of_valuation_sub_lt K hg _]
    · exact lt_trans hn (Int.lt_of_le_sub_one <| (sub_le_sub_iff_right _).mpr (min_le_right _ d))

theorem val_le_one_iff_eq_coe (f : LaurentSeries K) :
    Valued.v f ≤ (1 : ℤₘ₀) ↔ ∃ F : PowerSeries K, ↑F = f := by
  rw [← WithZero.coe_one, ← ofAdd_zero, ← neg_zero, valuation_le_iff_coeff_zero_of_lt]
  refine' ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, _⟩, _⟩
  ext (_ | n)
  · simp only [Int.ofNat_eq_coe, LaurentSeries.coeff_coe_powerSeries, coeff_mk]
  simp only [h (Int.negSucc n) (Int.negSucc_lt_zero n)]
  swap
  rintro ⟨F, rfl⟩ _ _
  all_goals
    apply HahnSeries.embDomain_notin_range
    simp only [Nat.coe_castAddMonoidHom, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.mem_range, not_exists, Int.negSucc_lt_zero]
    intro
  linarith
  simp only [not_false_eq_true]

end Valuation

end LaurentSeries

section CompletionLaurentSeries

open LaurentSeries Polynomial
section Complete

open Filter TopologicalSpace

open scoped Filter BigOperators Topology

theorem uniformContinuous_coeff {uK : UniformSpace K} (h : uniformity K = 𝓟 idRel) (d : ℤ) :
    UniformContinuous fun f : LaurentSeries K => f.coeff d := by
  refine' uniformContinuous_iff_eventually.mpr fun S hS => eventually_iff_exists_mem.mpr _
  let γ : ℤₘ₀ˣ := Units.mk0 (↑(Multiplicative.ofAdd (-(d + 1)))) WithZero.coe_ne_zero
  use{P | Valued.v (P.snd - P.fst) < ↑γ}
  refine' ⟨(Valued.hasBasis_uniformity (LaurentSeries K) ℤₘ₀).mem_of_mem (by tauto), fun P hP => _⟩
  rw [h] at hS
  apply hS
  rw [eq_coeff_of_valuation_sub_lt K (le_of_lt hP) (lt_add_one _), mem_idRel]

variable {K}

/-- Having proved that taking the coefficients (regarded as maps) are uniformly continuous, every
Cauchy filter in `laurent_series K` gives rise to a Cauchy filter in `K` for every `d : ℤ`, and
such Cauchy filter in `K` converges to a principal filter -/
def Cauchy.coeff {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) : ℤ → K := by
  letI : UniformSpace K := ⊥
  have hK : @uniformity K ⊥ = Filter.principal idRel := rfl
  use fun d => cauchy_discrete_is_constant hK (hℱ.map (uniformContinuous_coeff K hK d))

theorem Cauchy.coeff_tendso {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) (D : ℤ) :
    Tendsto (fun f : LaurentSeries K => f.coeff D) ℱ (𝓟 {Cauchy.coeff hℱ D}) := by
  letI : UniformSpace K := ⊥
  have hK : uniformity K = Filter.principal idRel := rfl
  exact cauchy_discrete_le hK (hℱ.map (uniformContinuous_coeff K hK D))

/- Porting note : error "don't know how to synthesize placeholder for argument 'hi'", which
  only shows up when the proof is apparently complete -/
theorem Cauchy.exists_lb_eventual_support {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ᶠ f : LaurentSeries K in ℱ, ∀ n < N, f.coeff n = (0 : K) := by
  let entourage : Set (LaurentSeries K × LaurentSeries K) :=
    {P : LaurentSeries K × LaurentSeries K |
      Valued.v (P.snd - P.fst) < ((Multiplicative.ofAdd 0 : Multiplicative ℤ) : ℤₘ₀)}
  let a : Multiplicative ℤ := Multiplicative.ofAdd 0
  let b := @WithZero.coe_ne_zero (Multiplicative ℤ) a
  let ζ := Units.mk0 (G₀ := ℤₘ₀) _ b
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ :=
    mem_prod_iff.mp
      (Filter.le_def.mp hℱ.2 entourage
        (@HasBasis.mem_of_mem _ _ _ _ _ ζ (Valued.hasBasis_uniformity (LaurentSeries K) ℤₘ₀)
          (by tauto)))
  obtain ⟨f, hf⟩ := forall_mem_nonempty_iff_neBot.mpr hℱ.1 (S ∩ T) (inter_mem_iff.mpr ⟨hS, hT⟩)
  obtain ⟨N, hN⟩ := bounded_supp_of_valuation_le K f 0
  use N
  apply mem_of_superset (inter_mem hS hT)
  suffices (S ∩ T) ×ˢ (S ∩ T) ⊆ entourage by
    intro g hg
    have h_prod : (f, g) ∈ entourage := by
      refine' this (Set.mem_prod.mpr _)
      exact ⟨hf, hg⟩
    exact fun _ hn => hN g (le_of_lt h_prod) _ hn
  exact (Set.prod_mono (Set.inter_subset_left (s :=S) (t := T))
    (Set.inter_subset_right (s :=S) (t := T))).trans H

theorem Cauchy.exists_lb_gt_principal {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ n < N, (ℱ.map fun f : LaurentSeries K => f.coeff n) ≤ Filter.principal {0} := by
  simp only [principal_singleton, pure_zero, nonpos_iff, mem_map]
  obtain ⟨N, hN⟩ := Cauchy.exists_lb_eventual_support hℱ -- Porting note: dot notation doesn't work
  exact ⟨N, fun n hn =>  Filter.mem_of_superset hN (fun a ha => ha n hn)⟩

theorem Cauchy.exists_lb_support {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ n, n < N → coeff hℱ n = 0 := by -- Porting note: dot notation doesn't work
  letI : UniformSpace K := ⊥
  have hK : uniformity K = Filter.principal idRel := rfl
  obtain ⟨N, hN⟩ := exists_lb_gt_principal hℱ -- Porting note: dot notation doesn't work
  exact ⟨N, fun n hn => neBot_unique_principal hK (hℱ.map (uniformContinuous_coeff K hK n)).1
    (coeff_tendso _ _) (hN n hn)⟩

/- Porting note: dot notation doesn't work for the `Cauchy` hypothesis `hℱ`. -/

/- The following lemma shows that for every `d` smaller than the minimum between the integers
produced in `cauchy.exists_lb_eventual_support` and `cauchy.exists_lb_support`, for almost all
series in `ℱ` the `d`th coefficient coincides with the `d`th coefficient of `coeff hℱ`. -/
theorem Cauchy.exists_lb_coeff_ne {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ᶠ f : LaurentSeries K in ℱ, ∀ d < N, coeff hℱ d = f.coeff d := by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := exists_lb_eventual_support hℱ, exists_lb_support hℱ
  refine' ⟨min N₁ N₂, ℱ.3 hN₁ fun _ hf d hd => _⟩
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _)), hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))]

theorem Cauchy.coeff_support_bdd {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) :
    BddBelow (coeff hℱ).support := by
  refine' ⟨(exists_lb_support hℱ).choose, fun d hd => _⟩
  by_contra hNd
  exact hd ((exists_lb_support hℱ).choose_spec d (not_le.mp hNd))

/-- To any Cauchy filter ℱ of `laurent_series K`, we can attach a laurent series that is the limit
of the filter. Its `d`-th coefficient is defined as the limit of `ℱ.coeff d`, which is again Cauchy
but valued in the discrete space `K`. That sufficiently negative coefficients vanish follows from
`cauchy.coeff_support_bdd` -/
def Cauchy.mk_LaurentSeries {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) : LaurentSeries K :=
  HahnSeries.mk (fun d => coeff hℱ d) (Set.IsWF.isPWO (coeff_support_bdd hℱ).wellFoundedOn_lt)

set_option pp.proofs true

theorem Cauchy.coeff_eventually_equal {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) :
    ∀ D : ℤ, ∀ᶠ f : LaurentSeries K in ℱ, ∀ d, d < D → (coeff hℱ) d = f.coeff d := by
  intro D
  set X : ℤ → Set (LaurentSeries K) := fun d => {f | (coeff hℱ) d = f.coeff d} with hX
  have intersec :
    (⋂ n ∈ Set.Iio D, X n) ⊆ {x : LaurentSeries K | ∀ d : ℤ, d < D → (coeff hℱ) d = x.coeff d} :=
    by
    rintro (_ hf n hn)
    simp only [Set.mem_iInter, Set.mem_setOf_eq, hX] at hf
    exact hf n hn
  set N := min (exists_lb_coeff_ne hℱ).choose D with hN₀
  suffices (⋂ n ∈ Set.Iio D, X n) ∈ ℱ by
    exact ℱ.3 this intersec
  by_cases H : D < (exists_lb_coeff_ne hℱ).choose
  · apply ℱ.3 (exists_lb_coeff_ne hℱ).choose_spec
    simp only [Set.mem_Iio, Set.subset_iInter₂_iff, Set.setOf_subset_setOf]
    intro m hm f hd
    exact hd _ (lt_trans hm H)
  · rw [← Set.Iio_union_Ico_eq_Iio (le_of_not_gt H)]
    rw [Set.biInter_union]
    simp only [Set.mem_Iio, Set.mem_Ico, inter_mem_iff]
    constructor
    · convert (exists_lb_coeff_ne hℱ).choose_spec using 1
      ext f
      simp only [Set.mem_Iio, Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    · have : ⋂ x, ⋂ (_ : (exists_lb_coeff_ne hℱ).choose ≤ x ∧ x < D), X x =
        (⋂ (n : ℤ) (_ : n ∈ Set.Ico N D), X n) := by
        simp only [Set.mem_Ico]
        apply Set.iInter_congr
        intro
        refine Set.iInter_congr_Prop ?h.pq (congrFun rfl)
        omega
      rw [this, biInter_mem (Set.finite_Ico N D)]
      intro d _
      apply coeff_tendso hℱ
      simp only [principal_singleton, mem_pure]
      rfl

theorem Cauchy.eventually_mem_nhds {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ)
    {U : Set (LaurentSeries K)} (hU : U ∈ 𝓝 (mk_LaurentSeries hℱ)) : ∀ᶠ f in ℱ, f ∈ U := by
  letI : Ring (LaurentSeries K) := inferInstance -- Porting note : I had to add this
  obtain ⟨γ, hU₁⟩ := Valued.mem_nhds.mp hU
  suffices ∀ᶠ f in ℱ, f ∈ {y : LaurentSeries K | Valued.v (y - (mk_LaurentSeries hℱ)) < ↑γ} by
    apply this.mono fun _ hf => hU₁ hf
  · set D := -(Multiplicative.toAdd (WithZero.unzero γ.ne_zero) - 1) with hD₀
    have hD : ((Multiplicative.ofAdd (-D) : Multiplicative ℤ) : ℤₘ₀) < γ := by
      rw [← WithZero.coe_unzero γ.ne_zero, WithZero.coe_lt_coe, hD₀, neg_neg, ofAdd_sub,
        ofAdd_toAdd, div_lt_comm, div_self', ← ofAdd_zero, Multiplicative.ofAdd_lt]
      exact zero_lt_one
    apply (coeff_eventually_equal  hℱ D).mono
    intro f hf
    apply lt_of_le_of_lt (valuation_le_of_coeff_eventually_eq _ _) hD
    apply hf

instance : CompleteSpace (LaurentSeries K) :=
  ⟨fun hℱ => ⟨Cauchy.mk_LaurentSeries hℱ, fun _ hS => Cauchy.eventually_mem_nhds hℱ hS⟩⟩

end Complete

section Dense

open HahnSeries

theorem exists_pol_int_val_lt (F : PowerSeries K) (η : ℤₘ₀ˣ) :
    ∃ P : Polynomial K, (PowerSeries.idealX K).intValuation (F - P) < η := by
  by_cases h_neg' : 1 < η
  · use 0
    rw [Polynomial.coe_zero, sub_zero]
    apply lt_of_le_of_lt (int_valuation_le_one (PowerSeries.idealX K) F)
    rwa [← Units.val_one, Units.val_lt_val]
  · set D := Multiplicative.toAdd (WithZero.unzero η.ne_zero) with hD
    rw [not_lt, ← Units.val_le_val, Units.val_one, ← WithZero.coe_one, ←
      WithZero.coe_unzero η.ne_zero, WithZero.coe_le_coe, ← Multiplicative.toAdd_le, ← hD,
      toAdd_one] at h_neg'
    obtain ⟨d, hd⟩ := Int.exists_eq_neg_ofNat h_neg'
    use F.trunc (d + 1)
    have trunc_prop : ∀ m : ℕ, m < d + 1 → PowerSeries.coeff K m (F - ↑(F.trunc (d + 1))) = 0 :=
      by
      intro m hm
      rw [map_sub, sub_eq_zero, Polynomial.coeff_coe, coeff_trunc, if_pos hm]
    have := (LaurentSeries.int_valuation_le_iff_coeff_zero_of_lt K _).mpr trunc_prop
    rw [Nat.cast_add, neg_add, ofAdd_add, ← hd, hD, ofAdd_toAdd, WithZero.coe_mul,
      WithZero.coe_unzero, ← LaurentSeries.coe_algebraMap] at this
    rw [← @valuation_of_algebraMap (PowerSeries K) _ _ (LaurentSeries K) _ _ _
      (PowerSeries.idealX K) (F - ↑(F.trunc (d + 1)))]
    apply lt_of_le_of_lt this
    rw [← mul_one (η : ℤₘ₀), mul_assoc, one_mul]
    apply WithZero.lt_hMul_left₀ _ η.ne_zero
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ofAdd_neg, Right.inv_lt_one_iff, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    apply Int.zero_lt_one

theorem exists_ratFunc_val_lt (f : LaurentSeries K) (γ : ℤₘ₀ˣ) :
    ∃ Q : RatFunc K, Valued.v (f - Q) < γ := by
  set F := f.powerSeriesPart with hF
  by_cases ord_nonpos : f.order < 0
  · have h₀ : ((Multiplicative.ofAdd f.order : Multiplicative ℤ) : ℤₘ₀) ≠ 0 := WithZero.coe_ne_zero
    set η : ℤₘ₀ˣ := Units.mk0 (Multiplicative.ofAdd f.order : Multiplicative ℤ) h₀ with hη
    obtain ⟨P, hP⟩ := exists_pol_int_val_lt K F (η * γ)
    use RatFunc.X ^ f.order * (P : RatFunc K)
    have F_mul := f.ofPowerSeries_powerSeriesPart
    obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (le_of_lt ord_nonpos)
    rw [← hF, hs, neg_neg, ← HahnSeries.ofPowerSeries_X_pow s, ← inv_mul_eq_iff_eq_mul₀] at F_mul
    erw [hs, ← F_mul, PowerSeries.coe_pow, PowerSeries.coe_X, RatFunc.coe_mul, zpow_neg, zpow_ofNat,
      inv_eq_one_div (RatFunc.X ^ s), RatFunc.coe_div, RatFunc.coe_pow, RatFunc.coe_X,
      RatFunc.coe_one, ← inv_eq_one_div, ← mul_sub, map_mul, map_inv₀, ← PowerSeries.coe_X,
      valuation_of_X_zpow, ← hs, ← RatFunc.coe_coe, ← coe_sub, ← LaurentSeries.coe_algebraMap,
        valuation_of_algebraMap, ← Units.val_mk0 h₀, ← hη]
    apply inv_mul_lt_of_lt_mul₀
    rwa [← Units.val_mul]
    · simp only [PowerSeries.coe_pow, pow_ne_zero, PowerSeries.coe_X, ne_eq,
        HahnSeries.single_eq_zero_iff, one_ne_zero, not_false_iff]
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (not_lt.mp ord_nonpos))
    simp only [neg_inj] at hs
    have hf_coe : (PowerSeries.X ^ s * F : PowerSeries K) = f := by
      rw [← f.single_order_mul_powerSeriesPart, hs, hF, PowerSeries.coe_mul, PowerSeries.coe_pow,
        PowerSeries.coe_X, single_pow, nsmul_eq_mul, mul_one, one_pow]
    rw [← hf_coe]
    obtain ⟨P, hP⟩ := exists_pol_int_val_lt K (PowerSeries.X ^ s * F) γ
    use ↑P
    erw [← RatFunc.coe_coe, ← coe_sub, ← LaurentSeries.coe_algebraMap, valuation_of_algebraMap]
    exact hP

theorem coe_range_dense : DenseRange (Coe.coe : RatFunc K → LaurentSeries K) := by
  letI : Ring (LaurentSeries K) := inferInstance
  rw [denseRange_iff_closure_range]
  ext f
  simp only [UniformSpace.mem_closure_iff_symm_ball, Set.mem_univ, iff_true_iff, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_range, Set.mem_setOf_eq, exists_exists_eq_and]
  intro V hV h_symm
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV
  obtain ⟨T, hT₀, hT₁⟩ := hV
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hT₀
  obtain ⟨P, hP⟩ := exists_ratFunc_val_lt K f γ
  use P
  apply hT₁
  apply hγ
  simpa only [add_comm, ← sub_eq_add_neg, gt_iff_lt, Set.mem_setOf_eq]

end Dense

section Comparison

open RatFunc
namespace RatFunc

theorem mk_eq_mk' (f : Polynomial K) (g : Polynomial K) (hg : g ≠ 0) :
    RatFunc.mk f g = IsLocalization.mk' (RatFunc K) f ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 hg⟩ :=
  by simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

theorem mk_val (f : Polynomial K) (g : Polynomial K) (hg : g ≠ 0) :
    (Polynomial.idealX K).valuation (RatFunc.mk f g) =
      (Polynomial.idealX K).intValuation f / (Polynomial.idealX K).intValuation g :=
  by simp only [RatFunc.mk_eq_mk' _ _ _ hg, valuation_of_mk']

theorem valuation_eq_LaurentSeries_valuation (P : RatFunc K) :
    (Polynomial.idealX K).valuation P = (PowerSeries.idealX K).valuation (↑P : LaurentSeries K) := by
  refine' RatFunc.induction_on' P _
  intro f g h
  convert RatFunc.mk_val K f g h
  rw [RatFunc.mk_eq_mk' K f g h]
  have aux :
    (↑(IsLocalization.mk' (RatFunc K) f ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 h⟩) :
        LaurentSeries K) =
      (IsLocalization.mk' (LaurentSeries K) (↑f : PowerSeries K)
          ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 <| coe_ne_zero h⟩ :
        LaurentSeries K) := by
    simp only [IsFractionRing.mk'_eq_div, coe_div]
    congr
    exacts [(RatFunc.coe_coe f).symm, (RatFunc.coe_coe g).symm]
  rw [aux]
  convert @valuation_of_mk' (PowerSeries K) _ _ (LaurentSeries K) _ _ _ (PowerSeries.idealX K) f
        ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 <| coe_ne_zero h⟩ <;>
    apply PowerSeries.pol_intValuation_eq_powerSeries


end RatFunc

theorem inducing_coe : UniformInducing (Coe.coe : RatFunc K → LaurentSeries K) := by
  letI : Ring (LaurentSeries K) := inferInstance -- Porting note: I had to add this
  rw [uniformInducing_iff, Filter.comap]
  ext S
  simp only [exists_prop, Filter.mem_mk, Set.mem_setOf_eq, uniformity_eq_comap_nhds_zero,
    Filter.mem_comap]
  constructor
  · rintro ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hR
    use {P : RatFunc K | Valued.v P < ↑d}
    · simp only [Valued.mem_nhds, sub_zero]
      constructor
      · use d
      · refine' subset_trans _ pre_T
        rintro _ _
        apply pre_R
        apply hd
        simp only [sub_zero, Set.mem_setOf_eq]
        erw [← RatFunc.coe_sub, ← RatFunc.valuation_eq_LaurentSeries_valuation]
        assumption
  · rintro ⟨T, ⟨hT, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hT
    let X := {f : LaurentSeries K | Valued.v f < ↑d}
    refine ⟨(fun x : LaurentSeries K × LaurentSeries K => x.snd - x.fst) ⁻¹' X, ⟨X, ?_⟩, ?_⟩
    · refine ⟨?_, Set.Subset.refl _⟩
      · simp only [Valued.mem_nhds, sub_zero]
        use d
    · refine subset_trans (fun _ _ => ?_) pre_T
      apply hd
      erw [Set.mem_setOf_eq, sub_zero, RatFunc.valuation_eq_LaurentSeries_valuation,
        RatFunc.coe_sub]
      assumption

theorem continuous_coe : Continuous (Coe.coe : RatFunc K → LaurentSeries K) :=
  (uniformInducing_iff'.1 (inducing_coe K)).1.continuous

/-- The `X`-adic completion as an abstract completion of `ratfunc K`-/
noncomputable def ratfuncAdicComplPkg : AbstractCompletion (RatFunc K) :=
  UniformSpace.Completion.cPkg

/-- Having established that the `laurent_series K` is complete and contains `ratfunc K` as a dense
subspace, it gives rise to an abstract completion of `ratfunc K`.-/
noncomputable def LaurentSeriesPkg : AbstractCompletion (RatFunc K)
    where
  space := LaurentSeries K
  coe := Coe.coe
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  uniformInducing := inducing_coe K
  dense := coe_range_dense K

instance : TopologicalSpace (LaurentSeriesPkg K).space :=
  (LaurentSeriesPkg K).uniformStruct.toTopologicalSpace

@[simp]
theorem LaurentSeries_coe (x : RatFunc K) : (LaurentSeriesPkg K).coe x = (↑x : LaurentSeries K) :=
  rfl

open AbstractCompletion

/-- Reintrerpret the extension of `coe : ratfunc K →+* laurent_series K` to the completion, as a
ring homomorphism -/
-- @[reducible]
noncomputable def extensionAsRingHom :=
  UniformSpace.Completion.extensionHom (coeAlgHom K).toRingHom


/-- An abbreviation for the `X`-adic completion of `ratfunc K` -/
@[reducible]
def RatFuncAdicCompl := adicCompletion (RatFunc K) (Polynomial.idealX K)

/-The two instances below make `comparePkg` and `comparePkg_eq_extension` slightly faster-/

instance : UniformSpace (RatFuncAdicCompl K) := inferInstance

instance : UniformSpace (LaurentSeries K) := inferInstance

/-- The uniform space isomorphism between two abstract completions of `ratfunc K` -/
@[reducible]
def comparePkg : RatFuncAdicCompl K ≃ᵤ LaurentSeries K :=
  compareEquiv (ratfuncAdicComplPkg K) (LaurentSeriesPkg K)

lemma comparePkg_eq_extension (x : UniformSpace.Completion (RatFunc K)) :
    (comparePkg K).toFun x = (extensionAsRingHom K (continuous_coe K)).toFun x := rfl

/-- The uniform space equivalence between two abstract completions of `ratfunc K` as a ring
equivalence: this will be the *inverse* of the fundamental one.-/
@[reducible]
def ratfuncAdicComplRingEquiv : RatFuncAdicCompl K ≃+* LaurentSeries K :=
  {comparePkg K with
    map_mul' := by
      unfold RatFuncAdicCompl
      unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion
      intro x y
      rw [comparePkg_eq_extension, (extensionAsRingHom K (continuous_coe K)).map_mul']
      rfl
    map_add' := by
      unfold RatFuncAdicCompl
      unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion
      intro x y
      rw [comparePkg_eq_extension, (extensionAsRingHom K (continuous_coe K)).map_add']
      rfl }

-- **NEW**
/-- The uniform space equivalence between two abstract completions of `ratfunc K` as a ring
equivalence: it goes from `laurent_series K` to `ratfunc_adic_compl K` -/
@[reducible]
def LaurentSeriesRingEquiv : LaurentSeries K ≃+* RatFuncAdicCompl K :=
  (ratfuncAdicComplRingEquiv K).symm

-- Porting note: times out
/- theorem LaurentSeriesRingEquiv_apply (x : LaurentSeries K) :
    (LaurentSeriesRingEquiv K) x = compareEquiv (LaurentSeriesPkg K) (ratfuncAdicComplPkg K) x := by
  simpa only [RingEquiv.apply_symm_apply]  -/

theorem ratfuncAdicComplRingEquiv_apply (x : RatFuncAdicCompl K) :
    ratfuncAdicComplRingEquiv K x = (ratfuncAdicComplPkg K).compare (LaurentSeriesPkg K) x :=
  rfl

theorem coe_X_compare :
    (ratfuncAdicComplRingEquiv K) (↑(@RatFunc.X K _ _) : RatFuncAdicCompl K) =
      (↑(@PowerSeries.X K _) : LaurentSeries K) := by
  rw [PowerSeries.coe_X, ← RatFunc.coe_X, ← LaurentSeries_coe, ← AbstractCompletion.compare_coe]
  rfl

open Filter AbstractCompletion

open scoped WithZeroTopology Topology

theorem valuation_LaurentSeries_equal_extension :
    (LaurentSeriesPkg K).denseInducing.extend Valued.v = @Valued.v (LaurentSeries K) _ ℤₘ₀ _ _ := by
  apply DenseInducing.extend_unique
  · intro x
    erw [valuation_eq_LaurentSeries_valuation K x]
    rfl
  · exact @Valued.continuous_valuation (LaurentSeries K) _ ℤₘ₀ _ _

theorem tendsto_valuation (a : (Polynomial.idealX K).adicCompletion (RatFunc K)) :
    Tendsto (@Valued.v (RatFunc K) _ ℤₘ₀ _ _) (comap Coe.coe (𝓝 a)) (𝓝 (Valued.v a : ℤₘ₀)) := by
  set ψ := @Valued.v (RatFunc K) _ ℤₘ₀ _ _ with hψ
  let this := @Valued.is_topological_valuation
    ((Polynomial.idealX K).adicCompletion (RatFunc K)) _ ℤₘ₀ _ _
  by_cases ha : a = 0
  · rw [tendsto_def]
    intro S hS
    simp only [mem_comap, exists_prop]
    rw [ha, map_zero, WithZeroTopology.hasBasis_nhds_zero.1 S] at hS
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS
    use{t | Valued.v t < γ}
    constructor
    · rw [ha, this]
      use Units.mk0 γ γ_ne_zero
      rw [Units.val_mk0]
    · refine Set.Subset.trans (fun a _ ↦ ?_) (Set.preimage_mono γ_le)
      rwa [Set.mem_preimage, Set.mem_Iio, ← Valued.valuedCompletion_apply a]
  · rw [WithZeroTopology.tendsto_of_ne_zero ((Valuation.ne_zero_iff Valued.v).mpr ha), hψ,
      Filter.eventually_comap, Filter.Eventually, Valued.mem_nhds]
    simp only [Set.setOf_subset_setOf]
    set γ := Valued.v a / (↑(Multiplicative.ofAdd (1 : ℤ)) : ℤₘ₀) with h_aγ
    have γ_ne_zero : γ ≠ 0 := by
      rw [ne_eq, _root_.div_eq_zero_iff, Valuation.zero_iff]
      simpa only [WithZero.coe_ne_zero, or_false]
    use Units.mk0 γ γ_ne_zero
    intro y val_y b diff_b_y
    replace val_y : Valued.v y = Valued.v a := by
      refine' Valuation.map_eq_of_sub_lt _ (val_y.trans _)
      rw [Units.val_mk0, h_aγ, ← WithZero.coe_unzero ((Valuation.ne_zero_iff Valued.v).mpr ha), ←
        WithZero.coe_div, WithZero.coe_lt_coe, div_lt_self_iff, ← ofAdd_zero,
        Multiplicative.ofAdd_lt]
      exact Int.zero_lt_one
    rw [← Valued.extension_extends, ← val_y, ← diff_b_y]
    congr

theorem valuation_compare (f : LaurentSeries K) :
    (@Valued.v (RatFuncAdicCompl K) _ ℤₘ₀ _ _)
        (AbstractCompletion.compare (LaurentSeriesPkg K) (ratfuncAdicComplPkg K) f) =
      Valued.v f := by
  simp only [← valuation_LaurentSeries_equal_extension, ←
    extend_compare_extend (ratfuncAdicComplPkg K) (LaurentSeriesPkg K)
      (@Valued.v (RatFunc K) _ ℤₘ₀ _ _) Valued.continuous_valuation (tendsto_valuation K)]
  rfl

section PowerSeries

/-- In order to compare `PowerSeries K` with the valuation subring in the `X`-adic completion of
`RatFunc K` we regard it as a subring of `LaurentSeries K`. -/
@[reducible]
def powerSeries_as_subring : Subring (LaurentSeries K) :=
  RingHom.range (HahnSeries.ofPowerSeries ℤ K)

/-- The ring `power_series K` is isomorphic to the subring `power series_as_subring K` -/
@[reducible]
def powerSeriesEquivSubring : PowerSeries K ≃+* powerSeries_as_subring K := by
  rw [powerSeries_as_subring, RingHom.range_eq_map]
  -- Porting note: Lean 4 is no longer able to synthetize the `Add` instance on the `⊤` subring.
  let instAddZero : AddZeroClass (⊤ : (Subring (PowerSeries K))) := inferInstance
  let _ := instAddZero.2
  exact ((Subring.topEquiv).symm).trans (Subring.equivMapOfInjective ⊤ (HahnSeries.ofPowerSeries ℤ K)
    HahnSeries.ofPowerSeries_injective)
  -- exact (((@Subring.topEquiv (PowerSeries K) _)).symm).trans (Subring.equivMapOfInjective ⊤ (HahnSeries.ofPowerSeries ℤ K)
  --   HahnSeries.ofPowerSeries_injective)

theorem mem_integers_of_powerSeries (F : PowerSeries K) :
    (LaurentSeriesRingEquiv K) F ∈ (Polynomial.idealX K).adicCompletionIntegers (RatFunc K) := by
  have :
    (LaurentSeriesRingEquiv K) F =
      (LaurentSeriesPkg K).compare (ratfuncAdicComplPkg K) (F : LaurentSeries K) :=
    rfl
  simp only [Subring.mem_map, exists_prop, ValuationSubring.mem_toSubring,
    mem_adicCompletionIntegers, this, valuation_compare K F, val_le_one_iff_eq_coe]
  refine' ⟨F, rfl⟩

theorem exists_powerSeries_of_memIntegers {x : RatFuncAdicCompl K}
    (hx : x ∈ (Polynomial.idealX K).adicCompletionIntegers (RatFunc K)) :
    ∃ F : PowerSeries K, (LaurentSeriesRingEquiv K) F = x := by
  set f := (ratfuncAdicComplRingEquiv K) x with hf
  have := valuation_compare K f
  have H_x :
    (LaurentSeriesPkg K).compare (ratfuncAdicComplPkg K)
        ((ratfuncAdicComplRingEquiv K) x) =
      x :=
    congr_fun (inverse_compare (LaurentSeriesPkg K) (ratfuncAdicComplPkg K)) x
  simp only [Subring.mem_map, exists_prop, ValuationSubring.mem_toSubring,
    mem_adicCompletionIntegers, this] at hx
  rw [H_x] at this
  rw [this] at hx
  obtain ⟨F, h_fF⟩ := (val_le_one_iff_eq_coe K f).mp hx
  use F
  rw [h_fF, hf, RingEquiv.symm_apply_apply]

theorem power_series_ext_subring :
    Subring.map (LaurentSeriesRingEquiv K).toRingHom (powerSeries_as_subring K) =
      ((Polynomial.idealX K).adicCompletionIntegers (RatFunc K)).toSubring := by
  ext x
  constructor
  · rintro ⟨f, ⟨F, coe_F⟩, h_fF⟩
    simp only [ValuationSubring.mem_toSubring, ← h_fF, ← coe_F]
    apply mem_integers_of_powerSeries
  · intro H
    obtain ⟨F, hF⟩ := exists_powerSeries_of_memIntegers K H
    simp only [Equiv.toFun_as_coe, UniformEquiv.coe_toEquiv, exists_exists_eq_and,
      UniformEquiv.coe_symm_toEquiv, Subring.mem_map, Equiv.invFun_as_coe]
    exact ⟨F, ⟨F, rfl⟩, hF⟩

/-- The ring isomorphism between `(power_series K)` and the unit ball inside the `X`-adic
completion of `ratfunc`. -/
@[reducible]
def powerSeriesRingEquiv : PowerSeries K ≃+* (Polynomial.idealX K).adicCompletionIntegers (RatFunc K) :=
  ((powerSeriesEquivSubring K).trans
        (@RingEquiv.subringMap _ _ _ _ (powerSeries_as_subring K) (LaurentSeriesRingEquiv K))).trans
    (RingEquiv.subringCongr (power_series_ext_subring K))

end PowerSeries

end Comparison

end CompletionLaurentSeries
