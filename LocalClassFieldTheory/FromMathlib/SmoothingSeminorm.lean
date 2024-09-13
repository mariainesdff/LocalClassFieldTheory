/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
--import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Sequences
import LocalClassFieldTheory.FromMathlib.Limsup
import LocalClassFieldTheory.FromMathlib.RingSeminorm -- add lemmas to this PR

/-!
# smoothingSeminorm
In this file, we prove [BGR, Proposition 1.3.2/1][bosch-guntzer-remmert] : if `f` is a
nonarchimedean seminorm on `R`, then `iInf (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ)))` is a
power-multiplicative nonarchimedean seminorm on `R`.

## Main Definitions

* `smoothingSeminorm_seq` : the `ℝ`-valued sequence sending `n` to `(f (x ^ n))^(1/n : ℝ)`.
* `smoothingSeminorm'` : the iInf of the sequence `f(x^(n : ℕ)))^(1/(n : ℝ)`.
* `smoothingSeminorm` : if `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothingSeminorm'`
  is a ring seminorm.

## Main Results

* `smoothingSeminorm'_isLimit` :if `f 1 ≤ 1`, then `smoothingSeminorm' f x` is the limit
  of `smoothingSeminorm_seq f x` as `n` tends to infinity.
* `smoothingSeminorm_isNonarchimedean` : if `f 1 ≤ 1` and `f` is nonarchimedean, then
  `smoothingSeminorm'` is nonarchimedean.
* `smoothingSeminorm_isPowMul` : if `f 1 ≤ 1` and `f` is nonarchimedean, then
  `smoothingSeminorm' f` is power-multiplicative.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

smoothingSeminorm, seminorm, nonarchimedean
-/

-- In PR #15373

noncomputable section

open Real

open scoped Topology NNReal

-- In this section we prove auxiliary lemmas, which will be PR'd to the appropriate mathlib files.
section AuxLemmas

/-- If `a` belongs to the interval `[0, b]`, then so does `b - a`. -/
theorem sub_mem_Icc {a b : ℝ} (h : a ∈ Set.Icc (0 : ℝ) b) : b - a ∈ Set.Icc (0 : ℝ) b := by
  rw [Set.mem_Icc] at h ⊢
  rw [sub_le_self_iff]
  exact ⟨sub_nonneg_of_le h.2, h.1⟩

/-- If `x` is multiplicative with respect to `f`, then so is any `x^n`. -/
theorem is_mul_pow_of_is_mul {R : Type _} [CommRing R] (f : R → ℝ) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : ∀ (n : ℕ) (y : R), f (x ^ n * y) = f x ^ n * f y := by
  intro n
  induction' n with n hn
  · intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  · intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

-- Not used in this file
/-- For any `r : ℝ≥0` and any positive `n : ℕ`,  `(r ^ n)^(1/n : ℝ) = r`. -/
theorem NNReal.pow_n_n_inv (r : ℝ≥0) {n : ℕ} (hn : 0 < n) : (r ^ n) ^ (1 / n : ℝ) = r := by
  conv_rhs => rw [← rpow_one r, ← mul_one_div_cancel
    (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn))]
  rw [rpow_mul, rpow_natCast]

-- Not used in this file
/-- For any nonnegative `r : ℝ` and any positive `n : ℕ`,  `(r ^ n)^(1/n : ℝ) = r`. -/
theorem Real.pow_n_n_inv {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) : (r ^ n) ^ (1 / n : ℝ) = r := by
  conv_rhs => rw [← rpow_one r, ← mul_one_div_cancel
    (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn))]
  rw [Real.rpow_mul hr, rpow_natCast]

open Nat
namespace Filter

/-- If there exists real constants `b`and `B` such that for `n` big enough, `b ≤ f n ≤ B`, then
  `f n / (n : ℝ)` tends to `0` as `n` tends to infinity. -/
theorem tendsto_bdd_div_atTop_nhds_zero_nat (f : ℕ → ℝ) (b : ℝ)
    (hb : ∀ᶠ n : ℕ in atTop, b ≤ f n) (B : ℝ) (hB : ∀ᶠ n : ℕ in atTop, f n ≤ B) :
    Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_div_atTop_nhds_zero_nat b)
      (tendsto_const_div_atTop_nhds_zero_nat B) ?_ ?_
  · simp only [eventually_atTop, ge_iff_le] at hb ⊢
    obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun n hn ↦ div_le_div_of_nonneg_right (hN n hn) (cast_nonneg _)⟩
  · simp only [eventually_atTop, ge_iff_le] at hB ⊢
    obtain ⟨N, hN⟩ := hB
    exact ⟨N, fun n hn ↦ div_le_div_of_nonneg_right (hN n hn) (cast_nonneg _)⟩

/-- For any positive `m : ℕ`, `((n % m : ℕ) : ℝ) / (n : ℝ)` tends to `0` as `n` tends to `∞`. -/
theorem tendsto_mod_div_atTop_nhds_zero_nat {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n % m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero_nat (fun n : ℕ => ((n % m : ℕ) : ℝ)) 0
    (Eventually.of_forall (fun _ ↦ cast_nonneg _)) m
  apply Eventually.of_forall
  intro n
  simp only [cast_le, le_of_lt (mod_lt n hm)]

/-- If `u` tends to `∞` as `n` tends to `∞`, then for `n` big enough
  `((s n : ℝ) / (u n : ℝ)) * (u n : ℝ) = (s n : ℝ)` holds. -/
theorem div_mul_eventually_cancel (s : ℕ → ℕ) {u : ℕ → ℕ} (hu : Tendsto u atTop atTop) :
    (fun n => (s n : ℝ) / (u n : ℝ) * (u n : ℝ)) =ᶠ[atTop] fun n => (s n : ℝ) := by
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  simp only [tendsto_atTop, eventually_atTop, ge_iff_le] at hu
  obtain ⟨n, hn⟩ := hu 1
  use n
  intro m hm
  rw [div_mul_cancel₀ (s m : ℝ) (cast_ne_zero.mpr (one_le_iff_ne_zero.mp (hn m hm)))]

/-- If when `n` tends to `∞`, `u` tends to `∞` and `(s n : ℝ) / (u n : ℝ))` tends to a nonzero
  constant, then `s` tends to `∞`. -/
theorem Tendsto.num {s u : ℕ → ℕ} (hu : Tendsto u atTop atTop) {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto (fun n : ℕ => (s n : ℝ) / (u n : ℝ)) atTop (𝓝 a)) : Tendsto s atTop atTop :=
  tendsto_natCast_atTop_iff.mp (Tendsto.congr' (div_mul_eventually_cancel s hu)
    (Tendsto.mul_atTop ha hlim (tendsto_natCast_atTop_iff.mpr hu)))

/-- If `f` is a ring seminorm on `R` with `f 1 ≤ 1` and `s : ℕ → ℕ` is bounded by `n`, then
  `f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))` is eventually bounded. -/
theorem isBoundedUnder {R : Type _} [CommRing R] (f : RingSeminorm R) (hf1 : f 1 ≤ 1) {s : ℕ → ℕ}
    (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} (ψ : ℕ → ℕ) :
    IsBoundedUnder LE.le atTop fun n : ℕ => f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ)) := by
  have h_le : ∀ m : ℕ, f (x ^ s (ψ m)) ^ (1 / (ψ m : ℝ)) ≤ f x ^ ((s (ψ m) : ℝ) / (ψ m : ℝ)) := by
    intro m
    rw [← mul_one_div (s (ψ m) : ℝ), rpow_mul (apply_nonneg f x), rpow_natCast]
    exact rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hf1 x _)
      (one_div_nonneg.mpr (cast_nonneg _))
  apply isBoundedUnder_of
  by_cases hfx : f x ≤ 1
  · use 1, fun m => le_trans (h_le m)
      (rpow_le_one (apply_nonneg _ _) hfx (div_nonneg (cast_nonneg _) (cast_nonneg _)))
  · use f x
    intro m
    apply le_trans (h_le m)
    conv_rhs => rw [← rpow_one (f x)]
    exact rpow_le_rpow_of_exponent_le (le_of_lt (not_le.mp hfx))
      (div_le_one_of_le (cast_le.mpr (hs_le _)) (cast_nonneg _))

end Filter

end AuxLemmas

open Filter Nat Real

variable {R : Type _} [CommRing R] (f : RingSeminorm R)

section smoothingSeminorm

/-- The `ℝ`-valued sequence sending `n` to `(f (x ^ n))^(1/n : ℝ)`. -/
def smoothingSeminormSeq (x : R) : ℕ → ℝ := fun n => f (x ^ n) ^ (1 / n : ℝ)

/-- For any positive `ε`, there exists a positive natural number `m` such that
  `f (x ^ (m : ℕ)) ^ (1 / m : ℝ) < iInf (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2`. -/
private theorem smoothingSeminorm_seq_hasLimit_m (x : R) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : PNat, f (x ^ (m : ℕ)) ^ (1 / m : ℝ) <
        (iInf fun n : PNat => f (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) + ε / 2 :=
  exists_lt_of_ciInf_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))

private theorem smoothingSeminorm_seq_hasLimit_aux {L : ℝ} (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε)
    {m1 : ℕ} (hm1 : 0 < m1) {x : R} (hx : f x ≠ 0) :
    Tendsto
      (fun n : ℕ => (L + ε) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) * (f x ^ (n % m1)) ^ (1 / (n : ℝ)))
      atTop (𝓝 1) := by
  rw [← mul_one (1 : ℝ)]
  have h_exp : Tendsto (fun n : ℕ => ((n % m1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hm1
  apply Tendsto.mul
  · have h0 : Tendsto (fun t : ℕ => -(((t % m1 : ℕ) : ℝ) / (t : ℝ))) atTop (𝓝 0) := by
      rw [← neg_zero]
      exact Tendsto.neg h_exp
    rw [← rpow_zero (L + ε)]
    apply Tendsto.rpow tendsto_const_nhds h0
    rw [ne_eq, add_eq_zero_iff_of_nonneg hL (le_of_lt hε)]
    exact Or.inl (not_and_of_not_right _ (ne_of_gt hε))
  · simp_rw [mul_one, ← rpow_natCast, ← rpow_mul (apply_nonneg f x), ← mul_div_assoc, mul_one, ←
      rpow_zero (f x)]
    exact Tendsto.rpow tendsto_const_nhds h_exp (Or.inl hx)

/-- `smoothingSeminorm_seq` is bounded below by zero. -/
theorem smoothingSeminorm_seq_bddBelow (x : R) :
    BddBelow (Set.range fun n : ℕ+ => f (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) := by
  use 0
  rintro y ⟨n, rfl⟩
  exact rpow_nonneg (apply_nonneg f _) _

/-- The iInf of the sequence `f(x^(n : ℕ)))^(1/(n : ℝ)`. -/
def smoothingSeminorm' (x : R) : ℝ :=
  iInf fun n : PNat => f (x ^ (n : ℕ)) ^ (1 / (n : ℝ))

/-- If `f x = 0`, then `smoothingSeminorm' f x` is the limit of `smoothingSeminorm_seq f x`. -/
theorem smoothingSeminorm'_isLimit_zero {x : R} (hx : f x = 0) :
    Tendsto (smoothingSeminormSeq f x) atTop (𝓝 (smoothingSeminorm' f x)) := by
  have h0 : ∀ (n : ℕ) (_hn : 1 ≤ n), f (x ^ n) ^ (1 / (n : ℝ)) = 0 := fun n hn ↦ by
    have hfn : f (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg f _)
      rw [← zero_pow (pos_iff_ne_zero.mp hn), ← hx]
      exact map_pow_le_pow _ x (one_le_iff_ne_zero.mp hn)
    rw [hfn, zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  have hL0 : (iInf fun n : PNat => f (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) = 0 :=
    le_antisymm
      (ciInf_le_of_le (smoothingSeminorm_seq_bddBelow f x) (1 : PNat) (le_of_eq (h0 1 (le_refl _))))
      (le_ciInf fun n => rpow_nonneg (apply_nonneg f _) _)
  simp only [hL0, smoothingSeminormSeq, smoothingSeminorm']
  exact tendsto_atTop_of_eventually_const h0

/-- If `f 1 ≤ 1` and `f x ≠  0`, then `smoothingSeminorm' f x` is the limit of
`smoothingSeminorm_seq f x`. -/
theorem smoothingSeminorm'_isLimit_ne_zero (hf1 : f 1 ≤ 1) {x : R} (hx : f x ≠ 0) :
    Tendsto (smoothingSeminormSeq f x) atTop (𝓝 (smoothingSeminorm' f x)) := by
  simp only [smoothingSeminorm']
  set L := iInf fun n : PNat => f (x ^ (n : ℕ)) ^ (1 / (n : ℝ))
  have hL0 : 0 ≤ L := le_ciInf fun x => rpow_nonneg (apply_nonneg _ _) _
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m1, hm1⟩ := smoothingSeminorm_seq_hasLimit_m f x hε
  obtain ⟨m2, hm2⟩ : ∃ m : ℕ, ∀ n ≥ m,
      (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) * (f x ^ (n % m1)) ^ (1 / (n : ℝ)) - 1 ≤
      ε / (2 * (L + ε / 2)) := by
    have hε2 : 0 < ε / 2 := half_pos hε
    have hL2 := smoothingSeminorm_seq_hasLimit_aux f hL0 hε2 (PNat.pos m1) hx
    rw [Metric.tendsto_atTop] at hL2
    set δ : ℝ := ε / (2 * (L + ε / 2)) with hδ_def
    have hδ : 0 < δ := by
      rw [hδ_def, div_mul_eq_div_mul_one_div]
      exact mul_pos hε2
        ((one_div (L + ε / 2)).symm ▸ inv_pos_of_pos (add_pos_of_nonneg_of_pos hL0 hε2))
    obtain ⟨N, hN⟩ := hL2 δ hδ
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq, abs_lt] at hN
    exact le_of_lt hN.right
  use max (m1 : ℕ) m2
  intro n hn
  have hn0 : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (PNat.pos m1) (le_max_left (m1 : ℕ) m2)) hn
  rw [Real.dist_eq, abs_lt]
  have hL_le : L ≤ smoothingSeminormSeq f x n := by
    simp only [smoothingSeminormSeq]
    rw [← PNat.mk_coe n hn0]
    apply ciInf_le (smoothingSeminorm_seq_bddBelow f x)
  refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) (sub_nonneg.mpr hL_le), ?_⟩
  · suffices h : smoothingSeminormSeq f x n < L + ε by
      rw [tsub_lt_iff_left hL_le]
      exact h
    by_cases hxn : f (x ^ (n % m1)) = 0
    · simp only [smoothingSeminormSeq]
      nth_rw 1 [← div_add_mod n m1]
      have hLε : 0 < L + ε := add_pos_of_nonneg_of_pos hL0 hε
      apply lt_of_le_of_lt _ hLε
      rw [pow_add, ← MulZeroClass.mul_zero (f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ))),
        ← zero_rpow (one_div_cast_ne_zero (pos_iff_ne_zero.mp hn0)), ← hxn,
        ← mul_rpow (apply_nonneg f _) (apply_nonneg f _)]
      exact rpow_le_rpow (apply_nonneg f _) (map_mul_le_mul f _ _) (one_div_cast_nonneg _)
    · have hxn' : 0 < f (x ^ (n % ↑m1)) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hxn)
      simp only [smoothingSeminormSeq]
      nth_rw 1 [← div_add_mod n m1]
      have h : f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ)) ≤
          (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) := by
        apply rpow_le_rpow (apply_nonneg f _) _ (one_div_cast_nonneg _)
        rw [pow_mul]
        exact map_pow_le_pow f (x^(m1 : ℕ))
          (pos_iff_ne_zero.mp (Nat.div_pos (le_trans (le_max_left (m1 : ℕ) m2) hn) (PNat.pos m1)))
      have hL0' : 0 < L + ε / 2 := add_pos_of_nonneg_of_pos hL0 (half_pos hε)
      have h1 : (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) <
          (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) := by
        have hm10 : (m1 : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (PNat.pos m1))
        rw [← rpow_lt_rpow_iff (rpow_nonneg (apply_nonneg f _) _) (le_of_lt hL0')
          (cast_pos.mpr (PNat.pos m1)), ← rpow_mul (apply_nonneg f _), one_div_mul_cancel hm10,
          rpow_one] at hm1
        nth_rw 1 [← rpow_one (L + ε / 2)]
        have : (n : ℝ) / n = (1 : ℝ) := div_self (cast_ne_zero.mpr (_root_.ne_of_gt hn0))
        nth_rw 2 [← this]; clear this
        nth_rw 3 [← div_add_mod n m1]
        have h_lt : 0 < ((n / m1 : ℕ) : ℝ) / (n : ℝ) :=
          div_pos (cast_pos.mpr (Nat.div_pos (le_trans (le_max_left _ _) hn) (PNat.pos m1)))
            (cast_pos.mpr hn0)
        rw [← rpow_natCast, ← rpow_add hL0', ← neg_div, div_add_div_same, Nat.cast_add,
          add_neg_cancel_right, Nat.cast_mul, ← rpow_mul (apply_nonneg f _), mul_one_div,
          mul_div_assoc, rpow_mul (le_of_lt hL0')]
        exact rpow_lt_rpow (apply_nonneg f _) hm1 h_lt
      have h2 : f (x ^ (n % m1)) ^ (1 / (n : ℝ)) ≤ (f x ^ (n % m1)) ^ (1 / (n : ℝ)) := by
        by_cases hnm1 : n % m1 = 0
        · simpa [hnm1, pow_zero] using rpow_le_rpow (apply_nonneg f _) hf1 (one_div_cast_nonneg _)
        · exact rpow_le_rpow (apply_nonneg f _) (map_pow_le_pow f _ hnm1) (one_div_cast_nonneg _)
      have h3 : (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) *
            (f x ^ (n % m1)) ^ (1 / (n : ℝ)) ≤ L + ε := by
        have heq : L + ε = L + ε / 2 + ε / 2 := by rw [add_assoc, add_halves]
        have hL0' : 0 < L + ε / 2 := add_pos_of_nonneg_of_pos hL0 (half_pos hε)
        rw [heq, ← tsub_le_iff_left]
        nth_rw 3 [← mul_one (L + ε / 2)]
        rw [mul_assoc, ← mul_sub, mul_comm, ← le_div_iff₀ hL0', div_div]
        exact hm2 n (le_trans (le_max_right (m1 : ℕ) m2) hn)
      have h4 : 0 < f (x ^ (n % ↑m1)) ^ (1 / (n : ℝ)) := rpow_pos_of_pos hxn' _
      have h5 : 0 < (L + ε / 2) * (L + ε / 2) ^ (-(↑(n % ↑m1) / (n : ℝ))) :=
        mul_pos hL0' (rpow_pos_of_pos hL0' _)
      calc f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)) + n % m1)) ^ (1 / (n : ℝ)) =
            f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ))) * x ^ (n % m1)) ^ (1 / (n : ℝ)) :=
          by rw [pow_add]
        _ ≤ (f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) * f (x ^ (n % m1))) ^ (1 / (n : ℝ)) :=
          (rpow_le_rpow (apply_nonneg f _) (map_mul_le_mul f _ _) (one_div_cast_nonneg _))
        _ = f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ)) *
            f (x ^ (n % m1)) ^ (1 / (n : ℝ)) :=
          (mul_rpow (apply_nonneg f _) (apply_nonneg f _))
        _ ≤ (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) *
              f (x ^ (n % m1)) ^ (1 / (n : ℝ)) := ((mul_le_mul_right h4).mpr h)
        _ < (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) *
              f (x ^ (n % m1)) ^ (1 / (n : ℝ)) := (mul_lt_mul h1 (le_refl _) h4 (le_of_lt h5))
        _ ≤ (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) *
              (f x ^ (n % m1)) ^ (1 / (n : ℝ)) := ((mul_le_mul_left h5).mpr h2)
        _ ≤ L + ε := h3

/-- If `f 1 ≤ 1`, then `smoothingSeminorm' f x` is the limit of `smoothingSeminorm_seq f x`
  as `n` tends to infinity. -/
theorem smoothingSeminorm'_isLimit (hf1 : f 1 ≤ 1) (x : R) :
    Tendsto (smoothingSeminormSeq f x) atTop (𝓝 (smoothingSeminorm' f x)) := by
  by_cases hx : f x = 0
  · exact smoothingSeminorm'_isLimit_zero f hx
  · exact smoothingSeminorm'_isLimit_ne_zero f hf1 hx

/-- If `f 1 ≤ 1`, then `smoothingSeminorm' f x` is nonnegative. -/
theorem smoothingSeminorm_nonneg (hf1 : f 1 ≤ 1) (x : R) : 0 ≤ smoothingSeminorm' f x := by
  apply ge_of_tendsto (smoothingSeminorm'_isLimit f hf1 x)
  simp only [eventually_atTop, ge_iff_le]
  exact ⟨1, fun _ _ ↦ rpow_nonneg (apply_nonneg f _) _⟩

/- /-- If `f 1 ≤ 1`, then `smoothingSeminorm' f 0 = 0`. -/
theorem smoothingSeminorm_zero (hf1 : f 1 ≤ 1) : smoothingSeminorm' f 0 = 0 := by
  apply
    tendsto_nhds_unique_of_eventuallyEq (smoothingSeminorm'_isLimit f hf1 0) tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  rw [zero_pow (pos_iff_ne_zero.mp hn), map_zero, zero_rpow]
  exact one_div_ne_zero (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)) -/

/- /-- If `f (-x) = f x`, the same holds for `smoothingSeminorm' f`. -/
theorem smoothingSeminorm_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) :
    smoothingSeminorm' f (-x) = smoothingSeminorm' f x := by
  simp only [smoothingSeminorm', smoothingSeminorm']
  congr
  ext n
  rw [neg_pow]
  rcases neg_one_pow_eq_or R n with hpos | hneg
  · rw [hpos, one_mul]
  · rw [hneg, neg_one_mul, f_neg] -/

/- /-- If `f 1 ≤ 1`, then `smoothingSeminorm' f` is submultiplicative. -/
theorem smoothingSeminorm_mul (hf1 : f 1 ≤ 1) (x y : R) :
    smoothingSeminorm' f (x * y) ≤ smoothingSeminorm' f x * smoothingSeminorm' f y := by
  apply le_of_tendsto_of_tendsto' (smoothingSeminorm'_isLimit f hf1 (x * y))
    (Tendsto.mul (smoothingSeminorm'_isLimit f hf1 x) (smoothingSeminorm'_isLimit f hf1 y))
  intro n
  have hn : 0 ≤ 1 / (n : ℝ) := by simp only [one_div, inv_nonneg, cast_nonneg]
  simp only [smoothingSeminormSeq]
  rw [← mul_rpow (apply_nonneg f _) (apply_nonneg f _), mul_pow]
  exact rpow_le_rpow (apply_nonneg f _) (map_mul_le_mul f _ _) hn -/

/-- If `f 1 ≤ 1`, then `smoothingSeminorm' f 1 ≤ 1`. -/
theorem smoothingSeminorm_one (hf1 : f 1 ≤ 1) : smoothingSeminorm' f 1 ≤ 1 := by
  apply le_of_tendsto (smoothingSeminorm'_isLimit f hf1 (1 : R))
  simp only [eventually_atTop, ge_iff_le]
  use 1
  rintro n hn
  simp only [smoothingSeminormSeq]
  rw [one_pow]
  conv_rhs => rw [← one_rpow (1 / n : ℝ)]
  have hn1 : 0 < (1 / n : ℝ) := by
    apply div_pos zero_lt_one
    rw [← cast_zero, cast_lt]
    exact succ_le_iff.mp hn
  exact (rpow_le_rpow_iff (apply_nonneg f _) zero_le_one hn1).mpr hf1

/-- For any `x` and any positive `n`, `smoothingSeminorm' f x  ≤ f (x^(n : ℕ))^(1/n : ℝ)`. -/
theorem smoothingSeminorm_le_term (x : R) (n : PNat) :
    smoothingSeminorm' f x ≤ f (x ^ (n : ℕ)) ^ (1 / n : ℝ) :=
  ciInf_le (smoothingSeminorm_seq_bddBelow f x) _

/-- For all `x : R`, `smoothingSeminorm' f x ≤ f x`. -/
theorem smoothingSeminorm_le (x : R) : smoothingSeminorm' f x ≤ f x := by
  convert smoothingSeminorm_le_term f x 1
  rw [PNat.one_coe, pow_one, cast_one, div_one, rpow_one]


/- In this section, we prove that if `f` is nonarchimedean, then `smoothingSeminorm' f` is
  nonarchimedean. -/
section IsNonarchimedean

theorem exists_index_le (hna : IsNonarchimedean f) (x y : R) (n : ℕ) :
    ∃ (m : ℕ) (_ : m ∈ Finset.range (n + 1)), f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤
      (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)) := by
  obtain ⟨m, hm_lt, hm⟩ := isNonarchimedean_add_pow hna n x y
  exact ⟨m, hm_lt, rpow_le_rpow (apply_nonneg f _) hm (one_div_cast_nonneg (n : ℕ))⟩

/-- Auxiliary sequence for the proof that `smoothingSeminorm'` is nonarchimedean. -/
private def mu {x y : R} (hn : ∀ n : ℕ, ∃ (m : ℕ) (_ : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ))) :
    ℕ → ℕ := fun n => Classical.choose (hn n)

private theorem mu_property {x y : R} (hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
    (n : ℕ) : f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤
      (f (x ^ mu f hn n) * f (y ^ (n - mu f hn n : ℕ))) ^ (1 / (n : ℝ)) :=
  Classical.choose_spec (Classical.choose_spec (hn n))

private theorem mu_le {x y : R} (hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
    (n : ℕ) : mu f hn n ≤ n := by
  simp only [mu, ← Nat.lt_succ_iff, ← Finset.mem_range]
  exact Classical.choose (Classical.choose_spec (hn n))

private theorem mu_bdd {x y : R} (hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
    (n : ℕ) : (mu f hn n : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨div_nonneg (cast_nonneg (mu f hn n)) (cast_nonneg n), ?_⟩
  by_cases hn0 : n = 0
  · rw [hn0, cast_zero, div_zero]; exact zero_le_one
  · have hn' : 0 < (n : ℝ) := cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    rw [div_le_one hn', cast_le]
    exact mu_le _ _ _

private theorem f_bddBelow (s : ℕ → ℕ) {x y : R}
    (_hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
    (ψ : ℕ → ℕ) :
    BddBelow {a : ℝ | ∀ᶠ n : ℝ in map (fun n : ℕ => f x ^ (↑(s (ψ n)) * (1 / (ψ n : ℝ)))) atTop,
      n ≤ a} := by
  use 0
  simp only [mem_lowerBounds, eventually_map, eventually_atTop, ge_iff_le, Set.mem_setOf_eq,
    forall_exists_index]
  intro r m hm
  exact le_trans (rpow_nonneg (apply_nonneg f _) _) (hm m (le_refl _))

private theorem f_bddAbove (hf1 : f 1 ≤ 1) {s : ℕ → ℕ} (hs : ∀ n : ℕ, s n ≤ n) (x : R)
    (ψ : ℕ → ℕ) : BddAbove (Set.range fun n : ℕ => f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) := by
  have hψ : ∀ n : ℕ, 0 ≤ 1 / (ψ n : ℝ) := fun _ ↦ by simp only [one_div, inv_nonneg, cast_nonneg]
  by_cases hx : f x ≤ 1
  · use 1
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff']
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hf1 _ _) (hψ n))
    rw [← rpow_natCast, ← rpow_mul (apply_nonneg _ _), mul_one_div]
    exact rpow_le_one (apply_nonneg _ _) hx (div_nonneg (cast_nonneg _) (cast_nonneg _))
  · use f x
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff']
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hf1 _ _) (hψ n))
    rw [← rpow_natCast, ← rpow_mul (apply_nonneg _ _), mul_one_div]
    conv_rhs => rw [← rpow_one (f x)]
    rw [rpow_le_rpow_left_iff (not_le.mp hx)]
    exact div_le_one_of_le (cast_le.mpr (hs (ψ n))) (cast_nonneg _)

private theorem f_nonempty {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R} (_hn : ∀ n : ℕ,
      ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
        f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
    (ψ : ℕ → ℕ) :
    {a : ℝ | ∀ᶠ n : ℝ in map (fun n : ℕ => f x ^ (↑(s (ψ n)) * (1 / (ψ n : ℝ)))) atTop,
      n ≤ a}.Nonempty := by
  by_cases hfx : f x < 1
  · use 1
    simp only [eventually_map, eventually_atTop, ge_iff_le, Set.mem_setOf_eq]
    exact ⟨0, fun _ _ ↦ rpow_le_one (apply_nonneg _ _) (le_of_lt hfx)
      (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))⟩
  · use f x
    simp only [eventually_map, eventually_atTop, ge_iff_le, Set.mem_setOf_eq]
    use 0
    intro b _
    nth_rw 2 [← rpow_one (f x)]
    apply rpow_le_rpow_of_exponent_le (not_lt.mp hfx)
    rw [mul_one_div]
    exact div_le_one_of_le (cast_le.mpr (hs_le (ψ b))) (cast_nonneg _)

private theorem f_limsup_le_one {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R}
    (hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
      {ψ : ℕ → ℕ} (hψ_lim : Tendsto ((fun n : ℕ => ↑(s n) / (n : ℝ)) ∘ ψ) atTop (𝓝 0)) :
    limsup (fun n : ℕ => f x ^ ((s (ψ n) : ℝ) * (1 / (ψ n : ℝ)))) atTop ≤ 1 := by
  simp only [limsup, limsSup]
  rw [csInf_le_iff (f_bddBelow f s hn ψ) (f_nonempty f hs_le hn ψ)]
  · intro c hc_bd
    simp only [mem_lowerBounds, eventually_map, eventually_atTop, ge_iff_le, Set.mem_setOf_eq,
      forall_exists_index] at hc_bd
    by_cases hfx : f x < 1
    · apply hc_bd (1 : ℝ) 0
      intro b _
      exact rpow_le_one (apply_nonneg _ _) (le_of_lt hfx)
          (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))
    · have hf_lim : Tendsto (fun n : ℕ => f x ^ (↑(s (ψ n)) * (1 / (ψ n : ℝ)))) atTop (𝓝 1) := by
        nth_rw 1 [← rpow_zero (f x)]
        convert Tendsto.rpow tendsto_const_nhds hψ_lim
            (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (not_lt.mp hfx))))
        · simp only [rpow_zero, mul_one_div, Function.comp_apply]
        · rw [rpow_zero]
      rw [tendsto_atTop_nhds] at hf_lim
      apply le_of_forall_pos_le_add
      intro ε hε
      have h1 : (1 : ℝ) ∈ Set.Ioo 0 (1 + ε) := by
        simp only [Set.mem_Ioo, zero_lt_one, lt_add_iff_pos_right, true_and_iff, hε]
      obtain ⟨k, hk⟩ := hf_lim (Set.Ioo (0 : ℝ) (1 + ε)) h1 isOpen_Ioo
      exact hc_bd (1 + ε) k fun b hb => le_of_lt (Set.mem_Ioo.mp (hk b hb)).2

theorem smoothingSeminorm'_isLimit_comp (hf1 : f 1 ≤ 1) (x : R) {ψ : ℕ → ℕ}
    (hψ_mono : StrictMono ψ) :
    Tendsto (fun n : ℕ => f (x ^ ψ n) ^ (1 / ψ n : ℝ)) atTop (𝓝 (smoothingSeminorm' f x)) :=
  haveI hψ_lim' : Tendsto ψ atTop atTop := StrictMono.tendsto_atTop hψ_mono
  (smoothingSeminorm'_isLimit f hf1 x).comp hψ_lim'

private theorem limsup_mu_le (hf1 : f 1 ≤ 1) {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R}
    (hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
      f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))
    {a : ℝ} (a_in : a ∈ Set.Icc (0 : ℝ) 1) {ψ : ℕ → ℕ} (hψ_mono : StrictMono ψ)
    (hψ_lim : Tendsto ((fun n : ℕ => (s n : ℝ) / ↑n) ∘ ψ) atTop (𝓝 a)) :
    limsup (fun n : ℕ => f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤ smoothingSeminorm' f x ^ a := by
  by_cases ha : a = 0
  · rw [ha] at hψ_lim
    calc limsup (fun n : ℕ => f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
          limsup (fun n : ℕ => f x ^ ((s (ψ n) : ℝ) * (1 / (ψ n : ℝ)))) atTop := by
          apply csInf_le_csInf _ (f_nonempty f hs_le hn ψ)
          · intro b hb
            simp only [eventually_map, eventually_atTop, ge_iff_le, Set.mem_setOf_eq] at hb ⊢
            obtain ⟨m, hm⟩ := hb
            use m
            intro k hkm
            apply le_trans _ (hm k hkm)
            rw [rpow_mul (apply_nonneg f x), rpow_natCast]
            exact rpow_le_rpow (apply_nonneg f _) (map_pow_le_pow' hf1 x _)
              (one_div_nonneg.mpr (cast_nonneg _))
          · use 0
            simp only [mem_lowerBounds, eventually_map, eventually_atTop, ge_iff_le,
              Set.mem_setOf_eq, forall_exists_index]
            exact fun _ m hm ↦ le_trans (rpow_nonneg (apply_nonneg f _) _) (hm m (le_refl _))
      _ ≤ 1 := (f_limsup_le_one f hs_le hn hψ_lim)
      _ = smoothingSeminorm' f x ^ a := by rw [ha, rpow_zero]
  · have ha_pos : 0 < a := lt_of_le_of_ne a_in.1 (Ne.symm ha)
    have h_eq : (fun n : ℕ =>
        (f (x ^ s (ψ n)) ^ (1 / (s (ψ n) : ℝ))) ^ ((s (ψ n) : ℝ) / (ψ n : ℝ))) =ᶠ[atTop]
        fun n : ℕ => f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ)) := by
      have h : (fun n : ℕ => (1 : ℝ) / (s (ψ n) : ℝ) * (s (ψ n) : ℝ)) =ᶠ[atTop] 1 := by
        convert div_mul_eventually_cancel 1 (Tendsto.num hψ_mono.tendsto_atTop ha_pos hψ_lim)
          using 1
        · simp only [Pi.one_apply, cast_one]
        · simp only [Pi.one_apply, cast_one]; rfl
      simp_rw [← rpow_mul (apply_nonneg f _), mul_div]
      exact EventuallyEq.comp₂ EventuallyEq.rfl HPow.hPow (h.div EventuallyEq.rfl)
    exact le_of_eq (Tendsto.limsup_eq (Tendsto.congr' h_eq (Tendsto.rpow
      ((smoothingSeminorm'_isLimit f hf1 x).comp (Tendsto.num hψ_mono.tendsto_atTop ha_pos hψ_lim))
      hψ_lim (Or.inr ha_pos))))

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothingSeminorm'` is nonarchimedean. -/
theorem smoothingSeminorm_isNonarchimedean (hf1 : f 1 ≤ 1) (hna : IsNonarchimedean f) :
    IsNonarchimedean (smoothingSeminorm' f) := by
  intro x y
  have hn : ∀ n : ℕ, ∃ (m : ℕ) (_hm : m ∈ Finset.range (n + 1)),
        f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)) :=
    fun n => exists_index_le f hna x y n
  set mu : ℕ → ℕ := fun n => mu f hn n
  set nu : ℕ → ℕ := fun n => n - mu n with hnu
  have hmu_le : ∀ n : ℕ, mu n ≤ n := fun n => mu_le f hn n
  have hmu_bdd : ∀ n : ℕ, (mu n : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := fun n => mu_bdd f hn n
  have hs : Bornology.IsBounded (Set.Icc (0 : ℝ) 1) := Metric.isBounded_Icc 0 1
  obtain ⟨a, a_in, ψ, hψ_mono, hψ_lim⟩ := tendsto_subseq_of_bounded hs hmu_bdd
  rw [closure_Icc] at a_in
  set b := 1 - a with hb
  have hb_lim : Tendsto ((fun n : ℕ => (nu n : ℝ) / ↑n) ∘ ψ) atTop (𝓝 b) := by
    apply Tendsto.congr' _ (Tendsto.const_sub 1 hψ_lim)
    simp only [EventuallyEq, Function.comp_apply, eventually_atTop, ge_iff_le]
    use 1
    intro m hm
    have h0 : (ψ m : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_le_of_lt (_root_.zero_le _)
      (hψ_mono (Nat.pos_of_ne_zero (one_le_iff_ne_zero.mp hm)))))
    rw [← div_self h0, ← sub_div, cast_sub (hmu_le _)]
  have b_in : b ∈ Set.Icc (0 : ℝ) 1 := sub_mem_Icc a_in
  have hnu_le : ∀ n : ℕ, nu n ≤ n := fun n => by simp only [hnu, tsub_le_self]
  have hx : limsup (fun n : ℕ => f (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
      smoothingSeminorm' f x ^ a := limsup_mu_le f hf1 hmu_le hn a_in hψ_mono hψ_lim
  have hy : limsup (fun n : ℕ => f (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
      smoothingSeminorm' f y ^ b :=
    limsup_mu_le f hf1 hnu_le (exists_index_le f hna y x) b_in hψ_mono hb_lim
  have hxy : limsup
      (fun n : ℕ => f (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * f (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
      smoothingSeminorm' f x ^ a * smoothingSeminorm' f y ^ b := by
    have hxy' :
      limsup (fun n : ℕ => f (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * f (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)))
        atTop ≤ limsup (fun n : ℕ => f (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop *
          limsup (fun n : ℕ => f (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop :=
      limsup_mul_le (f_bddAbove f hf1 hmu_le x ψ) (fun n => rpow_nonneg (apply_nonneg _ _) _)
        (f_bddAbove f hf1 hnu_le y ψ) fun n => rpow_nonneg (apply_nonneg _ _) _
    have h_bdd : IsBoundedUnder LE.le atTop fun n : ℕ => f (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)) :=
      isBoundedUnder f hf1 hnu_le ψ
    exact le_trans hxy' (mul_le_mul hx hy (limsup_nonneg_of_nonneg h_bdd fun m =>
      rpow_nonneg (apply_nonneg _ _) _) (rpow_nonneg (smoothingSeminorm_nonneg f hf1 x) _))
  conv_lhs => simp only [smoothingSeminorm']
  apply le_of_forall_sub_le
  intro ε hε
  rw [sub_le_iff_le_add]
  have h_mul : smoothingSeminorm' f x ^ a * smoothingSeminorm' f y ^ b + ε ≤
      max (smoothingSeminorm' f x) (smoothingSeminorm' f y) + ε :=  by
    rw [max_def]
    split_ifs with h
    · rw [add_le_add_iff_right]
      apply le_trans (mul_le_mul_of_nonneg_right
        (rpow_le_rpow (smoothingSeminorm_nonneg f hf1 _) h a_in.1)
        (rpow_nonneg (smoothingSeminorm_nonneg f hf1 _) _))
      rw [hb, ← rpow_add_of_nonneg (smoothingSeminorm_nonneg f hf1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel_left, rpow_one]
    · rw [add_le_add_iff_right]
      apply le_trans (mul_le_mul_of_nonneg_left
        (rpow_le_rpow (smoothingSeminorm_nonneg f hf1 _) (le_of_lt (not_le.mp h)) b_in.1)
        (rpow_nonneg (smoothingSeminorm_nonneg f hf1 _) _))
      rw [hb, ← rpow_add_of_nonneg (smoothingSeminorm_nonneg f hf1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel_left, rpow_one]
  apply le_trans _ h_mul
  have hex : ∃ n : PNat, f (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * f (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)) <
      smoothingSeminorm' f x ^ a * smoothingSeminorm' f y ^ b + ε :=
    exists_lt_of_limsup_le (range_bddAbove_mul (f_bddAbove f hf1 hmu_le _ _)
        (fun n => rpow_nonneg (apply_nonneg _ _) _) (f_bddAbove f hf1 hnu_le _ _)
        fun n => rpow_nonneg (apply_nonneg _ _) _).isBoundedUnder_of_range hxy hε
  obtain ⟨N, hN⟩ := hex
  apply le_trans (ciInf_le (smoothingSeminorm_seq_bddBelow f _)
    ⟨ψ N, lt_of_le_of_lt (_root_.zero_le (ψ 0)) (hψ_mono.lt_iff_lt.mpr N.pos)⟩)
  apply le_trans _ hN.le
  simp only [PNat.mk_coe, hnu, ← mul_rpow (apply_nonneg f _) (apply_nonneg f _)]
  exact mu_property f hn (ψ N)

end IsNonarchimedean

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothingSeminorm'` is a ring seminorm. -/
def smoothingSeminorm (hf1 : f 1 ≤ 1) (hna : IsNonarchimedean f) : RingSeminorm R where
  toFun     := smoothingSeminorm' f
  map_zero' := by
    apply tendsto_nhds_unique_of_eventuallyEq (smoothingSeminorm'_isLimit f hf1 0)
      tendsto_const_nhds
    simp only [EventuallyEq, eventually_atTop, ge_iff_le]
    use 1
    intro n hn
    simp only [smoothingSeminormSeq]
    rw [zero_pow (pos_iff_ne_zero.mp hn), map_zero, zero_rpow]
    exact one_div_ne_zero (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn))
  add_le' := add_le_of_isNonarchimedean (smoothingSeminorm_nonneg f hf1)
      (smoothingSeminorm_isNonarchimedean f hf1 hna)
  neg' n := by
    simp only [smoothingSeminorm', smoothingSeminorm']
    congr
    ext n
    rw [neg_pow]
    rcases neg_one_pow_eq_or R n with hpos | hneg
    · rw [hpos, one_mul]
    · rw [hneg, neg_one_mul, map_neg_eq_map f]
  mul_le' x y := by
    apply le_of_tendsto_of_tendsto' (smoothingSeminorm'_isLimit f hf1 (x * y))
      (Tendsto.mul (smoothingSeminorm'_isLimit f hf1 x) (smoothingSeminorm'_isLimit f hf1 y))
    intro n
    have hn : 0 ≤ 1 / (n : ℝ) := by simp only [one_div, inv_nonneg, cast_nonneg]
    simp only [smoothingSeminormSeq]
    rw [← mul_rpow (apply_nonneg f _) (apply_nonneg f _), mul_pow]
    exact rpow_le_rpow (apply_nonneg f _) (map_mul_le_mul f _ _) hn

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothingSeminorm f hf1 hna 1 ≤ 1`. -/
theorem smoothingSeminorm_is_seminorm_is_norm_le_one_class (hf1 : f 1 ≤ 1)
    (hna : IsNonarchimedean f) : smoothingSeminorm f hf1 hna 1 ≤ 1 :=
  smoothingSeminorm_one f hf1

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothingSeminorm' f` is
  power-multiplicative. -/
theorem smoothingSeminorm_isPowMul (hf1 : f 1 ≤ 1) : IsPowMul (smoothingSeminorm' f) := by
  intro x m hm
  simp only [smoothingSeminorm']
  have hlim : Tendsto (fun n => smoothingSeminormSeq f x (m * n)) atTop
      (𝓝 (smoothingSeminorm' f x)) :=
    Tendsto.comp (smoothingSeminorm'_isLimit f hf1 x) (tendsto_atTop_atTop_of_monotone
      (fun n k hnk ↦ mul_le_mul_left' hnk m) (fun n ↦ ⟨n, le_mul_of_one_le_left' hm⟩))
  apply tendsto_nhds_unique _ (Tendsto.pow hlim m)
  have h_eq : ∀ n : ℕ, smoothingSeminormSeq f x (m * n) ^ m = smoothingSeminormSeq f (x ^ m) n := by
    have hm' : (m : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hm))
    intro n
    simp only [smoothingSeminormSeq]
    rw [pow_mul, ← rpow_natCast, ← rpow_mul (apply_nonneg f _), cast_mul, ← one_div_mul_one_div,
      mul_comm (1 / (m : ℝ)), mul_assoc, one_div_mul_cancel hm', mul_one]
  simp_rw [h_eq]
  exact smoothingSeminorm'_isLimit f hf1 _

/-- If `f 1 ≤ 1` and `∀ (1 ≤ n), f (x ^ n) = f x ^ n`, then `smoothingSeminorm' f x = f x`. -/
theorem smoothingSeminorm_of_powMul (hf1 : f 1 ≤ 1) {x : R}
    (hx : ∀ (n : ℕ) (_hn : 1 ≤ n), f (x ^ n) = f x ^ n) : smoothingSeminorm' f x = f x := by
  apply tendsto_nhds_unique_of_eventuallyEq (smoothingSeminorm'_isLimit f hf1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  have hn0 : (n : ℝ) ≠ 0 := cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)
  rw [hx n hn, ← rpow_natCast, ← rpow_mul (apply_nonneg f _), mul_one_div_cancel hn0, rpow_one]

/-- If `f 1 ≤ 1` and `∀ y : R, f (x * y) = f x * f y`, then `smoothingSeminorm' f x = f x`. -/
theorem smoothingSeminorm_apply_of_is_mul' (hf1 : f 1 ≤ 1) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : smoothingSeminorm' f x = f x := by
  apply tendsto_nhds_unique_of_eventuallyEq (smoothingSeminorm'_isLimit f hf1 x) tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  by_cases hx0 : f x = 0
  · have hxn : f (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg f _)
      apply le_trans (map_pow_le_pow f x (one_le_iff_ne_zero.mp hn))
      rw [hx0, zero_pow (pos_iff_ne_zero.mp hn)]
    rw [hx0, hxn, zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  · have h1 : f 1 = 1 := by rw [← mul_right_inj' hx0, ← hx 1, mul_one, mul_one]
    have hn0 : (n : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
    rw [← mul_one (x ^ n), is_mul_pow_of_is_mul f hx, ← rpow_natCast, h1, mul_one, ←
      rpow_mul (apply_nonneg f _), mul_one_div_cancel hn0, rpow_one]

/-- If `f 1 ≤ 1`, `f` is nonarchimedean, and `∀ y : R, f (x * y) = f x * f y`, then
  `smoothingSeminorm f hf1 hna x = f x`. -/
theorem smoothingSeminorm_apply_of_is_mul (hf1 : f 1 ≤ 1) (hna : IsNonarchimedean f) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : smoothingSeminorm f hf1 hna x = f x :=
  smoothingSeminorm_apply_of_is_mul' f hf1 hx

/-- If `f 1 ≤ 1`, and `x` is multiplicative for `f`, then it is multiplicative for
  `smoothingSeminorm'`. -/
theorem smoothingSeminorm_of_mul' (hf1 : f 1 ≤ 1) {x : R} (hx : ∀ y : R, f (x * y) = f x * f y)
    (y : R) : smoothingSeminorm' f (x * y) = smoothingSeminorm' f x * smoothingSeminorm' f y := by
  have hlim : Tendsto (fun n => f x * smoothingSeminormSeq f y n) atTop
      (𝓝 (smoothingSeminorm' f x * smoothingSeminorm' f y)) := by
    rw [smoothingSeminorm_apply_of_is_mul' f hf1 hx]
    exact Tendsto.const_mul _ (smoothingSeminorm'_isLimit f hf1 y)
  apply tendsto_nhds_unique_of_eventuallyEq (smoothingSeminorm'_isLimit f hf1 (x * y)) hlim
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  use 1
  intro n hn1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hn1))
  simp only [smoothingSeminormSeq]
  rw [mul_pow, is_mul_pow_of_is_mul f hx,
    mul_rpow (pow_nonneg (apply_nonneg f _) _) (apply_nonneg f _), ← rpow_natCast, ←
    rpow_mul (apply_nonneg f _), mul_one_div_cancel hn0, rpow_one]

/-- If `f 1 ≤ 1`, `f` is nonarchimedean, and `x` is multiplicative for `f`, then `x` is
  multiplicative for `smoothingSeminorm`. -/
theorem smoothingSeminorm_of_mul (hf1 : f 1 ≤ 1) (hna : IsNonarchimedean f) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    smoothingSeminorm f hf1 hna (x * y) =
      smoothingSeminorm f hf1 hna x * smoothingSeminorm f hf1 hna y :=
  smoothingSeminorm_of_mul' f hf1 hx y

end smoothingSeminorm
