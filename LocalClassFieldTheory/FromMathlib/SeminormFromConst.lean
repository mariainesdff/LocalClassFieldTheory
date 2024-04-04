/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import LocalClassFieldTheory.FromMathlib.Filter
import LocalClassFieldTheory.FromMathlib.RingSeminorm

#align_import from_mathlib.seminorm_from_const

/-!
# seminorm_from_const

In this file, we prove [BGR, Proposition 1.3.2/2] : starting from a power-multiplicative seminorm
on a commutative ring `R` and a nonzero `c : R`, we create a new power-multiplicative seminorm for
which `c` is multiplicative.

## Main Definitions

* `seminorm_from_const'` : the real-valued function sending `x ∈ R` to the limit of
  `(f (x * c^n))/((f c)^n)`.
* `seminorm_from_const` : the function `seminorm_from_const'` is a `ring_seminorm` on `R`.


## Main Results
* `seminorm_from_const_is_nonarchimedean` : the function `seminorm_from_const' hf1 hc hpm`
  is nonarchimedean when f is nonarchimedean.
* `seminorm_from_const_is_pow_mul` : the function `seminorm_from_const' hf1 hc hpm`
  is power-multiplicative.
* `seminorm_from_const_c_is_mul` : for every `x : R`, `seminorm_from_const' hf1 hc hpm (c * x)`
  equals the product `seminorm_from_const' hf1 hc hpm c * seminorm_from_const' hf1 hc hpm x`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

seminorm_from_const, seminorm, nonarchimedean
-/


noncomputable section

open scoped Topology

section Ring

variable {R : Type _} [CommRing R] (c : R) (f : RingSeminorm R) (hf1 : f 1 ≤ 1) (hc : 0 ≠ f c)
  (hpm : IsPowMul f)

/-- For a ring seminorm `f` on `R` and `c ∈ R`, the sequence given by `(f (x * c^n))/((f c)^n)`. -/
def seminormFromConst_seq (x : R) : ℕ → ℝ := fun n => f (x * c ^ n) / f c ^ n

lemma seminormFromConst_seq_def (x : R) :
  seminormFromConst_seq c f x = fun n => f (x * c ^ n) / f c ^ n := rfl


/-- The terms in the sequence `seminorm_from_const_seq c f x` are nonnegative. -/
theorem seminormFromConst_seq_nonneg (x : R) (n : ℕ) : 0 ≤ seminormFromConst_seq c f x n :=
  div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

/-- The image of `seminorm_from_const_seq c f x` is bounded below by zero. -/
theorem seminorm_from_const_is_bounded (x : R) :
    BddBelow (Set.range (seminormFromConst_seq c f x)) := by
  use 0
  rw [mem_lowerBounds]
  intro r hr
  obtain ⟨n, hn⟩ := hr
  rw [← hn]
  exact seminormFromConst_seq_nonneg c f x n

variable {f}

/-- `seminorm_from_const_seq c f 0` is the constant sequence zero. -/
theorem seminormFromConst_seq_zero (hf : f 0 = 0) : seminormFromConst_seq c f 0 = 0 := by
  rw [seminormFromConst_seq_def]
  ext n
  rw [MulZeroClass.zero_mul, hf, zero_div]
  rfl

variable {c}

/-- If `1 ≤ n`, then `seminorm_from_const_seq c f 1 n = 1`. -/
theorem seminormFromConst_seq_one (n : ℕ) (hn : 1 ≤ n) : seminormFromConst_seq c f 1 n = 1 := by
  simp only [seminormFromConst_seq]
  rw [one_mul, hpm _ hn, div_self (pow_ne_zero n (Ne.symm hc))]

/-- `seminorm_from_const_seq c f x` is antitone. -/
theorem seminormFromConst_seq_antitone (x : R) : Antitone (seminormFromConst_seq c f x) :=
  by
  intro m n hmn
  simp only [seminormFromConst_seq]
  nth_rw 1 [← Nat.add_sub_of_le hmn]
  rw [pow_add, ← mul_assoc]
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc
  apply le_trans ((div_le_div_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _))
  by_cases heq : m = n
  · have : n - m = 0 := by rw [heq]; exact Nat.sub_self n
    rw [this, heq, div_le_div_right (pow_pos hc_pos _), pow_zero]
    conv_rhs => rw [← mul_one (f (x * c ^ n))]
    exact mul_le_mul_of_nonneg_left hf1 (apply_nonneg f _)
  · have h1 : 1 ≤ n - m :=
      by
      rw [Nat.one_le_iff_ne_zero, Ne.def, Nat.sub_eq_zero_iff_le, not_le]
      exact lt_of_le_of_ne hmn heq
    rw [hpm c h1, mul_div_assoc, div_eq_mul_inv, pow_sub₀ _ (Ne.symm hc) hmn, mul_assoc,
      mul_comm (f c ^ m)⁻¹, ← mul_assoc (f c ^ n), mul_inv_cancel (pow_ne_zero n (Ne.symm hc)),
      one_mul, div_eq_mul_inv]

/-- The real-valued function sending `x ∈ R` to the limit of `(f (x * c^n))/((f c)^n)`. -/
def seminormFromConst' (x : R) : ℝ := Classical.choose
  (Real.tendsto_of_is_bounded_antitone (seminorm_from_const_is_bounded c f x)
    (seminormFromConst_seq_antitone hf1 hc hpm x))

/-- We prove that `seminorm_from_const' hf1 hc hpm x` is the limit of the sequence
  `seminorm_from_const_seq c f x` as `n` tends to infinity. -/
theorem seminorm_from_const_is_limit (x : R) :
    Filter.Tendsto (seminormFromConst_seq c f x) Filter.atTop
      (𝓝 (seminormFromConst' hf1 hc hpm x)) :=
  Classical.choose_spec
    (Real.tendsto_of_is_bounded_antitone (seminorm_from_const_is_bounded c f x)
      (seminormFromConst_seq_antitone hf1 hc hpm x))

/-- `seminorm_from_const' hf1 hc hpm 0 = 0`. -/
theorem seminorm_from_const_zero : seminormFromConst' hf1 hc hpm 0 = 0 :=
  tendsto_nhds_unique (seminorm_from_const_is_limit hf1 hc hpm 0)
    (by simpa [seminormFromConst_seq_zero c (map_zero _)] using tendsto_const_nhds)

/-- `seminorm_from_const' hf1 hc hpm 1 = 1`. -/
theorem seminorm_from_const_is_norm_one_class : seminormFromConst' hf1 hc hpm 1 = 1 := by
  apply tendsto_nhds_unique_of_eventuallyEq (seminorm_from_const_is_limit hf1 hc hpm 1)
    tendsto_const_nhds
  simp only [Filter.EventuallyEq, Filter.eventually_atTop, ge_iff_le]
  exact ⟨1, seminormFromConst_seq_one hc hpm⟩

/-- `seminorm_from_const' hf1 hc hpm` is submultiplicative. -/
theorem seminorm_from_const_hMul (x y : R) :
    seminormFromConst' hf1 hc hpm (x * y) ≤
      seminormFromConst' hf1 hc hpm x * seminormFromConst' hf1 hc hpm y := by
  have hlim : Filter.Tendsto (fun n => seminormFromConst_seq c f (x * y) (2 * n)) Filter.atTop
      (𝓝 (seminormFromConst' hf1 hc hpm (x * y))) := by
    refine' Filter.Tendsto.comp (seminorm_from_const_is_limit hf1 hc hpm (x * y)) _
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro n m hnm; simp only [mul_le_mul_left, Nat.succ_pos', hnm]
    · rintro n; use n; linarith
  apply le_of_tendsto_of_tendsto' hlim
    (Filter.Tendsto.mul (seminorm_from_const_is_limit hf1 hc hpm x)
      (seminorm_from_const_is_limit hf1 hc hpm y))
  intro n
  simp only [seminormFromConst_seq]
  rw [div_mul_div_comm, ← pow_add, two_mul,
    div_le_div_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc) _), pow_add, ← mul_assoc,
    mul_comm (x * y), ← mul_assoc, mul_assoc, mul_comm (c ^ n)]
  exact map_mul_le_mul f (x * c ^ n) (y * c ^ n)

/-- `seminorm_from_const' hf1 hc hpm` is invariant under negation of `x`. -/
theorem seminorm_from_const_neg (x : R) :
    seminormFromConst' hf1 hc hpm (-x) = seminormFromConst' hf1 hc hpm x := by
  apply tendsto_nhds_unique_of_eventuallyEq (seminorm_from_const_is_limit hf1 hc hpm (-x))
    (seminorm_from_const_is_limit hf1 hc hpm x)
  simp only [Filter.EventuallyEq, Filter.eventually_atTop]
  use 0
  intro n _hn
  simp only [seminormFromConst_seq]
  rw [neg_mul, map_neg_eq_map]

/-- `seminorm_from_const' hf1 hc hpm` satisfies the triangle inequality. -/
theorem seminorm_from_const_add (x y : R) :
    seminormFromConst' hf1 hc hpm (x + y) ≤
      seminormFromConst' hf1 hc hpm x + seminormFromConst' hf1 hc hpm y := by
  apply le_of_tendsto_of_tendsto' (seminorm_from_const_is_limit hf1 hc hpm (x + y))
      (Filter.Tendsto.add (seminorm_from_const_is_limit hf1 hc hpm x)
        (seminorm_from_const_is_limit hf1 hc hpm y))
  intro n
  have h_add : f ((x + y) * c ^ n) ≤ f (x * c ^ n) + f (y * c ^ n) := by
    rw [add_mul]
    exact map_add_le_add f _ _
  simp only [seminormFromConst_seq]
  rw [div_add_div_same]
  exact (div_le_div_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc) _)).mpr h_add

/-- The function `seminorm_from_const` is a `ring_seminorm` on `R`. -/
def seminormFromConst : RingSeminorm R where
  toFun     := seminormFromConst' hf1 hc hpm
  map_zero' := seminorm_from_const_zero hf1 hc hpm
  add_le'   := seminorm_from_const_add hf1 hc hpm
  neg'      := seminorm_from_const_neg hf1 hc hpm
  mul_le'   := seminorm_from_const_hMul hf1 hc hpm

theorem seminormFromConst_def (x : R) :
    seminormFromConst hf1 hc hpm x = seminormFromConst' hf1 hc hpm x :=
  rfl

/-- `seminorm_from_const' hf1 hc hpm 1 ≤ 1`. -/
theorem seminorm_from_const_is_norm_le_one_class : seminormFromConst' hf1 hc hpm 1 ≤ 1 :=
  le_of_eq (seminorm_from_const_is_norm_one_class hf1 hc hpm)

/-- The function `seminorm_from_const' hf1 hc hpm` is nonarchimedean. -/
theorem seminorm_from_const_isNonarchimedean (hna : IsNonarchimedean f) :
    IsNonarchimedean (seminormFromConst' hf1 hc hpm) := by
  intro x y
  apply le_of_tendsto_of_tendsto' (seminorm_from_const_is_limit hf1 hc hpm (x + y))
      (Filter.Tendsto.max (seminorm_from_const_is_limit hf1 hc hpm x)
        (seminorm_from_const_is_limit hf1 hc hpm y))
  intro n
  have hmax : f ((x + y) * c ^ n) ≤ max (f (x * c ^ n)) (f (y * c ^ n)) := by
    rw [add_mul]
    exact hna _ _
  rw [le_max_iff] at hmax ⊢
  cases' hmax with hmax hmax <;> [left; right] <;>
    exact (div_le_div_right (pow_pos (lt_of_le_of_ne (apply_nonneg f c) hc) _)).mpr hmax

/-- The function `seminorm_from_const' hf1 hc hpm` is power-multiplicative. -/
theorem seminorm_from_const_isPowMul : IsPowMul (seminormFromConst' hf1 hc hpm) := by
  intro x m hm
  simp only [seminormFromConst']
  have hlim : Filter.Tendsto (fun n => seminormFromConst_seq c f (x ^ m) (m * n)) Filter.atTop
      (𝓝 (seminormFromConst' hf1 hc hpm (x ^ m))) := by
    refine' Filter.Tendsto.comp (seminorm_from_const_is_limit hf1 hc hpm (x ^ m)) _
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro n k hnk; exact mul_le_mul_left' hnk m
    · rintro n; use n; exact le_mul_of_one_le_left' hm
  apply tendsto_nhds_unique hlim
  convert Filter.Tendsto.pow (seminorm_from_const_is_limit hf1 hc hpm x) m using 1
  ext n
  simp only [seminormFromConst_seq]
  rw [div_pow, ← hpm _ hm, ← pow_mul, mul_pow, ← pow_mul, mul_comm m n]

/-- The function `seminorm_from_const' hf1 hc hpm` is bounded above by `x`. -/
theorem seminorm_from_const_le_seminorm (x : R) : seminormFromConst' hf1 hc hpm x ≤ f x :=
  by
  apply le_of_tendsto (seminorm_from_const_is_limit hf1 hc hpm x)
  simp only [Filter.eventually_atTop, ge_iff_le]
  use 1
  rintro n hn
  apply le_trans ((div_le_div_right (pow_pos (lt_of_le_of_ne (apply_nonneg f c) hc) _)).mpr
    (map_mul_le_mul _ _ _))
  rw [hpm c hn, mul_div_assoc, div_self (pow_ne_zero n hc.symm), mul_one]

/-- If `x : R` is multiplicative for `f`, then `seminorm_from_const' hf1 hc hpm x = f x`. -/
theorem seminorm_from_const_apply_of_is_hMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
    seminormFromConst' hf1 hc hpm x = f x :=
  haveI hlim : Filter.Tendsto (seminormFromConst_seq c f x) Filter.atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f x = fun _n => f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq]
        rw [hn, pow_zero, pow_zero, mul_one, div_one]
      · simp only [seminormFromConst_seq]
        rw [hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn), mul_div_assoc,
          div_self (pow_ne_zero n hc.symm), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (seminorm_from_const_is_limit hf1 hc hpm x) hlim

/-- If `x : R` is multiplicative for `f`, then it is multiplicative for
  `seminorm_from_const' hf1 hc hpm`. -/
theorem seminorm_from_const_is_hMul_of_is_hMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y)
    (y : R) :
    seminormFromConst' hf1 hc hpm (x * y) =
      seminormFromConst' hf1 hc hpm x * seminormFromConst' hf1 hc hpm y :=
  haveI hlim :
    Filter.Tendsto (seminormFromConst_seq c f (x * y)) Filter.atTop
      (𝓝 (seminormFromConst' hf1 hc hpm x * seminormFromConst' hf1 hc hpm y)) := by
    rw [seminorm_from_const_apply_of_is_hMul hf1 hc hpm hx]
    have hseq : seminormFromConst_seq c f (x * y) =
      fun n => f x * seminormFromConst_seq c f y n := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_assoc, hx, mul_div_assoc]
    simpa [hseq] using Filter.Tendsto.const_mul _ (seminorm_from_const_is_limit hf1 hc hpm y)
  tendsto_nhds_unique (seminorm_from_const_is_limit hf1 hc hpm (x * y)) hlim

/-- `seminorm_from_const' hf1 hc hpm c = f c`. -/
theorem seminorm_from_const_apply_c : seminormFromConst' hf1 hc hpm c = f c :=
  haveI hlim : Filter.Tendsto (seminormFromConst_seq c f c) Filter.atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f c = fun _n => f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm, ← pow_succ, hpm _ le_add_self, pow_succ, mul_comm,  mul_div_assoc,
        div_self (pow_ne_zero n hc.symm), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (seminorm_from_const_is_limit hf1 hc hpm c) hlim

/-- For every `x : R`, `seminorm_from_const' hf1 hc hpm (c * x)` equals the product
  `seminorm_from_const' hf1 hc hpm c * seminorm_from_const' hf1 hc hpm x`. -/
theorem seminorm_from_const_c_is_mul (x : R) :
    seminormFromConst' hf1 hc hpm (c * x) =
      seminormFromConst' hf1 hc hpm c * seminormFromConst' hf1 hc hpm x := by
  have hlim :
    Filter.Tendsto (fun n => seminormFromConst_seq c f x (n + 1)) Filter.atTop
      (𝓝 (seminormFromConst' hf1 hc hpm x)) := by
    refine' Filter.Tendsto.comp (seminorm_from_const_is_limit hf1 hc hpm x) _
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro n m hnm
      exact add_le_add_right hnm 1
    · rintro n; use n; linarith
  rw [seminorm_from_const_apply_c hf1 hc hpm]
  apply tendsto_nhds_unique (seminorm_from_const_is_limit hf1 hc hpm (c * x))
  have hterm : seminormFromConst_seq c f (c * x) =
      fun n => f c * seminormFromConst_seq c f x (n + 1) := by
    simp only [seminormFromConst_seq_def]
    ext n
    ring_nf
    rw [mul_assoc _ (f c), mul_inv_cancel hc.symm, mul_one]
  simpa [hterm] using Filter.Tendsto.mul tendsto_const_nhds hlim

end Ring

section Field

variable {K : Type _} [Field K]

/-- If `K` is a field, the function `seminorm_from_const` is a `ring_norm` on `K`. -/
def seminormFromConstRingNormOfField {k : K} {g : RingSeminorm K} (hg1 : g 1 ≤ 1) (hg_k : g k ≠ 0)
    (hg_pm : IsPowMul g) : RingNorm K :=
  (seminormFromConst hg1 hg_k.symm hg_pm).toRingNorm
    (RingSeminorm.ne_zero_iff.mpr
      ⟨k, by simpa [seminormFromConst_def, seminorm_from_const_apply_c] using hg_k⟩)

theorem seminormFromConstRingNormOfField_def {k : K} {g : RingSeminorm K} (hg1 : g 1 ≤ 1)
    (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) (x : K) :
    seminormFromConstRingNormOfField hg1 hg_k hg_pm x = seminormFromConst' hg1 hg_k.symm hg_pm x :=
  rfl

end Field
