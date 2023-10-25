import Mathlib.Algebra.Group.WithOne.Units
import Mathlib.Data.Real.Nnreal
import Mathlib.Logic.Equiv.TransferInstance
import Mathlib.RingTheory.Valuation.Basic

#align_import for_mathlib.with_zero

/-!
# with_zero

In this file we provide some basic API lemmas for the `with_zero` construction and we define
the morphism `with_zero_mult_int_to_nnreal`.

## Main Definitions

* `with_zero_mult_int_to_nnreal` : The `monoid_with_zero_hom` from `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(multiplicative.to_add (with_zero.unzero hx)` when `x ≠ 0`, for a nonzero `e : ℝ≥0`.

## Main Results

* `with_zero_mult_int_to_nnreal_strict_mono` : The map `with_zero_mult_int_to_nnreal` is strictly
   monotone whenever `1 < e`.


## Tags

with_zero, multiplicative, nnreal
-/


noncomputable section

open scoped DiscreteValuation NNReal

open Multiplicative WithZero Equiv

namespace Multiplicative

theorem ofAdd_pow_comm (a b : ℤ) : ofAdd a ^ b = ofAdd b ^ a := by
  rw [← Int.ofAdd_mul, mul_comm, Int.ofAdd_mul]

theorem ofAdd_inj {x y : Multiplicative ℤ} (hxy : ofAdd x = ofAdd y) : x = y :=
  hxy

end Multiplicative

namespace WithZero

theorem ofAdd_zpow (n : ℤ) : (ofAdd n : ℤₘ₀) = ofAdd (1 : ℤ) ^ n := by
  rw [← WithZero.coe_zpow, WithZero.coe_inj, ← Int.ofAdd_mul, one_mul]

theorem ofAdd_pow_pow_comm (a b c : ℤ) :
    ((ofAdd (a : ℤ) : ℤₘ₀) ^ b) ^ c = (ofAdd (a : ℤ) ^ c) ^ b :=
  by
  simp only [← WithZero.coe_zpow]
  rw [← zpow_mul, mul_comm, zpow_mul]

theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((ofAdd (-1 : ℤ) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  rw [WithZero.ofAdd_zpow (-1), ← zpow_mul, neg_mul, one_mul, neg_neg, ← zpow_ofNat,
    of_add_pow_pow_comm 1 a, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul]

instance : Nontrivial ℤₘ₀ˣ :=
  haveI : Nontrivial (Multiplicative ℤ) := instNontrivialMultiplicative
  units_with_zero_equiv.toEquiv.Nontrivial

theorem one_lt_zpow' {α : Type _} [LinearOrderedCommGroupWithZero α] {a : α} (ha : 1 < a) {k : ℤ}
    (hk : 0 < k) : 1 < a ^ k := by
  lift k to ℕ using Int.le_of_lt hk
  rw [zpow_ofNat]
  exact one_lt_pow' ha (int.coe_nat_pos.mp hk).ne'

theorem hMul_lt_hMul_right₀ {α : Type _} {a b c : α} [LinearOrderedCommGroupWithZero α]
    (hc : 0 < c) : a * c < b * c ↔ a < b :=
  by
  rw [mul_comm a, mul_comm b]
  exact
    ⟨fun h => lt_of_mul_lt_mul_of_le₀ h hc (le_refl _), fun h =>
      mul_lt_mul_of_lt_of_le₀ (le_refl _) (ne_of_gt hc) h⟩

theorem lt_hMul_left₀ {α : Type _} {b c : α} [LinearOrderedCommGroupWithZero α] {a : α} (h : b < c)
    (ha : a ≠ 0) : a * b < a * c := by simpa only [mul_comm a _] using mul_lt_right₀ a h ha

theorem one_lt_div' {α : Type _} [LinearOrderedCommGroupWithZero α] (a : α) {b : α} (hb : b ≠ 0) :
    1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_right₀ (zero_lt_iff.mpr hb), one_mul, div_eq_mul_inv, inv_mul_cancel_right₀ hb]

open scoped DiscreteValuation

theorem strictMonoOn_zpow {n : ℤ} (hn : 0 < n) : StrictMonoOn (fun x : ℤₘ₀ => x ^ n) (Set.Ioi 0) :=
  fun a ha b hb hab => by
  simp only [Set.mem_Ioi] at ha hb
  have ha0 : a ≠ 0 := ne_of_gt ha
  have han : a ^ n ≠ 0 := by
    rw [WithZero.ne_zero_iff_exists] at ha0 ⊢
    obtain ⟨x, hx⟩ := ha0
    exact ⟨x ^ n, by rw [← hx, WithZero.coe_zpow]⟩
  simp only [← one_lt_div' _ han, ← div_zpow]
  exact one_lt_zpow' ((one_lt_div' _ ha0).mpr hab) hn

theorem zpow_left_injOn {n : ℤ} (hn : n ≠ 0) : Set.InjOn (fun _x : ℤₘ₀ => _x ^ n) (Set.Ioi 0) :=
  by
  cases hn.symm.lt_or_lt
  · exact (strict_mono_on_zpow h).InjOn
  · refine' fun a ha b hb (hab : a ^ n = b ^ n) =>
      (strict_mono_on_zpow (neg_pos.mpr h)).InjOn ha hb _
    simp only [zpow_neg, zpow_neg, hab]

theorem zpow_left_inj {n : ℤ} {a b : ℤₘ₀} (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b :=
  Set.InjOn.eq_iff (zpow_left_injOn hn) (Set.mem_Ioi.mpr (zero_lt_iff.mpr ha))
    (Set.mem_Ioi.mpr (zero_lt_iff.mpr hb))

theorem ofAdd_neg_nat (n : ℕ) : (ofAdd (-n : ℤ) : ℤₘ₀) = ofAdd (-1 : ℤ) ^ n := by
  rw [← WithZero.coe_pow, WithZero.coe_inj, ← one_mul (n : ℤ), ← neg_mul, Int.ofAdd_mul, zpow_ofNat]

theorem ofAdd_neg_one_lt_one : (Multiplicative.ofAdd (-1 : ℤ) : ℤₘ₀) < (1 : ℤₘ₀) :=
  by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero]
  exact neg_one_lt_zero

theorem lt_succ_iff_le (x : ℤₘ₀) (m : ℤ) : x < (ofAdd (m + 1) : ℤₘ₀) ↔ x ≤ (ofAdd m : ℤₘ₀) :=
  by
  by_cases hx : x = 0
  · simpa only [hx, zero_le', iff_true_iff, zero_lt_iff] using WithZero.coe_ne_zero
  · obtain ⟨γ, rfl⟩ := with_zero.ne_zero_iff_exists.mp hx
    rw [coe_le_coe, coe_lt_coe, ← to_add_le, ← to_add_lt, toAdd_ofAdd, toAdd_ofAdd]
    exact ⟨Int.le_of_lt_add_one, Int.lt_add_one_of_le⟩

end WithZero

/-- Given `e : ℝ≥0`, we define a map `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(multiplicative.to_add (with_zero.unzero hx)` when `x ≠ 0`.
  We regard this map as an inclusion of `ℤₘ₀` in `ℝ≥0`. -/
def withZeroMultIntToNnrealDef (e : NNReal) : ℤₘ₀ → ℝ≥0 := fun x =>
  if hx : x = 0 then 0 else e ^ Multiplicative.toAdd (WithZero.unzero hx)

open WithZero

/-- Given a nonzero `e : ℝ≥0`, this is the map `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(multiplicative.to_add (with_zero.unzero hx)` when `x ≠ 0` as a `monoid_with_zero_hom`. -/
def withZeroMultIntToNnreal {e : NNReal} (he : e ≠ 0) : ℤₘ₀ →*₀ ℝ≥0
    where
  toFun := withZeroMultIntToNnrealDef e
  map_zero' := by simp only [withZeroMultIntToNnrealDef]; rw [dif_pos]; rfl
  map_one' := by
    simp only [withZeroMultIntToNnrealDef]; rw [dif_neg]
    · simp only [unzero_coe, toAdd_one, zpow_zero]
    · exact NeZero.ne 1
  map_mul' x y := by
    simp only [withZeroMultIntToNnrealDef]
    by_cases hxy : x * y = 0
    · cases' zero_eq_mul.mp (Eq.symm hxy) with hx hy
      --either x = 0 or y = 0
      · rw [dif_pos hxy, dif_pos hx, MulZeroClass.zero_mul]
      · rw [dif_pos hxy, dif_pos hy, MulZeroClass.mul_zero]
    · cases' mul_ne_zero_iff.mp hxy with hx hy
      --  x ≠ 0 and y ≠ 0
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (Or.inl he)]
      apply congr_arg
      rw [← toAdd_mul]
      apply congr_arg
      rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]

/-- `with_zero_mult_int_to_nnreal` sends nonzero elements to nonzero elements. -/
theorem withZeroMultIntToNnreal_ne_zero {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
    withZeroMultIntToNnreal he m ≠ 0 := by
  simpa only [withZeroMultIntToNnreal, withZeroMultIntToNnrealDef, MonoidWithZeroHom.coe_mk,
    dif_neg hm] using zpow_ne_zero _ he

/-- `with_zero_mult_int_to_nnreal` sends nonzero elements to positive elements. -/
theorem withZeroMultIntToNnreal_pos {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
    0 < withZeroMultIntToNnreal he m :=
  lt_of_le_of_ne zero_le' (withZeroMultIntToNnreal_ne_zero he hm).symm

/-- The map `with_zero_mult_int_to_nnreal` is strictly monotone whenever `1 < e`. -/
theorem withZeroMultIntToNnreal_strictMono {e : NNReal} (he : 1 < e) :
    StrictMono (withZeroMultIntToNnreal (ne_zero_of_lt he)) :=
  by
  intro x y hxy
  simp only [withZeroMultIntToNnreal, withZeroMultIntToNnrealDef, MonoidWithZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp only [hy, not_lt_zero'] at hxy ; exfalso; exact hxy
  · apply NNReal.zpow_pos (ne_zero_of_lt he)
  · simp only [hy, not_lt_zero'] at hxy ; exfalso; exact hxy
  · rw [zpow_lt_iff_lt he, Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero hx,
      WithZero.coe_unzero hy]
    exact hxy
