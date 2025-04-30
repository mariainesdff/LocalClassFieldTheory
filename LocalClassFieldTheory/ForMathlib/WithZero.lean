/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Data.NNReal.Defs

/-!
# WithZero

In this file we provide some basic API lemmas for the `WithZero` construction and we define
the morphism `WithZeroMulInt.toNNReal`.

## Main Definitions

* `WithZeroMulInt.toNNReal` : The `MonoidWithZeroHom` from `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(Multiplicative.toAdd (WithZero.unzero hx)` when `x ≠ 0`, for a nonzero `e : ℝ≥0`.

## Main Results

* `WithZeroMulInt.toNNReal_strictMono` : The map `WithZeroMulInt.toNNReal` is strictly
   monotone whenever `1 < e`.


## Tags

WithZero, multiplicative, nnreal
-/


noncomputable section

open scoped Multiplicative NNReal

open Multiplicative WithZero Equiv

-- Most of what follows is in **PR #23177**
namespace Multiplicative

-- Mathlib.Algebra.Ring.Int
theorem ofAdd_pow_comm (a b : ℤ) : ofAdd a ^ b = ofAdd b ^ a := by
  rw [← Int.ofAdd_mul, mul_comm, Int.ofAdd_mul]

-- [Mathlib.Algebra.Group.TypeTags]
-- theorem ofAdd_inj {x y : Multiplicative ℤ} (hxy : ofAdd x = ofAdd y) : x = y := hxy

end Multiplicative

namespace WithZero

-- In PR #21370
/- theorem ofAdd_zpow (n : ℤ) : (↑(ofAdd n) : ℤₘ₀) = ofAdd (1 : ℤ) ^ n := by
  rw [← WithZero.coe_zpow, WithZero.coe_inj, ← Int.ofAdd_mul, one_mul] -/

-- In PR #21370
/- theorem ofAdd_zpow_zpow_comm (a b c : ℤ) : ((↑(ofAdd a) : ℤₘ₀) ^ b) ^ c = (ofAdd (a : ℤ) ^ c) ^ b := by
  simp only [← WithZero.coe_zpow]
  rw [← zpow_mul, mul_comm, zpow_mul] -/

-- In PR #21370
/- theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  rw [ofAdd_zpow (-1)]
  simp only [zpow_neg, zpow_one, inv_zpow', inv_inv, coe_zpow]
  rw [← zpow_natCast, ofAdd_zpow_zpow_comm, ← ofAdd_zpow] -/

-- Q: where?
-- **In PR #23177**
instance (α : Type*) [Group α] [Nontrivial α] : Nontrivial (WithZero α)ˣ := (unitsWithZeroEquiv).toEquiv.nontrivial
-- instance : Nontrivial ℤₘ₀ˣ := inferInstance

-- [Mathlib.SetTheory.Cardinal.Basic, Mathlib.Data.ENat.Basic, Mathlib.Algebra.Order.Nonneg.Field,
--Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
-- **In PR #23177**
lemma one_lt_zpow {G : Type*} [DivInvMonoid G] [Preorder G] [MulLeftMono G] {a : G} (ha : 1 < a) {k : ℤ}
    (hk : 0 < k) : 1 < a ^ k := by
  lift k to ℕ using Int.le_of_lt hk
  rw [zpow_natCast]
  exact one_lt_pow' ha (Int.natCast_pos.mp hk).ne'

-- [Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
-- **In PR #23177**
theorem lt_succ_iff_le (x : ℤₘ₀) (m : ℤ) :
    x < (↑(ofAdd (m + 1)) : ℤₘ₀) ↔ x ≤ (↑(ofAdd m) : ℤₘ₀) := by
  by_cases hx : x = 0
  · simpa only [hx, zero_le', iff_true, zero_lt_iff] using WithZero.coe_ne_zero
  · obtain ⟨γ, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
    rw [coe_le_coe, coe_lt_coe, ← toAdd_le, ← toAdd_lt, toAdd_ofAdd, toAdd_ofAdd]
    exact ⟨Int.le_of_lt_add_one, Int.lt_add_one_of_le⟩

-- theorem one_lt_zpow {α : Type _} [LinearOrderedCommGroupWithZero α] {a : α} (ha : 1 < a) {k : ℤ}
--     (hk : 0 < k) : 1 < a ^ k := by apply foo α ha hk
--   -- lift k to ℕ using Int.le_of_lt hk
--   -- rw [zpow_natCast]
--   -- exact one_lt_pow' ha (Int.natCast_pos.mp hk).ne'

    -- fun h ↦ mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hc (le_refl _) (ne_of_gt hc)⟩
--[Mathlib.Algebra.Order.GroupWithZero.Canonical]
-- *FAE* The lemma below was used only once and was basically already in mathlib: removed
-- theorem lt_mul_left₀ {α : Type _} {b c : α} [LinearOrderedCommGroupWithZero α] {a : α} (h : b < c)
--     (ha : a ≠ 0) : a * b < a * c := by simpa only [mul_comm a _] using mul_lt_right₀ a h ha

-- [Mathlib.Algebra.Order.GroupWithZero.Canonical]
-- **In PR #23177**
theorem mul_lt_mul_right₀ {α : Type*} {a b c : α} [LinearOrderedCommGroupWithZero α]
    (hc : 0 < c) : a * c < b * c ↔ a < b := by
  rw [mul_comm a, mul_comm b]
  exact mul_lt_mul_left hc

-- **In PR #23177**
theorem one_lt_div' {α : Type*} [LinearOrderedCommGroupWithZero α] (a : α) {b : α} (hb : b ≠ 0) :
    1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_right₀ (zero_lt_iff.mpr hb), one_mul, div_eq_mul_inv, inv_mul_cancel_right₀ hb]

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

-- **In PR #23177**
theorem strictMonoOn_zpow {n : ℤ} (hn : 0 < n) :
    StrictMonoOn (fun x : (WithZero α) ↦ x ^ n) (Set.Ioi 0) :=
  fun a ha b _ hab ↦ by
    have ha0 : a ≠ 0 := ne_of_gt ha
    have han : a ^ n ≠ 0 := by
      rw [WithZero.ne_zero_iff_exists] at ha0 ⊢
      obtain ⟨x, hx⟩ := ha0
      exact ⟨x ^ n, by rw [← hx, WithZero.coe_zpow]⟩
    simp only [← one_lt_div' (b^n) han, ← div_zpow]
    exact one_lt_zpow ((one_lt_div' _ ha0).mpr hab) hn


-- **In PR #23177**
theorem zpow_left_injOn {n : ℤ} (hn : n ≠ 0) :
    Set.InjOn (fun x : (WithZero α) ↦ x ^ n) (Set.Ioi 0) := by
  rcases hn.symm.lt_or_lt with h | h
  · exact (strictMonoOn_zpow h).injOn
  · refine fun a ha b hb (hab : a ^ n = b ^ n) ↦ (strictMonoOn_zpow (neg_pos.mpr h)).injOn ha hb ?_
    simp only [zpow_neg, zpow_neg, hab]

-- **In PR #23177**
theorem zpow_left_inj {n : ℤ} {a b : WithZero α}
    (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  Set.InjOn.eq_iff (zpow_left_injOn hn) (Set.mem_Ioi.mpr (zero_lt_iff.mpr ha))
    (Set.mem_Ioi.mpr (zero_lt_iff.mpr hb))


-- **In PR #23177**
theorem ofAdd_neg_nat (n : ℕ) : (↑(ofAdd (-n : ℤ)) : ℤₘ₀) = ofAdd (-1 : ℤ) ^ n := by
  simp only [ofAdd_neg, coe_inv, inv_pow, coe_pow, inv_inj]
  rw [← @WithZero.coe_pow, WithZero.coe_inj, ← one_mul (n : ℤ), Int.ofAdd_mul, zpow_natCast]

-- **In PR #23177**
theorem ofAdd_neg_one_lt_one : (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) < (1 : ℤₘ₀) := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, ofAdd_lt]
  exact neg_one_lt_zero


end WithZero

-- From this line, in PR #15741

-- open WithZero

-- /-- Given a nonzero `e : ℝ≥0`, this is the map `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
--   `x ↦ e^(Multiplicative.toAdd (WithZero.unzero hx)` when `x ≠ 0` as a `MonoidWithZeroHom`. -/
-- def WithZeroMulInt.toNNReal {e : NNReal} (he : e ≠ 0) : ℤₘ₀ →*₀ ℝ≥0 where
--   toFun := fun x ↦ if hx : x = 0 then 0 else e ^ Multiplicative.toAdd (WithZero.unzero hx)
--   map_zero' := rfl
--   map_one' := by
--     simp only [dif_neg one_ne_zero]
--     erw [toAdd_one, zpow_zero]
--   map_mul' x y := by
--     simp only
--     by_cases hxy : x * y = 0
--     · cases' zero_eq_mul.mp (Eq.symm hxy) with hx hy
--       --either x = 0 or y = 0
--       · rw [dif_pos hxy, dif_pos hx, MulZeroClass.zero_mul]
--       · rw [dif_pos hxy, dif_pos hy, MulZeroClass.mul_zero]
--     · cases' mul_ne_zero_iff.mp hxy with hx hy
--       --  x ≠ 0 and y ≠ 0
--       rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (Or.inl he), ← toAdd_mul]
--       congr
--       rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]

-- theorem WithZeroMulInt.toNNReal_pos_apply {e : NNReal} (he : e ≠ 0) {x : ℤₘ₀} (hx : x = 0) :
--     WithZeroMulInt.toNNReal he x = 0 := by
--   simp only [WithZeroMulInt.toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
--   split_ifs; rfl

-- theorem WithZeroMulInt.toNNReal_neg_apply {e : NNReal} (he : e ≠ 0) {x : ℤₘ₀} (hx : x ≠ 0) :
--     WithZeroMulInt.toNNReal he x = e ^ Multiplicative.toAdd (WithZero.unzero hx) := by
--   simp only [WithZeroMulInt.toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
--   split_ifs; tauto; rfl

-- /-- `WithZeroMulInt.toNNReal` sends nonzero elements to nonzero elements. -/
-- theorem WithZeroMulInt.toNNReal_ne_zero {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
--     WithZeroMulInt.toNNReal he m ≠ 0 := by
--   simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

-- /-- `WithZeroMulInt.toNNReal` sends nonzero elements to positive elements. -/
-- theorem WithZeroMulInt.toNNReal_pos {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
--     0 < WithZeroMulInt.toNNReal he m :=
--   lt_of_le_of_ne zero_le' (WithZeroMulInt.toNNReal_ne_zero he hm).symm

-- -- [Mathlib.Data.NNReal.Basic]
-- /-- The map `WithZeroMulInt.toNNReal` is strictly monotone whenever `1 < e`. -/
-- theorem WithZeroMulInt.toNNReal_strictMono {e : NNReal} (he : 1 < e) :
--     StrictMono (WithZeroMulInt.toNNReal (ne_zero_of_lt he)) := by
--   intro x y hxy
--   simp only [WithZeroMulInt.toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
--   split_ifs with hx hy hy
--   · simp only [hy, not_lt_zero'] at hxy
--   · exact NNReal.zpow_pos (ne_zero_of_lt he) _
--   · simp only [hy, not_lt_zero'] at hxy
--   · rw [zpow_lt_iff_lt he, Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero hx,
--       WithZero.coe_unzero hy]
--     exact hxy
