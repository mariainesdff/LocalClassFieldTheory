import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic

namespace Valuation

open Function Set LinearOrderedCommGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

variable {A : Type*} [Ring A] (v : Valuation A Γ)

lemma IsDiscrete.mulArchimedean [IsDiscrete v] : MulArchimedean Γ := by
  constructor
  intro x y hy
  obtain ⟨g, hgen, hg_lt_one, -, ha⟩ := v.exists_generator_lt_one
  rcases le_or_lt x 1 with hx|hx
  · exact ⟨0, by simpa using hx⟩
  norm_cast at hx hy ⊢
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, g⁻¹ ^ k = x := by
    lift x to Γˣ using isUnit_iff_ne_zero.mpr (zero_lt_one.trans hx).ne'
    norm_cast
    simp only [← Subgroup.mem_zpowers_iff, Subgroup.zpowers_inv, hgen, Subgroup.mem_top]
  have hk : 0 < k := by
    simp only [Units.val_inv_eq_inv_val, ← inv_zpow', zpow_neg] at hx
    rwa [one_lt_zpow_iff_right₀] at hx
    norm_cast
    simp [hg_lt_one]
  obtain ⟨l, rfl⟩ : ∃ l : ℤ, g⁻¹ ^ l = y := by
    lift y to Γˣ using isUnit_iff_ne_zero.mpr (zero_lt_one.trans hy).ne'
    norm_cast
    simp only [← Subgroup.mem_zpowers_iff, Subgroup.zpowers_inv, hgen, Subgroup.mem_top]
  have hl : 0 < l := by
    simp only [Units.val_inv_eq_inv_val, ← inv_zpow', zpow_neg] at hy
    rwa [one_lt_zpow_iff_right₀] at hy
    norm_cast
    simp [hg_lt_one]
  lift k to ℕ using hk.le
  lift l to ℕ using hl.le
  norm_cast at hk hl ⊢
  obtain ⟨n, hn⟩ := Archimedean.arch k hl
  refine ⟨n, ?_⟩
  simp only [Units.val_inv_eq_inv_val, zpow_natCast, ← pow_mul']
  refine pow_right_monotone ?_ hn
  simp [hg_lt_one.le]

lemma IsDiscrete.not_denselyOrdered [IsDiscrete v] : ¬ DenselyOrdered Γ := by
  have := nontrivial_value_group v
  have H := cyclic_value_group v
  contrapose! H
  rw [← denselyOrdered_units_iff] at H
  exact not_isCyclic_of_denselyOrdered _

open Multiplicative in
lemma IsDiscrete.nonempty_mulOrderIso_multiplicative_int [IsDiscrete v] :
    Nonempty (Γ ≃*o ℤₘ₀) := by
  have := mulArchimedean v
  have := nontrivial_value_group v
  rw [LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
  exact not_denselyOrdered v

-- TODO: move elsewhere
instance {X : Type*} [Preorder X] [Nonempty X] [NoMaxOrder X] : NoMaxOrder (WithZero X) := by
  constructor
  intro x
  refine WithZero.cases_on x ?_ ?_
  · inhabit X
    exact ⟨(default : X), WithZero.zero_lt_coe _⟩
  · intro a
    obtain ⟨b, hb⟩ := exists_gt a
    refine ⟨b, ?_⟩
    simp [hb]

open Multiplicative in
lemma IsDiscrete.infinite_value_group [IsDiscrete v] : Infinite Γˣ := by
  obtain ⟨e⟩ := nonempty_mulOrderIso_multiplicative_int v
  let e' : Γˣ ≃* Multiplicative ℤ := MulEquiv.unzero (WithZero.withZeroUnitsEquiv.trans e)
  rw [e'.toEquiv.infinite_iff]
  infer_instance

-- TODO: move elsewhere
@[to_additive]
lemma Subgroup.zpowers_eq_zpowers_iff {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    {x y : G} : Subgroup.zpowers x = Subgroup.zpowers y ↔ x = y ∨ x⁻¹ = y := by
  rw [iff_comm]
  constructor
  · rintro (rfl|rfl) <;>
    · simp
  intro h
  have hx : x ∈ Subgroup.zpowers y := by
    simp [← h]
  have hy : y ∈ Subgroup.zpowers x := by
    simp [h]
  rw [Subgroup.mem_zpowers_iff] at hx hy
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨l, hl⟩ := hx
  wlog hx1 : 1 < x
  · push_neg at hx1
    rcases hx1.eq_or_lt with rfl|hx1
    · simp
    · specialize this (x := x⁻¹) (-k) (by simp [h]) (-l) (by simp [hl]) (by simp [hx1])
      simpa [or_comm] using this
  simp only [← zpow_mul] at hl
  replace hl : x ^ (k * l) = x ^ (1 : ℤ) := by simp [hl]
  rw [zpow_right_inj hx1, Int.mul_eq_one_iff_eq_one_or_neg_one] at hl
  refine hl.imp ?_ ?_ <;>
  simp +contextual
