import LocalClassFieldTheory.FromMathlib.DiscreteBasic
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Basic
-- import Mathlib.RingTheory.Valuation.Discrete.Basic

namespace Valuation

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {A : Type*} [Ring A] (v : Valuation A Γ)

open Subgroup

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
    simp only [← mem_zpowers_iff, zpowers_inv, hgen, mem_top]
  have hk : 0 < k := by
    simp only [Units.val_inv_eq_inv_val, ← inv_zpow', zpow_neg] at hx
    rwa [one_lt_zpow_iff_right₀] at hx
    norm_cast
    simp [hg_lt_one]
  obtain ⟨l, rfl⟩ : ∃ l : ℤ, g⁻¹ ^ l = y := by
    lift y to Γˣ using isUnit_iff_ne_zero.mpr (zero_lt_one.trans hy).ne'
    norm_cast
    simp only [← mem_zpowers_iff, zpowers_inv, hgen, mem_top]
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

-- -- TODO: move elsewhere
-- instance {X : Type*} [Preorder X] [Nonempty X] [NoMaxOrder X] : NoMaxOrder (WithZero X) := by
--   constructor
--   intro x
--   refine WithZero.cases_on x ?_ ?_
--   · inhabit X
--     exact ⟨(default : X), WithZero.zero_lt_coe _⟩
--   · intro a
--     obtain ⟨b, hb⟩ := exists_gt a
--     refine ⟨b, ?_⟩
--     simp [hb]

open Multiplicative in
lemma IsDiscrete.infinite_value_group [IsDiscrete v] : Infinite Γˣ := by
  obtain ⟨e⟩ := nonempty_mulOrderIso_multiplicative_int v
  let e' : Γˣ ≃* Multiplicative ℤ := MulEquiv.unzero (WithZero.withZeroUnitsEquiv.trans e)
  rw [e'.toEquiv.infinite_iff]
  infer_instance

end Valuation

namespace Subgroup
-- TODO: move elsewhere
@[to_additive]
lemma zpowers_eq_zpowers_iff {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    {x y : G} : zpowers x = zpowers y ↔ x = y ∨ x⁻¹ = y := by
  rw [iff_comm]
  constructor
  · rintro (rfl|rfl) <;>
    · simp
  intro h
  have hx : x ∈ zpowers y := by
    simp [← h]
  have hy : y ∈ zpowers x := by
    simp [h]
  rw [mem_zpowers_iff] at hx hy
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

open LinearOrderedCommGroup in
lemma genLTOne_unique {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [IsCyclic G] [Nontrivial G] (g : G) : g < 1 ∧ Subgroup.zpowers g = ⊤ → g = genLTOne G := by
  rintro ⟨hg_lt, hg_top⟩
  rw [← (⊤ : Subgroup G).genLTOne_zpowers_eq_top] at hg_top
  rcases zpowers_eq_zpowers_iff.mp hg_top with _ | h
  · assumption
  rw [← one_lt_inv', h] at hg_lt
  exact (not_lt_of_lt hg_lt <| Subgroup.genLTOne_lt_one _).elim

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [IsCyclic G]

variable (H : Subgroup G) [Nontrivial H]

open LinearOrderedCommGroup Valuation

-- Move to `Order.Cyclic`???
lemma genLTOne_val_eq_genLTOne : ((⊤ : Subgroup H).genLTOne) = H.genLTOne := by
  set γ := H.genLTOne with hγ
  set η := ((⊤ : Subgroup H).genLTOne) with hη
  have h1 (x : H) : ∃ k : ℤ, η ^ k = x := by
    have uno := Subgroup.genLTOne_zpowers_eq_top (G := H) (H := ⊤)
    have tre : IsCyclic H := by
      apply isCyclic_iff_exists_zpowers_eq_top (α := H)|>.mpr
      use η
    rw [← Subgroup.mem_zpowers_iff (G := H) (h := x) (g := η)]
    rw [uno]
    trivial
  replace h1 (x : G) : x ∈ H → ∃ k : ℤ, η ^ k = x := by
    intro hx
    obtain ⟨k, hk⟩ := h1 ⟨x, hx⟩
    use k
    norm_cast
    rw [hk]
  have h2 := Subgroup.genLTOne_zpowers_eq_top (G := G) (H := H)
  replace h2 (x : G) : x ∈ H → ∃ k : ℤ, γ ^ k = x := by
    rw [← Subgroup.mem_zpowers_iff (g := γ) (h := x)]
    intro h_mem
    rwa [h2]
  have main : Subgroup.zpowers ↑η = Subgroup.zpowers γ := by
    ext y
    refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
    · rw [Subgroup.mem_zpowers_iff]
      apply h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hk]
      apply Subgroup.zpow_mem
      simp only [SetLike.coe_mem]
    · rw [H.genLTOne_zpowers_eq_top] at hy
      obtain ⟨k, hk⟩ := h1 y hy
      rw [Subgroup.mem_zpowers_iff]
      use k
  rw [zpowers_eq_zpowers_iff] at main
  rcases main with _ | h
  · assumption
  have hγ_lt := H.genLTOne_lt_one
  have hη_lt := (⊤ : Subgroup H).genLTOne_lt_one
  rw [← hη] at hη_lt
  rw [← hγ, ← h] at hγ_lt
  rw [inv_lt_one'] at hγ_lt
  exact (not_lt_of_lt hγ_lt hη_lt).elim

end Subgroup

namespace Multiplicative

open Subgroup

instance : IsCyclic ℤₘ₀ˣ :=
  isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm (MulEquiv.surjective _)

instance : Nontrivial ℤₘ₀ˣ :=
  Function.Surjective.nontrivial (f := WithZero.unitsWithZeroEquiv) (MulEquiv.surjective _)

lemma top_eq_zpowers_neg_one :
    zpowers (ofAdd (-1 : ℤ)) = (⊤ : Subgroup (Multiplicative ℤ)) := by
  rw [← coe_eq_univ, ← ofAdd_image_zmultiples_eq_zpowers_ofAdd]
  simp

open LinearOrderedCommGroup WithZero in
lemma genLTOne_eq_neg_one : unitsWithZeroEquiv.symm (ofAdd (-1 : ℤ)) = (genLTOne (ℤₘ₀ˣ)) :=  by
  let e := (unitsWithZeroEquiv (α := Multiplicative ℤ)).symm
  refine genLTOne_unique (e (ofAdd (-1 : ℤ))) ⟨?_, ?_⟩
  · simpa only [Int.reduceNeg, ofAdd_neg, map_inv, Left.inv_lt_one_iff] using
      compareOfLessAndEq_eq_lt.mp rfl
  rw [← map_top_of_surjective e.toMonoidHom (MulEquiv.surjective _), ← top_eq_zpowers_neg_one,
    MonoidHom.map_zpowers]
  rfl
