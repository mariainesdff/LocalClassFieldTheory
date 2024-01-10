/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import LocalClassFieldTheory.FromMathlib.RingSeminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Order.Hom.Basic

#align_import from_mathlib.pow_mult_faithful

/-!
# Equivalent power-multiplicative norms

In this file, we prove [BGR, Proposition 3.1.5/1]: if `R` is a normed commutative ring and `f₁` and
`f₂` are two power-multiplicative `R`-algebra norms on `S`, then if `f₁` and `f₂` are equivalent on
every subring `R[y]` for `y : S`, it follows that `f₁ = f₂`.

## Main Definitions
* `algebra_norm.restriction` : The restriction of an algebra norm to a subalgebra.
* `ring_hom.is_bounded_wrt` :A ring homomorphism `f : α →+* β` is bounded with respect to the
  functions `nα : α → ℝ` and `nβ : β → ℝ` if there exists a positive constant `C` such that for all
  `x` in `α`, `nβ (f x) ≤ C * nα x`.

## Main Results
* `eq_of_pow_mult_faithful` : the proof of [BGR, Proposition 3.1.5/1].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

norm, equivalent, power-multiplicative
-/


open scoped Topology

/-- A homomorphism `f` between semi_normed_rings is bounded if there exists a positive
  constant `C` such that for all `x` in `α`, `norm (f x) ≤ C * norm x`. -/
def RingHom.IsBounded {α : Type _} [SeminormedRing α] {β : Type _} [SeminormedRing β]
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

/-- A ring homomorphism `f : α →+* β` is bounded with respect to the functions `nα : α → ℝ` and
  `nβ : β → ℝ` if there exists a positive constant `C` such that for all `x` in `α`,
  `nβ (f x) ≤ C * nα x`. -/
def RingHom.IsBoundedWrt {α : Type _} [Ring α] {β : Type _} [Ring β] (nα : α → ℝ) (nβ : β → ℝ)
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x

/-- If `f : α →+* β` is bounded with respect to a ring seminorm `nα` on `α` and a
  power-multiplicative function `nβ : β → ℝ`, then `∀ x : α, nβ (f x) ≤ nα x`. -/
theorem contraction_of_is_pm_wrt {F : Type _} {α : outParam (Type _)} [Ring α]
    [RingSeminormClass F α ℝ] {β : Type _} [Ring β] (nα : F) {nβ : β → ℝ} (hβ : IsPowMul nβ)
    {f : α →+* β} (hf : f.IsBoundedWrt nα nβ) (x : α) : nβ (f x) ≤ nα x :=
  by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Filter.Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ)) * nα x) Filter.atTop (𝓝 (nα x)) :=
    by
    have : 𝓝 (nα x) = 𝓝 (1 * nα x) := by rw [one_mul]
    rw [this]
    apply Filter.Tendsto.mul
    · apply Filter.Tendsto.comp _ (tendsto_const_div_atTop_nhds_0_nat 1)
      rw [← Real.rpow_zero C]
      apply ContinuousAt.tendsto (Real.continuousAt_const_rpow (ne_of_gt hC0))
    exact tendsto_const_nhds
  apply ge_of_tendsto hlim
  simp only [Filter.eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  have h : (C ^ (1 / n : ℝ)) ^ n = C := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    rw [← Real.rpow_nat_cast, ← Real.rpow_mul (le_of_lt hC0), one_div, inv_mul_cancel hn0,
      Real.rpow_one]
  apply le_of_pow_le_pow_left (ne_of_gt hn)
    (mul_nonneg (Real.rpow_nonneg_of_nonneg (le_of_lt hC0) _) (map_nonneg _ _))
  · rw [mul_pow, h, ← hβ _ hn, ← RingHom.map_pow]
    apply le_trans (hC (x ^ n))
    rw [mul_le_mul_left hC0]
    exact map_pow_le_pow _ _ (Nat.one_le_iff_ne_zero.mp hn)

/-- Given a bounded `f : α →+* β` between seminormed rings, is the seminorm on `β` is
  power-multiplicative, then `f` is a contraction. -/
theorem contraction_of_is_pm {α : Type _} [SeminormedRing α] {β : Type _} [SeminormedRing β]
    (hβ : IsPowMul (norm : β → ℝ)) {f : α →+* β} (hf : f.IsBounded) (x : α) : norm (f x) ≤ norm x :=
  contraction_of_is_pm_wrt (SeminormedRing.toRingSeminorm α) hβ hf x

/-- Given two power-multiplicative ring seminorms `f, g` on `α`, if `f` is bounded by a positive
  multiple of `g` and viceversa, then `f = g`. -/
theorem eq_seminorms {F : Type _} {α : outParam (Type _)} [Ring α] [RingSeminormClass F α ℝ]
    (f g : F) (hfpm : IsPowMul f) (hgpm : IsPowMul g)
    (hfg : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, f a ≤ r * g a)
    (hgf : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, g a ≤ r * f a) : f = g := by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff FunLike.coe_injective']
  ext x
  exact le_antisymm (contraction_of_is_pm_wrt g hfpm hge x) (contraction_of_is_pm_wrt f hgpm hle x)

variable {R S : Type _} [NormedCommRing R] [CommRing S] [Algebra R S]

/-- The restriction of a power-multiplicative function to a subalgebra is power-multiplicative. -/
theorem IsPowMul.restriction (A : Subalgebra R S) {f : S → ℝ} (hf_pm : IsPowMul f) :
    IsPowMul fun x : A => f x.val := fun x n hn => by
  simpa [SubsemiringClass.coe_pow] using hf_pm (↑x) hn

/-- The restriction of an algebra norm to a subalgebra. -/
def AlgebraNorm.restriction (A : Subalgebra R S) (f : AlgebraNorm R S) : AlgebraNorm R A where
  toFun       := fun x : A => f x.val
  map_zero'   := map_zero f
  add_le' x y := map_add_le_add _ _ _
  neg' x      := map_neg_eq_map _ _
  mul_le' x y := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' x hx := by
    rw [← ZeroMemClass.coe_eq_zero]; exact eq_zero_of_map_eq_zero f hx
  smul' r x := map_smul_eq_mul _ _ _

/-- If `R` is a normed commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra
  norms on `S`, then if `f₁` and `f₂` are equivalent on every  subring `R[y]` for `y : S`, it
  follows that `f₁ = f₂` [BGR, Proposition 3.1.5/1].  -/
theorem eq_of_pow_mult_faithful (f₁ : AlgebraNorm R S) (hf₁_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S)
    (hf₂_pm : IsPowMul f₂)
    (h_eq : ∀ y : S, ∃ (C₁ C₂ : ℝ) (_ : 0 < C₁) (_ : 0 < C₂),
      ∀ x : Algebra.adjoin R {y}, f₁ x.val ≤ C₁ * f₂ x.val ∧ f₂ x.val ≤ C₂ * f₁ x.val) :
    f₁ = f₂ := by
  ext x
  set g₁ : AlgebraNorm R (Algebra.adjoin R ({x} : Set S)) := AlgebraNorm.restriction _ f₁
  set g₂ : AlgebraNorm R (Algebra.adjoin R ({x} : Set S)) := AlgebraNorm.restriction _ f₂
  have hg₁_pm : IsPowMul g₁ := IsPowMul.restriction _ hf₁_pm
  have hg₂_pm : IsPowMul g₂ := IsPowMul.restriction _ hf₂_pm
  let y : Algebra.adjoin R ({x} : Set S) := ⟨x, Algebra.self_mem_adjoin_singleton R x⟩
  have hy : x = y.val := rfl
  have h1 : f₁ y.val = g₁ y := rfl
  have h2 : f₂ y.val = g₂ y := rfl
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hC⟩ := h_eq x
  obtain ⟨hC₁, hC₂⟩ := forall_and.mp hC
  rw [hy, h1, h2, eq_seminorms g₁ g₂ hg₁_pm hg₂_pm ⟨C₁, hC₁_pos, hC₁⟩ ⟨C₂, hC₂_pos, hC₂⟩]
