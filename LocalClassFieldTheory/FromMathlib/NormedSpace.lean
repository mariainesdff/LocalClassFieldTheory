/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import LocalClassFieldTheory.FromMathlib.SmoothingSeminorm
import Mathlib.Analysis.Normed.Algebra.Norm
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.SeminormFromBounded
import Mathlib.LinearAlgebra.FiniteDimensional.Defs


/-!
# Basis.norm

In this file, we prove [BGR, Lemma 3.2.1./3][bosch-guntzer-remmert]  : if `K` is a normed field
with a nonarchimedean power-multiplicative norm and `L/K` is a finite extension, then there exists
at least one power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions
* `Basis.norm` : the function sending an element `x : L` to the maximum of the norms of its
  coefficients with respect to the `K`-basis `B` of `L`.

## Main Results
* `finite_extension_pow_mul_seminorm` : the proof of [BGR, Lemma 3.2.1./3].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

Basis.norm, nonarchimedean
-/

set_option autoImplicit false


noncomputable section

open Finset

open scoped BigOperators

section Continuous

/- /-- A continuous linear map between normed spaces. -/
structure IsContinuousLinearMap (𝕜 : Type*) [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E → F) extends
    IsLinearMap 𝕜 f : Prop where
  cont : Continuous f := by continuity -/

/- /-- A linear map between normed spaces is continuous if and only if it is bounded,-/
theorem isContinuousLinearMap_iff_isBoundedLinearMap' {K : Type*} [NontriviallyNormedField K]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace K M] {N : Type*} [NormedAddCommGroup N]
    [NormedSpace K N] (f : M → N) : IsContinuousLinearMap K f ↔ IsBoundedLinearMap K f := by
  refine ⟨fun h_cont ↦ ?_, fun h_bdd ↦ ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩⟩
  · set F : M →L[K] N := by
      use ⟨⟨f, IsLinearMap.map_add h_cont.1⟩, IsLinearMap.map_smul h_cont.1⟩
      exact h_cont.2
    exact ContinuousLinearMap.isBoundedLinearMap F -/

-- It seems like we are not using this
/-- A linear map between normed spaces is continuous if and only if it is bounded,-/
theorem isContinuousLinearMap_iff_isBoundedLinearMap {K M N : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup M] [NormedSpace K M] [NormedAddCommGroup N] [NormedSpace K N] (f : M → N) :
    IsLinearMap K f ∧ Continuous f ↔ IsBoundedLinearMap K f :=
  ⟨fun ⟨hlin, hcont⟩ ↦ ContinuousLinearMap.isBoundedLinearMap
      ⟨⟨⟨f, IsLinearMap.map_add hlin⟩, IsLinearMap.map_smul hlin⟩, hcont⟩,
        fun h_bdd ↦ ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩⟩


end Continuous

section finsum

variable {R S : Type*} {α : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M N : Type*) [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module S N] (g : M ≃ₛₗ[σ] N) (f : α → M)

-- Mathlib.LinearAlgebra.DFinsupp
/-- Given a linear equivalence `g : M ≃ₛₗ[σ] N` and a function `f : α → M`, we have
  `g ∑ᶠ f i = ∑ᶠ g(f i)`.  -/
theorem LinearEquiv.map_finsum : g (finsum fun i : α ↦ f i) = finsum fun i : α ↦ g (f i) :=
  AddEquiv.map_finsum g.toAddEquiv f

/-- Given a fintype `α`, a function `f : α → M` and a linear equivalence `g : M ≃ₛₗ[σ] N`, we have
  `g (∑ (i : α), f i) = ∑ (i : α), g (f i)`.  -/
theorem LinearEquiv.map_finset_sum [Fintype α] :
    g (∑ i : α, f i) = ∑ i : α, g (f i) := by
  simp only [← finsum_eq_sum_of_fintype, LinearEquiv.map_finsum]

-- This is now in Mathlib.Algebra.BigOperators.Finprod
/- theorem finsum_apply {α : Type*} {β : α → Type*} {γ : Type*} [Finite γ]
    [∀ a : α, AddCommMonoid (β a)] (a : α) (g : γ → ∀ a : α, β a) :
    finsum (fun c : γ ↦ g c) a = finsum fun c : γ ↦ g c a :=
  by
  cases nonempty_fintype γ
  simp only [finsum_eq_sum_of_fintype, sum_apply] -/

-- [Mathlib.LinearAlgebra.LinearIndependent]
/-- If `∑ i, f i • v i = ∑ i, g i • v i`, then for all `i`, `f i = g i`. -/
theorem LinearIndependent.eq_coords_of_eq {R M ι: Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype ι] {v : ι → M} (hv : LinearIndependent R v) {f : ι → R}
    {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := by
  rw [← sub_eq_zero, ← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  rw [linearIndependent_iff'] at hv
  exact sub_eq_zero.mp (hv univ (fun i ↦ f i - g i) heq i (mem_univ i))

end finsum

section Ring

variable {K L : Type*} [CommRing K] [Ring L] [Algebra K L]

-- [Mathlib.LinearAlgebra.FreeModule.Basic, Mathlib.LinearAlgebra.Dimension.StrongRankCondition]
/-- If `B` is a basis of the `K`-vector space `L` such that `B i = 1` for some index `i`, then
each `k:K` gets represented as `k • B i` as an element of `L`. -/
theorem equivFun_algebraMap {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Basis ι K L} {i : ι}
    (hBi : B i = (1 : L)) (k : K) :
    B.equivFun ((algebraMap K L) k) = fun j : ι ↦ if j = i then k else 0 := by
  ext j
  apply LinearIndependent.eq_coords_of_eq B.linearIndependent
  rw [Basis.sum_equivFun B (algebraMap K L k), sum_congr (Eq.refl _)
    (fun x _ ↦ ite_zero_smul _ k (B x)), Algebra.algebraMap_eq_smul_one,
      sum_ite_eq' univ (i : ι) fun j : ι ↦ k • B j]
  simp only [mem_univ, if_true, hBi]

end Ring

section

variable {K L : Type*} [NormedField K] [Ring L] [Algebra K L]

namespace Basis

variable {ι : Type*} [Fintype ι] [Nonempty ι] (B : Basis ι K L)

/-- The function sending an element `x : L` to the maximum of the norms of its coefficients
  with respect to the `K`-basis `B` of `L`.-/
def norm  : L → ℝ := fun x ↦
  ‖B.equivFun x (Classical.choose (Finite.exists_max fun i : ι ↦ ‖B.equivFun x i‖))‖

/-- The norm of a coefficient `x_i` is less than or equal to the norm of `x`. -/
theorem norm_equivFun_le_norm {x : L} (i : ι) :
    ‖B.equivFun x i‖ ≤ B.norm x :=
  Classical.choose_spec (Finite.exists_max fun i : ι ↦ ‖B.equivFun x i‖) i

/-- For any `K`-basis of `L`, we have `B.norm 0 = 0`. -/
protected theorem norm_zero : B.norm 0 = 0 := by
  simp [norm, map_zero, Pi.zero_apply, norm_zero]

/-- For any `K`-basis of `L`, and any `x : L`, we have `B.norm (-x) = B.norm x`. -/
protected theorem norm_neg (x : L) : B.norm (-x) = B.norm x := by
  simp [norm, map_neg, equivFun_apply,  Pi.neg_apply, _root_.norm_neg]

variable {B}

/-- For any `K`-basis of `L`, `B.norm` extends the norm on `K`. -/
theorem norm_extends {i : ι} (hBi : B i = (1 : L)) : FunctionExtends (fun x : K ↦ ‖x‖) B.norm := by
  classical
  intro k
  · by_cases hk : k = 0
    · simp [hk, map_zero, norm_zero, Basis.norm_zero]
    · simp only [norm, equivFun_algebraMap hBi]
      have h_max : Classical.choose
          (Finite.exists_max fun j : ι ↦ ‖(fun n : ι ↦ if n = i then k else 0) j‖) = i := by
        by_contra h
        have h_max := Classical.choose_spec
          (Finite.exists_max fun j : ι ↦ ‖(fun n : ι ↦ if n = i then k else 0) j‖)
        simp only [if_neg h] at h_max
        specialize h_max i
        rw [if_pos rfl, norm_zero, norm_le_zero_iff] at h_max
        exact hk h_max
      rw [if_pos h_max]

/-- For any `K`-basis of `L`, if the norm on `K` is nonarchimedean, then so is `B.norm`. -/
theorem norm_isNonarchimedean (hna : IsNonarchimedean (Norm.norm : K → ℝ)) :
    IsNonarchimedean B.norm := by
  classical
  intro x y
  simp only [Basis.norm]
  set ixy := Classical.choose (Finite.exists_max fun i : ι ↦ ‖B.equivFun (x + y) i‖)
  have hxy : ‖B.equivFun (x + y) ixy‖ ≤ max ‖B.equivFun x ixy‖ ‖B.equivFun y ixy‖ := by
    rw [LinearEquiv.map_add, Pi.add_apply]; exact hna _ _
  have hix := Classical.choose_spec (Finite.exists_max fun i : ι ↦ ‖B.equivFun x i‖)
  have hiy := Classical.choose_spec (Finite.exists_max fun i : ι ↦ ‖B.equivFun y i‖)
  rcases le_max_iff.mp hxy with (hx | hy)
  · exact le_max_of_le_left (le_trans hx (hix ixy))
  · exact le_max_of_le_right (le_trans hy (hiy ixy))

/-- For any `K`-basis of `L`, `B.norm` is bounded with respect to multiplication. That is,
  `∃ (c : ℝ), c > 0` such that ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y`. -/
theorem norm_mul_le_const_mul_norm {i : ι} (hBi : B i = (1 : L))
      (hna : IsNonarchimedean (Norm.norm : K → ℝ)) :
    ∃ (c : ℝ) (_ : 0 < c), ∀ x y : L, B.norm (x * y) ≤ c * B.norm x * B.norm y := by
  classical
  -- The bounding constant `c` will be the maximum of the products `B.norm (B i * B j)`.
  set c := Classical.choose (Finite.exists_max fun i : ι × ι ↦ B.norm (B i.1 * B i.2))
  have hc := Classical.choose_spec (Finite.exists_max fun i : ι × ι ↦ B.norm (B i.1 * B i.2))
  use B.norm (B c.1 * B c.2)
  constructor
  -- ∀ (x y : L), B.norm (x * y) ≤ B.norm (⇑B c.fst * ⇑B c.snd) * B.norm x * B.norm y
  · intro x y
    -- `ixy` is an index for which `‖B.equivFun (x*y) i‖` is maximum.
    set ixy := Classical.choose (Finite.exists_max fun i : ι ↦ ‖B.equivFun (x * y) i‖) with
      hixy_def
    -- We rewrite the LHS using `ixy`.
    conv_lhs =>
      simp only [Basis.norm]
      rw [← hixy_def, ← Basis.sum_equivFun B x, ← Basis.sum_equivFun B y]
    rw [sum_mul, LinearEquiv.map_finset_sum, sum_apply]
    simp_rw [smul_mul_assoc, LinearEquiv.map_smul, mul_sum, LinearEquiv.map_finset_sum,
      mul_smul_comm, LinearEquiv.map_smul]
    have hna' : IsNonarchimedean (NormedField.toMulRingNorm K) := hna
    /- Since the norm is nonarchimidean, the norm of a finite sum is bounded by the maximum of the
          norms of the summands. -/
    have hk : ∃ (k : ι) (_ : (univ : Finset ι).Nonempty → k ∈ univ ),
        ‖∑ i : ι, (B.equivFun x i • ∑ i_1 : ι, B.equivFun y i_1 • B.equivFun (B i * B i_1)) ixy‖ ≤
          ‖(B.equivFun x k • ∑ j : ι, B.equivFun y j • B.equivFun (B k * B j)) ixy‖ := by
      obtain ⟨k, hk0, hk⟩ := IsNonarchimedean.finset_image_add hna'
        (fun i ↦ (B.equivFun x i • ∑ i_1 : ι, B.equivFun y i_1 • B.equivFun (B i * B i_1)) ixy)
        (univ : Finset ι)
      exact ⟨k, hk0, hk⟩
    obtain ⟨k, -, hk⟩ := hk
    apply le_trans hk
    -- We use the above property again.
    have hk' : ∃ (k' : ι) (_ : (univ : Finset ι).Nonempty → k' ∈ univ),
        ‖∑ j : ι, B.equivFun y j • B.equivFun (B k * B j) ixy‖ ≤
          ‖B.equivFun y k' • B.equivFun (B k * B k') ixy‖ := by
      obtain ⟨k, hk0, hk⟩ := IsNonarchimedean.finset_image_add hna'
        (fun i ↦ B.equivFun y i • B.equivFun (B k * B i) ixy) (univ : Finset ι)
      exact ⟨k, hk0, hk⟩
    obtain ⟨k', -, hk'⟩ := hk'
    rw [Pi.smul_apply, norm_smul, sum_apply]
    apply le_trans (mul_le_mul_of_nonneg_left hk' (norm_nonneg _))
    -- Now an easy computation leads to the desired conclusion.
    rw [norm_smul, mul_assoc, mul_comm (B.norm (B c.fst * B c.snd)), ← mul_assoc]
    exact mul_le_mul (mul_le_mul (B.norm_equivFun_le_norm _) (B.norm_equivFun_le_norm _)
      (norm_nonneg _) (norm_nonneg _)) (le_trans (B.norm_equivFun_le_norm _) (hc (k, k')))
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    -- `B c.1 * B c.2` is positive
  · have h_pos : (0 : ℝ) < B.norm (B i * B i) := by
      have h1 : (1 : L) = (algebraMap K L) 1 := by rw [map_one]
      rw [hBi, mul_one, h1, Basis.norm_extends hBi]
      simp [norm_one, zero_lt_one]
    exact lt_of_lt_of_le h_pos (hc (i, i))

/-- For any `k : K`, `y : L`, we have
  `B.equivFun ((algebra_map K L k) * y) i = k * (B.equivFun y i) `. -/
theorem repr_smul' {ι : Type*} [Fintype ι] (B : Basis ι K L) (i : ι) (k : K) (y : L) :
    B.equivFun (algebraMap K L k * y) i = k * B.equivFun y i := by
  rw [← smul_eq_mul, algebraMap_smul, LinearEquiv.map_smul]; rfl

/-- For any `k : K`, `y : L`, we have
  `B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y`. -/
theorem norm_smul {ι : Type*} [Fintype ι] [Nonempty ι] {B : Basis ι K L} {i : ι}
    (hBi : B i = (1 : L)) (k : K) (y : L) :
    B.norm ((algebraMap K L) k * y) = B.norm ((algebraMap K L) k) * B.norm y := by
  classical
  by_cases hk : k = 0
  · rw [hk, map_zero, MulZeroClass.zero_mul, B.norm_zero, MulZeroClass.zero_mul]
  · rw [norm_extends hBi]
    simp only [norm]
    set i := Classical.choose (Finite.exists_max fun i : ι ↦ ‖B.equivFun y i‖)
    have hi := Classical.choose_spec (Finite.exists_max fun i : ι ↦ ‖B.equivFun y i‖)
    set j := Classical.choose
        (Finite.exists_max fun i : ι ↦ ‖B.equivFun ((algebraMap K L) k * y) i‖) with hj_def
    have hj := Classical.choose_spec
        (Finite.exists_max fun i : ι ↦ ‖B.equivFun ((algebraMap K L) k * y) i‖)
    have hij : ‖B.equivFun y i‖ = ‖B.equivFun y j‖ := by
      refine le_antisymm ?_ (hi j)
      specialize hj i
      rw [← hj_def, repr_smul', norm_mul, repr_smul', norm_mul] at hj
      exact (mul_le_mul_left (lt_of_le_of_ne (norm_nonneg _)
        (Ne.symm (norm_ne_zero_iff.mpr hk)))).mp hj
    rw [repr_smul', norm_mul, hij]

end Basis

end

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L]

/-- If `K` is a nonarchimedean normed field `L/K` is a finite extension, then there exists a
power-multiplicative nonarchimedean `K`-algebra norm on `L` extending the norm on `K`. -/
theorem finite_extension_pow_mul_seminorm (hfd : FiniteDimensional K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) :
    ∃ f : AlgebraNorm K L, IsPowMul f ∧ FunctionExtends (norm : K → ℝ) f ∧ IsNonarchimedean f := by
  classical
  -- Choose a basis B = {1, e2,..., en} of the K-vector space L
  set h1 : LinearIndependent K fun x : ({1} : Set L) ↦ (x : L) :=
    linearIndependent_singleton one_ne_zero
  set ι := { x // x ∈ h1.extend (Set.subset_univ ({1} : Set L)) }
  set B : Basis ι K L := Basis.extend h1
  letI hfin : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  haveI hem : Nonempty ι := B.index_nonempty
  have h1L : (1 : L) ∈ h1.extend _ := Basis.subset_extend _ (Set.mem_singleton (1 : L))
  have hB1 : B ⟨1, h1L⟩ = (1 : L) := by rw [Basis.coe_extend, Subtype.coe_mk]
  -- For every k ∈ K, k = k • 1 + 0 • e2 + ... + 0 • en
 /-  have h_k :
    ∀ k : K, B.equivFun ((algebraMap K L) k) = fun i : ι ↦ if i = ⟨(1 : L), h1L⟩ then k else 0 :=
    equivFun_algebraMap hB1 -/
  -- Define a function g : L → ℝ by setting g (∑ki • ei) = maxᵢ ‖ ki ‖
  set g : L → ℝ := B.norm
  -- g 0 = 0seminormFromBounded
  have hg0 : g 0 = 0 := B.norm_zero
  -- g takes nonnegative values
  have hg_nonneg : ∀ x : L, 0 ≤ g x := fun x ↦ norm_nonneg _
  -- g extends the norm on K
  have hg_ext : FunctionExtends (norm : K → ℝ) g := Basis.norm_extends hB1
  -- g is nonarchimedean
  have hg_na : IsNonarchimedean g := Basis.norm_isNonarchimedean hna
  -- g satisfies the triangle inequality
  have hg_add : ∀ a b : L, g (a + b) ≤ g a + g b :=
    fun _ _ ↦ IsNonarchimedean.add_le hg_nonneg hg_na
  -- g (-a) = g a
  have hg_neg : ∀ a : L, g (-a) = g a := B.norm_neg
  -- g is multiplicatively bounded
  obtain ⟨_, _, hg_bdd⟩ := Basis.norm_mul_le_const_mul_norm hB1 hna
  -- g is a K-module norm
  have hg_mul : ∀ (k : K) (y : L), g ((algebraMap K L) k * y) = g ((algebraMap K L) k) * g y :=
    fun k y ↦ Basis.norm_smul hB1 k y
  -- Using BGR Prop. 1.2.1/2, we can smooth g to a ring norm f on L that extends the norm on K.
  set f := seminormFromBounded hg0 hg_nonneg hg_bdd hg_add hg_neg
  have hf_na : IsNonarchimedean f := seminormFromBounded_isNonarchimedean hg_nonneg hg_bdd hg_na
  have hf_1 : f 1 ≤ 1 := seminormFromBounded_one_le hg_nonneg hg_bdd
  have hf_ext : FunctionExtends (norm : K → ℝ) f := by
    intro k
    rw [← hg_ext]
    exact seminormFromBounded_of_mul_apply hg_nonneg hg_bdd (hg_mul k)
  -- Using BGR Prop. 1.3.2/1, we obtain from f  a power multiplicative K-algebra norm on L
  -- extending the norm on K.
  set F' := smoothingSeminorm f hf_1 hf_na with hF'
  have hF'_ext : ∀ k : K, F' ((algebraMap K L) k) = ‖k‖ := by
    intro k
    rw [← hf_ext _]
    exact smoothingSeminorm_apply_of_is_mul f hf_1 hf_na
      (seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k))
  have hF'_1 : F' 1 = 1 := by
    have h1 : (1 : L) = (algebraMap K L) 1 := by rw [map_one]
    simp only [h1, hF'_ext (1 : K), norm_one]
  have hF'_0 : F' ≠ 0 := DFunLike.ne_iff.mpr ⟨(1 : L), by rw [hF'_1]; exact one_ne_zero⟩
  set F : AlgebraNorm K L :=
    { RingSeminorm.toRingNorm F' hF'_0 with
      smul' := fun k y ↦ by
        have hk : ∀ y : L, f (algebraMap K L k * y) = f (algebraMap K L k) * f y :=
          seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k)
        have hfk : ‖k‖ = (smoothingSeminorm f hf_1 hf_na) ((algebraMap K L) k) := by
          rw [← hf_ext k, eq_comm, smoothingSeminorm_apply_of_is_mul f hf_1 hf_na hk]
        simp only [hfk, hF']
        erw [← smoothingSeminorm_of_mul f hf_1 hf_na hk y, Algebra.smul_def]
        rfl }
  have hF_ext : ∀ k : K, F ((algebraMap K L) k) = ‖k‖ := by
    intro k
    rw [← hf_ext _]
    exact smoothingSeminorm_apply_of_is_mul f hf_1 hf_na
      (seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k))
  exact ⟨F, smoothingSeminorm_isPowMul f hf_1, hF_ext,
      smoothingSeminorm_isNonarchimedean f hf_1 hf_na⟩
