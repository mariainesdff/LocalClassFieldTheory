/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unique norm extension theorem

Let `K` be a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
`L/K` be an algebraic extension. We show that the spectral norm on `L` is a nonarchimedean
multiplicative norm, and any power-multiplicative `K`-algebra norm on `L` coincides with the
spectral norm. More over, if `L/K` is finite, then `L` is a complete space.
This result is [S. Bosch, U. Güntzer, R. Remmert,*Non-Archimedean Analysis* (Theorem 3.2.4/2)]
[bosch-guntzer-remmert].

## Main Definitions

* `spectralMulAlgNorm` : the spectral norm is a multiplicative `K`-algebra norm on `L`.

## Main Results
* `spectralNorm_unique` : any power-multiplicative `K`-algebra norm on `L` coincides with the
  spectral norm.
* `spectralAlgNorm_mul` : the spectral norm on `L` is multiplicative.
* `spectralNorm.completeSpace` : if `L/K` is finite dimensional, then `L` is a complete space
  with respect to topology induced by the spectral norm.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, unique, seminorm, norm, nonarchimedean
-/

-- In PR #23268 and

noncomputable section

section Prelim

-- In PR #23268
/-- The `NormedRing` stucture on a ring `A` determined by a `RingNorm`. -/
def RingNorm.to_normedRing {A : Type*} [Ring A] (f : RingNorm A) : NormedRing A where
  norm x := f x
  dist x y := f (x - y)
  dist_self x := by simp [sub_self, _root_.map_zero]
  dist_comm x y := by
    rw [← neg_sub x y, map_neg_eq_map]
  dist_triangle x y z := by
    have hxyz : x - z = x - y + (y - z) := by abel
    simp only [hxyz, map_add_le_add]
  dist_eq x y := rfl
  norm_mul_le x y := by simp [map_mul_le_mul]
  edist_dist x y := by rw [eq_comm, ENNReal.ofReal_eq_coe_nnreal]
  eq_of_dist_eq_zero hxy := by
    exact eq_of_sub_eq_zero (RingNorm.eq_zero_of_map_eq_zero' _ _ hxy)

end Prelim

open scoped NNReal IntermediateField
section NontriviallyNormedField

open IntermediateField

universe u v

variable {K : Type u} [NontriviallyNormedField K] {L : Type v} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [hu : IsUltrametricDist K]

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any power-multiplicative `K`-algebra norm on `L` coincides
  with the spectral norm. -/
theorem spectralNorm_unique [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPowMul f) :
    f = spectralAlgNorm K L := by
  apply eq_of_powMul_faithful f hf_pm _ spectralAlgNorm_isPowMul
  intro x
  set E : Type v := id K⟮x⟯ with hEdef
  letI hE : Field E := by rw [hEdef, id_eq]; infer_instance
  letI : Algebra K E := K⟮x⟯.algebra
  letI hidE : ZeroHomClass (id ↥K⟮x⟯ →ₗ[K] ↥K⟮x⟯) _ _ := AddMonoidHomClass.toZeroHomClass
  set id1 : K⟮x⟯ →ₗ[K] E :=
    { toFun := id
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  set id2 : E →ₗ[K] K⟮x⟯ :=
    { toFun := id
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  set hs_norm : RingNorm E :=
    { toFun := fun y : E => spectralNorm K L (id2 y : L)
      map_zero' := by simp [map_zero, spectralNorm_zero, ZeroMemClass.coe_zero]
      add_le' := fun a b => by
        simp only [← spectralAlgNorm_def]
        exact map_add_le_add _ _ _
      neg' := fun a => by simp [map_neg, NegMemClass.coe_neg, ← spectralAlgNorm_def, map_neg_eq_map]
      mul_le' := fun a b => by
        simp only [← spectralAlgNorm_def]
        exact map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' := fun a ha => by
        simpa [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, ← spectralAlgNorm_def,
          map_eq_zero_iff_eq_zero, ZeroMemClass.coe_eq_zero] using ha }
  letI n1 : NormedRing E := RingNorm.toNormedRing hs_norm
  letI N1 : NormedSpace K E :=
    { one_smul := fun e => by simp [one_smul]
      mul_smul  := fun k1 k2 e => by simp [mul_smul]
      smul_zero := fun e => by simp
      smul_add  := fun k e_1 e_2 => by simp [smul_add]
      add_smul  := fun k_1 k_2 e => by simp [add_smul]
      zero_smul := fun e => by simp [zero_smul]
      norm_smul_le := fun k y => by
        change (spectralAlgNorm K L (id2 (k • y) : L) : ℝ) ≤
          ‖k‖ * spectralAlgNorm K L (id2 y : L)
        rw [map_smul, IntermediateField.coe_smul, map_smul_eq_mul] }
  set hf_norm : RingNorm K⟮x⟯ :=
    { toFun := fun y => f ((algebraMap K⟮x⟯ L) y)
      map_zero' := map_zero _
      add_le' := fun a b => map_add_le_add _ _ _
      neg' := fun y => by simp [(algebraMap K⟮x⟯ L).map_neg y]
      mul_le' := fun a b => map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' := fun a ha => by
        simpa [map_eq_zero_iff_eq_zero, map_eq_zero] using ha }
  letI n2 : NormedRing K⟮x⟯ := RingNorm.toNormedRing hf_norm
  letI N2 : NormedSpace K K⟮x⟯ :=
    { one_smul := fun e => by simp [one_smul]
      mul_smul  := fun k1 k2 e => by simp [mul_smul]
      smul_zero := fun e => by simp
      smul_add  := fun k e_1 e_2 => by simp [smul_add]
      add_smul  := fun k_1 k_2 e => by simp [add_smul]
      zero_smul := fun e => by simp [zero_smul]
      norm_smul_le := fun k y => by
        change (f ((algebraMap K⟮x⟯ L) (k • y)) : ℝ) ≤ ‖k‖ * f (algebraMap K⟮x⟯ L y)
        have : (algebraMap (↥K⟮x⟯) L) (k • y) = k • algebraMap (↥K⟮x⟯) L y := by
          simp [IntermediateField.algebraMap_apply]
        rw [this, map_smul_eq_mul] }
  haveI hKx_fin : FiniteDimensional K ↥K⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional K E := hKx_fin
  set Id1 : K⟮x⟯ →L[K] E := ⟨id1, id1.continuous_of_finiteDimensional⟩
  set Id2 : E →L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finiteDimensional⟩
  obtain ⟨C1, hC1_pos, hC1⟩ : ∃ C1 : ℝ, 0 < C1 ∧ ∀ y : K⟮x⟯, ‖id1 y‖ ≤ C1 * ‖y‖ :=
    Id1.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ : ∃ C2 : ℝ, 0 < C2 ∧ ∀ y : E, ‖id2 y‖ ≤ C2 * ‖y‖ :=
    Id2.isBoundedLinearMap.bound
  exact ⟨ C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y ↦ hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y ↦ hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any multiplicative ring norm on `L` extending the norm on
  `K` coincides with the spectral norm. -/
theorem spectralNorm_unique_field_norm_ext [CompleteSpace K]
    {f : AbsoluteValue L ℝ} (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) (x : L) :
    f x = spectralNorm K L x := by
  set g : AlgebraNorm K L :=
    { MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f with
      smul' := fun k x => by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
        rw [Algebra.smul_def, map_mul]
        congr
        rw [← hf_ext k]
        rfl
      mul_le' := fun x y => by
        simp [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] }
  have hg_pow : IsPowMul g := MulRingNorm.isPowMul _
  have hgx : f x = g x := rfl
  rw [hgx, spectralNorm_unique hg_pow, spectralAlgNorm_def]

/-- Given a nonzero `x : L`, the corresponding `seminormFromConst` can be regarded as an algebra
  norm, when one assumes that `(spectralAlgNorm h_alg hna) 1 ≤ 1`. -/
def algNormFromConst (h1 : (spectralAlgNorm K L).toRingSeminorm 1 ≤ 1) {x : L} (hx : x ≠ 0) :
    AlgebraNorm K L :=
  have hx' : spectralAlgNorm K L x ≠ 0 :=
    ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
  { normFromConst h1 hx' spectralAlgNorm_isPowMul with
    smul' := fun k y => by
      have h_mul : ∀ y : L, spectralNorm K L (algebraMap K L k * y) =
          spectralNorm K L (algebraMap K L k) * spectralNorm K L y := fun y ↦ by
        rw [spectralNorm_extends, ← Algebra.smul_def, ← spectralAlgNorm_def,
          map_smul_eq_mul _ _ _, spectralAlgNorm_def]
      have h : spectralNorm K L (algebraMap K L k) =
        seminormFromConst' h1 hx' isPowMul_spectralNorm (algebraMap K L k) := by
          rw [seminormFromConst_apply_of_isMul h1 hx' _ h_mul]; rfl
      rw [← @spectralNorm_extends K _ L _ _ k, Algebra.smul_def, h]
      exact seminormFromConst_isMul_of_isMul _ _ _ h_mul _ }

theorem algNormFromConst_def (h1 : (spectralAlgNorm K L).toRingSeminorm 1 ≤ 1) {x y : L}
    (hx : x ≠ 0) :
    algNormFromConst h1 hx y =
      seminormFromConst h1 (ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x)))
        isPowMul_spectralNorm y := rfl

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then the spectral norm on `L` is multiplicative. -/
theorem spectralAlgNorm_mul [CompleteSpace K] (x y : L) :
    spectralAlgNorm K L (x * y) = spectralAlgNorm K L x * spectralAlgNorm K L y := by
  by_cases hx : x = 0
  · simp [hx, zero_mul, map_zero]
  · have hx' : spectralAlgNorm K L x ≠ 0 :=
      ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
    have hf1 : (spectralAlgNorm K L) 1 ≤ 1 := le_of_eq spectralAlgNorm_one
    set f : AlgebraNorm K L := algNormFromConst hf1 hx with hf
    have hf_pow : IsPowMul f := seminormFromConst_isPowMul hf1 hx' isPowMul_spectralNorm
    rw [← spectralNorm_unique hf_pow, hf]
    simp [algNormFromConst_def]
    exact seminormFromConst_const_mul hf1 hx' isPowMul_spectralNorm _

variable (K L) in
/-- The spectral norm is a multiplicative `K`-algebra norm on `L`. -/
def spectralMulAlgNorm [CompleteSpace K] : MulAlgebraNorm K L :=
  { spectralAlgNorm K L with
    map_one' := spectralAlgNorm_one
    map_mul' := spectralAlgNorm_mul }

theorem spectralMulAlgNorm_def [CompleteSpace K]
    (x : L) : spectralMulAlgNorm K L x = spectralNorm K L x := rfl

namespace spectralNorm

variable (K L)

/-- `L` with the spectral norm is a `NormedField`. -/
def normedField [CompleteSpace K] : NormedField L :=
  { (inferInstance : Field L) with
    norm := fun x : L => (spectralNorm K L x : ℝ)
    dist := fun x y : L => (spectralNorm K L (x - y) : ℝ)
    dist_self := fun x => by simp [sub_self, spectralNorm_zero]
    dist_comm := fun x y => by
      rw [← neg_sub, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle := fun x y z =>
      sub_add_sub_cancel x y z ▸ isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg
    eq_of_dist_eq_zero := fun hxy => by
      rw [← sub_eq_zero]
      exact (map_eq_zero_iff_eq_zero (spectralMulAlgNorm K L)).mp hxy
    dist_eq := fun x y => by rfl
    norm_mul := fun x y => by simp [← spectralMulAlgNorm_def, map_mul]
    edist_dist := fun x y => by rw [ENNReal.ofReal_eq_coe_nnreal] }

/-- `L` with the spectral norm is a `normed_add_comm_group`. -/
def normedAddCommGroup [CompleteSpace K] : NormedAddCommGroup L := by
  haveI : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `seminormed_add_comm_group`. -/
def seminormedAddCommGroup [CompleteSpace K] : SeminormedAddCommGroup L := by
  have : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `normed_space` over `K`. -/
def normedSpace [CompleteSpace K] : @NormedSpace K L _ (seminormedAddCommGroup K L) :=
   letI _ := seminormedAddCommGroup K L
   {(inferInstance : Module K L) with
     norm_smul_le := fun r x => by
       change spectralAlgNorm K L (r • x) ≤ ‖r‖ * spectralAlgNorm K L x
       exact le_of_eq (map_smul_eq_mul _ _ _)}

/-- The metric space structure on `L` induced by the spectral norm. -/
def metricSpace [CompleteSpace K] : MetricSpace L := (normedField K L).toMetricSpace

/-- The uniform space structure on `L` induced by the spectral norm. -/
def uniformSpace [CompleteSpace K] : UniformSpace L := (metricSpace K L).toUniformSpace

/-- If `L/K` is finite dimensional, then `L` is a complete space with respect to topology induced
  by the spectral norm. -/
instance (priority := 100) completeSpace [CompleteSpace K] [h_fin : FiniteDimensional K L] :
    @CompleteSpace L (uniformSpace K L) := by
  letI := (normedAddCommGroup K L)
  letI := (normedSpace K L)
  exact FiniteDimensional.complete K L

end spectralNorm

end NontriviallyNormedField
