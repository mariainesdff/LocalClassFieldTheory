/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import LocalClassFieldTheory.FromMathlib.SpectralNorm
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unique norm extension theorem

Let `K` be a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
`L/K` be an algebraic extension. We show that the spectral norm on `L` is a nonarchimedean
multiplicative norm, and any power-multiplicative `K`-algebra norm on `L` coincides with the
spectral norm. More over, if `L/K` is finite, then `L` is a complete space.
This result is <[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Theorem 3.2.4/2]>.

## Main Definitions

* `spectral_mul_alg_norm` : the spectral norm is a multiplicative `K`-algebra norm on `L`.

## Main Results
* `spectral_norm_unique'` : any power-multiplicative `K`-algebra norm on `L` coincides with the
  spectral norm.
* `spectral_norm_is_mul` : the spectral norm on `L` is multiplicative.
* `spectral_norm_complete_space` : if `L/K` is finite dimensional, then `L` is a complete space
  with respect to topology induced by the spectral norm.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, unique, seminorm, norm, nonarchimedean
-/


noncomputable section

open scoped NNReal IntermediateField

variable {K : Type _} [NontriviallyNormedField K] {L : Type _} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any power-multiplicative `K`-algebra norm on `L` coincides
  with the spectral norm. -/
theorem spectral_norm_unique' [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hna : IsNonarchimedean (norm : K → ℝ)) : f = spectralAlgNorm hna := by
  apply eq_of_powMul_faithful f hf_pm _ (spectralAlgNorm_isPowMul hna)
  intro x
  set E : Type _ := id K⟮x⟯ with hEdef
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
      map_zero' := by
        simp only [map_zero, spectralNorm_zero, ZeroMemClass.coe_zero]
      add_le' := fun a b => by
        simp only [← spectralAlgNorm_def hna, Subfield.coe_add]; exact map_add_le_add _ _ _
      neg' := fun a => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, map_neg, LinearMap.coe_mk,
          NegMemClass.coe_neg, ← spectralAlgNorm_def hna, map_neg_eq_map]
      mul_le' := fun a b => by
        simp only [← spectralAlgNorm_def hna, Subfield.coe_mul]; exact map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' := fun a ha => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, ← spectralAlgNorm_def hna,
          map_eq_zero_iff_eq_zero, ZeroMemClass.coe_eq_zero] at ha
        exact ha }
  letI n1 : NormedRing E := normToNormedRing hs_norm
  letI N1 : NormedSpace K E :=
    { --K⟮x⟯.algebra with --TODO: Fix
      one_smul := fun e => by simp only [one_smul]
      mul_smul  := fun k1 k2 e => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, mul_smul]
      smul_zero := fun e => by simp only [id_eq, smul_eq_zero, or_true]
      smul_add  := fun k e_1 e_2 => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, smul_add]
      add_smul  := fun k_1 k_2 e => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, add_smul]
      zero_smul := fun e => by simp only [id_eq, zero_smul]
      norm_smul_le := fun k y => by
        change (spectralAlgNorm hna (id2 (k • y) : L) : ℝ) ≤
          ‖k‖ * spectralAlgNorm hna (id2 y : L)
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, map_smul, LinearMap.coe_mk]
        rw [IntermediateField.coe_smul, map_smul_eq_mul] }
  set hf_norm : RingNorm K⟮x⟯ :=
    { toFun := fun y => f ((algebraMap K⟮x⟯ L) y)
      map_zero' := map_zero _
      add_le' := fun a b => map_add_le_add _ _ _
      neg' := fun y => by
        simp only [(algebraMap K⟮x⟯ L).map_neg y,
          map_neg_eq_map (f := f) ((algebraMap K⟮x⟯ L) y)]
      mul_le' := fun a b => map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' := fun a ha => by
        simp only [map_eq_zero_iff_eq_zero, map_eq_zero] at ha
        exact ha }
  letI n2 : NormedRing K⟮x⟯ := normToNormedRing hf_norm
  letI N2 : NormedSpace K K⟮x⟯ :=
    { K⟮x⟯.algebra with --TODO: Fix
      one_smul := fun e => by simp only [one_smul]
      mul_smul  := fun k1 k2 e => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, mul_smul]
      smul_zero := fun e => by simp only [id_eq, smul_eq_zero, or_true]
      smul_add  := fun k e_1 e_2 => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, smul_add]
      add_smul  := fun k_1 k_2 e => by
        simp only [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, add_smul]
      zero_smul := fun e => by simp only [id_eq, zero_smul]
      norm_smul_le := fun k y => by
        change (f ((algebraMap K⟮x⟯ L) (k • y)) : ℝ) ≤ ‖k‖ * f (algebraMap K⟮x⟯ L y)
        have : (algebraMap (↥K⟮x⟯) L) (k • y) = k • algebraMap (↥K⟮x⟯) L y := by
          simp only [IntermediateField.algebraMap_apply]
          rfl
        rw [this, map_smul_eq_mul] }
  haveI hKx_fin : FiniteDimensional K ↥K⟮x⟯ :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional K E := hKx_fin
  set Id1 : K⟮x⟯ →L[K] E := ⟨id1, id1.continuous_of_finiteDimensional⟩
  set Id2 : E →L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finiteDimensional⟩
  have hC1 : ∃ C1 : ℝ, 0 < C1 ∧ ∀ y : K⟮x⟯, ‖id1 y‖ ≤ C1 * ‖y‖ := Id1.isBoundedLinearMap.bound
  have hC2 : ∃ C2 : ℝ, 0 < C2 ∧ ∀ y : E, ‖id2 y‖ ≤ C2 * ‖y‖ := Id2.isBoundedLinearMap.bound
  obtain ⟨C1, hC1_pos, hC1⟩ := hC1
  obtain ⟨C2, hC2_pos, hC2⟩ := hC2
  use C2, C1, hC2_pos, hC1_pos
  rw [forall_and]
  constructor
  · intro y; exact hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩
  · intro y; exact hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any multiplicative ring norm on `L` extending the norm on
  `K` coincides with the spectral norm. -/
theorem spectralNorm_unique_field_norm_ext [CompleteSpace K]
    {f : MulRingNorm L} (hf_ext : FunctionExtends (norm : K → ℝ) f)
    (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) : f x = spectralNorm K L x := by
  set g : AlgebraNorm K L :=
    { f with
      smul' := fun k x => by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
        rw [Algebra.smul_def, map_mul]
        congr
        rw [← hf_ext k]
        rfl
      mul_le' := fun x y => by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_mul_le_mul] }
  have hg_pow : IsPowMul g := MulRingNorm.isPowMul _
  have hgx : f x = g x := rfl
  rw [hgx, spectral_norm_unique' hg_pow hna]; rfl

/-- `seminormFromConst` can be regarded as an algebra norm, when one assumes that
`(spectral_alg_norm h_alg hna).to_ring_seminorm 1 ≤ 1` and `0 ≠ spectral_alg_norm h_alg hna x`
for some `x : L` -/
def algNormFromConst (hna : IsNonarchimedean (norm : K → ℝ))
    (h1 : (spectralAlgNorm (L := L) hna).toRingSeminorm 1 ≤ 1) {x : L}
    (hx : spectralAlgNorm hna x ≠ 0) : AlgebraNorm K L :=
  { normFromConst h1 hx (spectralAlgNorm_isPowMul hna) with
    smul' := fun k y => by
      have h_mul :
        ∀ y : L,
          spectralNorm K L (algebraMap K L k * y) =
            spectralNorm K L (algebraMap K L k) * spectralNorm K L y := by
        intro y
        rw [spectralNorm_extends, ← Algebra.smul_def, ← spectralAlgNorm_def hna,
          map_smul_eq_mul _ _ _]
        rfl
      have h : spectralNorm K L (algebraMap K L k) =
          seminormFromConst' h1 hx (spectralNorm_isPowMul hna) (algebraMap K L k) :=
        by rw [seminormFromConst_apply_of_isMul h1 hx _ h_mul]; rfl
      simp only [RingSeminorm.toFun_eq_coe, seminormFromConstRingNormOfField_def]
      rw [← @spectralNorm_extends K _ L _ _ k, Algebra.smul_def, h]
      exact seminormFromConst_isMul_of_isMul _ _ _ h_mul _ }

theorem algNormFromConst_def (hna : IsNonarchimedean (norm : K → ℝ))
    (h1 : (spectralAlgNorm (L := L) hna).toRingSeminorm 1 ≤ 1) {x y : L}
    (hx : spectralAlgNorm hna x ≠ 0) :
    algNormFromConst hna h1 hx y =
      seminormFromConst h1 hx (spectralNorm_isPowMul hna) y :=
  rfl

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then the spectral norm on `L` is multiplicative. -/
theorem spectral_norm_is_mul [CompleteSpace K] (hna : IsNonarchimedean (norm : K → ℝ)) (x y : L) :
    spectralAlgNorm hna (x * y) =
      spectralAlgNorm hna x * spectralAlgNorm hna y := by
  by_cases hx : spectralAlgNorm hna x = 0
  · rw [hx, MulZeroClass.zero_mul]
    rw [map_eq_zero_iff_eq_zero] at hx ⊢
    rw [hx, MulZeroClass.zero_mul]
  · have hf1 : (spectralAlgNorm (L := L) hna) 1 ≤ 1 :=
      spectralAlgNorm_is_norm_le_one_class hna
    set f : AlgebraNorm K L := algNormFromConst hna hf1 hx with hf
    have hf_pow : IsPowMul f :=
      seminormFromConst_isPowMul hf1 hx (spectralNorm_isPowMul hna)
    rw [← spectral_norm_unique' hf_pow, hf]
    simp only [algNormFromConst_def]
    exact seminormFromConst_const_mul hf1 hx (spectralNorm_isPowMul hna) _

/-- The spectral norm is a multiplicative `K`-algebra norm on `L`.-/
def spectralMulAlgNorm [CompleteSpace K] (hna : IsNonarchimedean (norm : K → ℝ)) :
    MulAlgebraNorm K L :=
  { spectralAlgNorm hna with
    map_one' := spectralAlgNorm_is_norm_one_class hna
    map_mul' := spectral_norm_is_mul hna }

theorem spectral_mul_ring_norm_def [CompleteSpace K] (hna : IsNonarchimedean (norm : K → ℝ))
    (x : L) : spectralMulAlgNorm hna x = spectralNorm K L x :=
  rfl

/-- `L` with the spectral norm is a `normed_field`. -/
def spectralNormToNormedField [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) :
    NormedField L :=
  { (inferInstance : Field L) with
    norm := fun x : L => (spectralNorm K L x : ℝ)
    dist := fun x y : L => (spectralNorm K L (x - y) : ℝ)
    dist_self := fun x => by simp only [sub_self, spectralNorm_zero]
    dist_comm := fun x y => by simp only [dist]; rw [← neg_sub, spectralNorm_neg h
      (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle := fun x y z => by
      simp only [dist_eq_norm]
      rw [← sub_add_sub_cancel x y z]
      apply IsNonarchimedean.add_le spectralNorm_nonneg (spectralNorm_isNonarchimedean h)
    eq_of_dist_eq_zero := fun hxy => by
      simp only [← spectral_mul_ring_norm_def h] at hxy
      rw [← sub_eq_zero]
      exact (map_eq_zero_iff_eq_zero (spectralMulAlgNorm h)).mp hxy
    dist_eq := fun x y => by rfl
    norm_mul := fun x y => by
      simp only [← spectral_mul_ring_norm_def h]; exact map_mul _ _ _
    edist_dist := fun x y => by
      simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe]
      rw [ENNReal.ofReal_eq_coe_nnreal] }

/-- `L` with the spectral norm is a `normed_add_comm_group`. -/
def spectralNormToNormedAddCommGroup [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) :
     NormedAddCommGroup L := by
  haveI : NormedField L := spectralNormToNormedField h
  infer_instance

/-- `L` with the spectral norm is a `seminormed_add_comm_group`. -/
def spectralNormToSeminormedAddCommGroup [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) :
    SeminormedAddCommGroup L := by
  have : NormedField L := spectralNormToNormedField h
  infer_instance

/-- `L` with the spectral norm is a `normed_space` over `K`. -/
def spectralNormToNormedSpace [CompleteSpace K]
    (h : IsNonarchimedean (norm : K → ℝ)) :
    @NormedSpace K L _ (spectralNormToSeminormedAddCommGroup h) :=
   letI _ := spectralNormToSeminormedAddCommGroup (L := L) h
   {(inferInstance : Module K L) with
     norm_smul_le := fun r x => by
       change spectralAlgNorm h (r • x) ≤ ‖r‖ * spectralAlgNorm h x
       exact le_of_eq (map_smul_eq_mul _ _ _)}

/-- The metric space structure on `L` induced by the spectral norm. -/
def ms [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) : MetricSpace L :=
  (spectralNormToNormedField h).toMetricSpace

/-- The uniform space structure on `L` induced by the spectral norm. -/
def us [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) : UniformSpace L :=
  (ms h).toUniformSpace

-- normed_field.to_uniform_space
/-- If `L/K` is finite dimensional, then `L` is a complete space with respect to topology induced
  by the spectral norm. -/
instance (priority := 100) spectral_norm_completeSpace [CompleteSpace K]
    (h : IsNonarchimedean (norm : K → ℝ)) [h_fin : FiniteDimensional K L] :
    @CompleteSpace L (us h) := by
  letI := (spectralNormToNormedAddCommGroup (L := L) h)
  letI := (spectralNormToNormedSpace (L := L) h)
  exact FiniteDimensional.complete K L
