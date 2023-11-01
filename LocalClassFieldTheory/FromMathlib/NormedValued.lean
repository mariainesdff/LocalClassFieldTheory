/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import LocalClassFieldTheory.FromMathlib.RankOneValuation
import LocalClassFieldTheory.FromMathlib.RingSeminorm
import Mathlib.Topology.Algebra.Valuation

#align_import from_mathlib.normed_valued

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `ValuedField.toNormedField` : the normed field structure determined by a rank one valuation.

## Main Results
* `real.exists_strict_mono_lt` : if `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is a strict
  monomorphism, then for any positive real `r`, there exists `d : Γ₀ˣ` with `f d < r`.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/


noncomputable section

open scoped NNReal

variable {K : Type _} [hK : NormedField K]

/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`. -/
def valuationFromNorm (h : IsNonarchimedean (norm : K → ℝ)) : Valuation K ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := h

theorem valuationFromNorm_apply (h : IsNonarchimedean (norm : K → ℝ)) (x : K) :
    valuationFromNorm h x = ‖x‖₊ :=
  rfl

/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
def NormedField.toValued (h : IsNonarchimedean (norm : K → ℝ)) : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    NonUnitalNormedRing.toNormedAddCommGroup with
    v := valuationFromNorm h
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      refine' ⟨fun h => _, fun h => _⟩
      · obtain ⟨ε, hε, h⟩ := h
        use Units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε)
        intro x hx
        exact h (mem_ball_zero_iff.mpr hx)
      · obtain ⟨ε, hε⟩ := h
        use(ε : ℝ), NNReal.coe_pos.mpr (Units.zero_lt _)
        intro x hx
        exact hε (mem_ball_zero_iff.mp hx) }

variable {L : Type _} [hL : Field L] {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : IsRankOne val.v]

/-- If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is a strict monomorphism, then for any positive
  `r : ℝ≥0`, there exists `d : Γ₀ˣ` with `f d < r`. -/
theorem NNReal.exists_strictMono_lt [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ ℝ≥0} (hf : StrictMono f)
    {r : ℝ≥0} (hr : 0 < r) : ∃ d : Γ₀ˣ, f d < r := by
  obtain ⟨g, hg1⟩ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mp h
  set u : Γ₀ˣ := if g < 1 then g else g⁻¹ with hu
  have hfu : f u < 1 := by
    rw [hu]
    split_ifs with hu1
    · rw [if_pos hu1, ← map_one f]; exact hf hu1
    · have hfg0 : f g ≠ 0 := by
        intro h0
        exact (Units.ne_zero g) ((map_eq_zero f).mp h0)
      have hg1' : 1 < g := lt_of_le_of_ne (not_lt.mp hu1) hg1.symm
      rw [if_neg hu1, Units.val_inv_eq_inv_val, map_inv₀, NNReal.inv_lt_one_iff hfg0, ← map_one f]
      exact hf hg1'
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hr hfu
  use u ^ n
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact hn

/-- If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is a strict monomorphism, then for any positive
  real `r`, there exists `d : Γ₀ˣ` with `f d < r`. -/
theorem Real.exists_strictMono_lt [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ ℝ≥0} (hf : StrictMono f) {r : ℝ}
    (hr : 0 < r) : ∃ d : Γ₀ˣ, (f d : ℝ) < r := by
  set s : NNReal := ⟨r, le_of_lt hr⟩
  have hs : 0 < s := hr
  exact NNReal.exists_strictMono_lt hf hs

namespace RankOneValuation

/-- The norm function determined by a rank one valuation on a field `L`. -/
def normDef : L → ℝ := fun x : L => hv.hom (Valued.v x)

theorem normDef_nonneg (x : L) : 0 ≤ normDef x := by simp only [normDef, NNReal.zero_le_coe]

theorem normDef_add_le (x y : L) : normDef (x + y) ≤ max (normDef x) (normDef y) :=
  by
  simp only [normDef, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' val.v _ _)

theorem normDef_eq_zero {x : L} (hx : normDef x = 0) : x = 0 := by
  simpa [normDef, NNReal.coe_eq_zero, isRankOne_hom_eq_zero_iff, Valuation.zero_iff] using hx

variable (L) (Γ₀)

/-- The normed field structure determined by a rank one valuation. -/
def ValuedField.toNormedField : NormedField L :=
  { hL with
    norm := normDef
    dist := fun x y => normDef (x - y)
    dist_self := fun x => by
      simp only [sub_self, normDef, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [normDef]; rw [← neg_sub, Valuation.map_neg]
    dist_triangle := fun x y z => by
      simp only [← sub_add_sub_cancel x y z]
      exact le_trans (normDef_add_le _ _)
        (max_le_add_of_nonneg (normDef_nonneg _) (normDef_nonneg _))
    edist_dist := fun x y => by simp only [ENNReal.ofReal_eq_coe_nnreal (normDef_nonneg _)]
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (normDef_eq_zero hxy)
    dist_eq := fun x y => rfl
    norm_mul' := fun x y => by simp only [normDef, ← NNReal.coe_mul, map_mul]
    toUniformSpace := Valued.toUniformSpace
    uniformity_dist := by
      letI : Nonempty { ε : ℝ // ε > 0 } := Set.nonempty_Ioi_subtype
      ext U
      rw [Filter.hasBasis_iff.mp (Valued.hasBasis_uniformity L Γ₀), iInf_subtype',
        Filter.mem_iInf_of_directed]
      · simp only [exists_true_left, Filter.mem_principal, Subtype.exists, gt_iff_lt,
          Subtype.coe_mk, exists_prop, true_and_iff]
        refine' ⟨fun h => _, fun h => _⟩
        · obtain ⟨ε, hε⟩ := h
          set δ : ℝ≥0 := hv.hom ε with hδ
          have hδ_pos : 0 < δ := by
            rw [hδ, ← map_zero hv.hom]
            exact hv.strictMono (Units.zero_lt ε)
          use δ, hδ_pos
          apply subset_trans _ hε
          intro x hx
          simp only [Set.mem_setOf_eq, normDef, hδ, NNReal.val_eq_coe, NNReal.coe_lt_coe] at hx
          rw [Set.mem_setOf, ← neg_sub, Valuation.map_neg]
          exact hv.strictMono.lt_iff_lt.mp hx
        · letI : Nontrivial Γ₀ˣ :=
            (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mpr
              ⟨isRankOneUnit val.v, isRankOneUnit_ne_one val.v⟩
          obtain ⟨r, hr_pos, hr⟩ := h
          obtain ⟨u, hu⟩ := Real.exists_strictMono_lt hv.strictMono hr_pos
          use u
          apply subset_trans _ hr
          intro x hx
          simp only [normDef, Set.mem_setOf_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe, ← neg_sub, Valuation.map_neg]
          exact hv.strictMono.lt_iff_lt.mpr hx
      · simp only [gt_iff_lt, ge_iff_le, Directed]
        intro x y
        use min x y
        simp only [Filter.le_principal_iff, Filter.mem_principal, Set.setOf_subset_setOf,
          Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩ }

end RankOneValuation
