/-
Copyright (c) 2023 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Analysis.SpecificLimits.Basic

#align_import from_mathlib.specific_limits

open NNReal Filter

open scoped NNReal Topology

theorem NNReal.lt_one_of_tendsto_pow_0 (a : ℝ≥0) (h : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)) :
    a < 1 := by
  by_cases ha₀ : a = 0
  · rw [ha₀]; exact zero_lt_one
  · by_contra ha_le
    rw [not_lt] at ha_le 
    by_cases ha : a = 1
    · simp only [ha, one_pow] at h 
      exact zero_ne_one (tendsto_nhds_unique h tendsto_const_nhds)
    · replace h : tendsto (fun n : ℕ => (a : ENNReal) ^ n) at_top (𝓝 0)
      · rw [← ENNReal.coe_zero]
        simp_rw [← ENNReal.coe_pow, ENNReal.tendsto_coe]
        exact h
      set b : ENNReal := ↑a⁻¹ with hb
      replace h : tendsto (fun n : ℕ => b ^ n) at_top (𝓝 ⊤)
      · rw [hb, ENNReal.coe_inv ha₀]
        convert (@ENNReal.tendsto_inv_iff ℕ at_top (fun n => ↑a ^ n) 0).mpr h
        · funext n; exact ennreal.inv_pow.symm
        · simp only [ENNReal.inv_zero]
      have hb₁ : b < 1 := by
        rw [hb, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
        exact inv_lt_one (lt_of_le_of_ne ha_le (Ne.symm ha))
      exact
        ENNReal.zero_ne_top (tendsto_nhds_unique (ENNReal.tendsto_pow_atTop_nhds_0_of_lt_1 hb₁) h)

