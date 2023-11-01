/-
Copyright (c) 2023 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Analysis.SpecificLimits.Basic

#align_import from_mathlib.specific_limits

open NNReal Filter

open scoped NNReal Topology

theorem NNReal.lt_one_of_tendsto_pow_0 (a : ℝ≥0) (h : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)) :
    a < 1 := by
    rw [← tendsto_coe] at h
    have bla := (tendsto_pow_atTop_nhds_0_iff).1 h
    have foo := NNReal.abs_eq a
    rw [← val_eq_coe] at foo
    rw [foo] at bla
    have := NNReal.coe_one
    rw [← this] at bla
    rw [← NNReal.coe_lt_coe]
    exact bla
