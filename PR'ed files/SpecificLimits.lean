/-
Copyright (c) 2023 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

-- Everything in #11008

-- import Mathlib.Analysis.SpecificLimits.Basic
--
-- open NNReal Filter
--
-- open scoped NNReal Topology
--
-- theorem NNReal.lt_one_of_tendsto_pow_0 (a : ℝ≥0) (h : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)) :
--     a < 1 := by
--     simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe]
--         using tendsto_pow_atTop_nhds_zero_iff.mp <| tendsto_coe.mpr h
