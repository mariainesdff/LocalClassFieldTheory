/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Topology.Instances.NNReal

#align_import from_mathlib.filter

/-!
# Limits of monotone and antitone sequences

We prove some auxiliary results about limits of `ℝ`-valued and `ℝ≥0`-valued sequences.

## Main Results

* `Real.tendsto_of_is_bounded_antitone` : an antitone, bounded below sequence `f : ℕ → ℝ` has a
  finite limit.
* `NNReal.tendsto_of_is_bounded_antitone` : an antitone sequence `f : ℕ → ℝ≥0` has a finite limit.

## Tags

glb, monotone, antitone, tendsto
-/


open scoped Filter Topology

/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
theorem Real.exists_isGLB {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S) : ∃ x, IsGLB S x := by
  set T := -S
  have hT_ne : T.Nonempty := Set.nonempty_neg.mpr hne
  have hT_bdd : BddAbove T := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB T hT_ne hT_bdd)
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB T hT_ne hT_bdd)

/-- An monotone, bounded above sequence `f : ℕ → ℝ` has a finite limit. -/
theorem Filter.tendsto_of_is_bounded_monotone {f : ℕ → ℝ} (h_bdd : BddAbove (Set.range f))
    (h_mon : Monotone f) : ∃ r : ℝ, Filter.Tendsto f Filter.atTop (𝓝 r) := by
  obtain ⟨B, hB⟩ := Real.exists_isLUB (Set.range f) (Set.range_nonempty f) h_bdd
  exact ⟨B, tendsto_atTop_isLUB h_mon hB⟩

/-- An antitone, bounded below sequence `f : ℕ → ℝ` has a finite limit. -/
theorem Real.tendsto_of_is_bounded_antitone {f : ℕ → ℝ} (h_bdd : BddBelow (Set.range f))
    (h_ant : Antitone f) : ∃ r : ℝ, Filter.Tendsto f Filter.atTop (𝓝 r) := by
  obtain ⟨B, hB⟩ := Real.exists_isGLB (Set.range_nonempty f) h_bdd
  exact ⟨B, tendsto_atTop_isGLB h_ant hB⟩

/-- An antitone sequence `f : ℕ → ℝ≥0` has a finite limit. -/
theorem NNReal.tendsto_of_is_bounded_antitone {f : ℕ → NNReal} (h_ant : Antitone f) :
    ∃ r : NNReal, Filter.Tendsto f Filter.atTop (𝓝 r) := by
  have h_bdd_0 : (0 : ℝ) ∈ lowerBounds (Set.range fun n : ℕ => (f n : ℝ)) :=
    by
    intro r hr
    obtain ⟨n, hn⟩ := Set.mem_range.mpr hr
    simp_rw [← hn]
    exact NNReal.coe_nonneg _
  have h_bdd : BddBelow (Set.range fun n => (f n : ℝ)) := ⟨0, h_bdd_0⟩
  obtain ⟨L, hL⟩ := Real.tendsto_of_is_bounded_antitone h_bdd h_ant
  have hL0 : 0 ≤ L :=
    haveI h_glb : IsGLB (Set.range fun n => (f n : ℝ)) L := isGLB_of_tendsto_atTop h_ant hL
    (le_isGLB_iff h_glb).mpr h_bdd_0
  use⟨L, hL0⟩
  rw [← NNReal.tendsto_coe]
  exact hL
