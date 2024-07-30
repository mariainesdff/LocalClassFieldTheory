/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

-- `FAE` the whole file is in PR #12179

import Mathlib.Order.Filter.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Discrete uniformity
This file contains generalities about Cauchy filters (and convergence theoref) in spaces endowed
with the discrete uniformity.

# Main Results

* `cauchy_discrete_is_constant` stating that a Cauchy filter in a discrete space is actually a
principal filter
* `ne_bot_unique_principal` saying that in a non-empty discrete space, two principal filters that
contain a non-trivial filter coincide
-/


namespace Set

theorem prod_subset_diag_singleton_left {X : Type _} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, S = {x} := by
  rcases hS, hT with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  refine ⟨s, eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨s, hs⟩, fun x hx ↦ ?_⟩⟩
  rw [prod_subset_iff] at h_diag
  replace hs := h_diag s hs t ht
  replace hx := h_diag x hx t ht
  simp only [idRel, mem_setOf_eq] at hx hs
  rwa [← hs] at hx

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_subset_idRel_Eq_singleton_right {X : Type _} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, T = {x} := by
  rw [Set.prod_subset_iff] at h_diag
  replace h_diag := fun x hx y hy ↦ (h_diag y hy x hx).symm
  exact prod_subset_diag_singleton_left hT hS (prod_subset_iff.mpr h_diag)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_subset_idRel_Eq_singleton {X : Type _} {S T : Set X} (hS : S.Nonempty) (hT : T.Nonempty)
    (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, S = {x} ∧ T = {x} := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := prod_subset_diag_singleton_left hS hT h_diag,
    prod_subset_idRel_Eq_singleton_right hS hT h_diag
  refine ⟨x, ⟨hx, ?_⟩⟩
  rw [hy, Set.singleton_eq_singleton_iff]
  exact
    (Set.prod_subset_iff.mp h_diag x (by simp only [hx, Set.mem_singleton]) y
        (by simp only [hy, Set.mem_singleton])).symm

end Set

section CauchyDiscrete

open Filter Set

open scoped Filter Topology


theorem cauchy_discrete_le_principal {X : Type _} {uX : UniformSpace X}
    (hX : uniformity X = 𝓟 idRel) {α : Filter X} (hα : Cauchy α) : ∃ x : X, α ≤ 𝓟 {x} := by
  rcases hα with ⟨α_ne_bot, α_le⟩
  rw [Filter.le_def] at α_le
  specialize α_le idRel
  simp only [Filter.le_def, hX, mem_principal, idRel_subset, mem_idRel, eq_self_iff_true,
    imp_true_iff, forall_true_left, Filter.mem_prod_iff] at α_le
  obtain ⟨_, ⟨hS, ⟨_, ⟨hT, H⟩⟩⟩⟩ := α_le
  obtain ⟨x, hx⟩ :=
    prod_subset_diag_singleton_left (@Filter.nonempty_of_mem X α α_ne_bot _ hS)
      (@Filter.nonempty_of_mem _ _ α_ne_bot _ hT) H
  use x
  rwa [Filter.le_principal_iff, ← hx]

/-- The constant to which a Cauchy filter in a discrete space converges.
-/
noncomputable def cauchy_discrete_is_constant {X : Type _} {_ : UniformSpace X}
    (hX : uniformity X = 𝓟 idRel) {α : Filter X} (hα : Cauchy α) : X :=
  (cauchy_discrete_le_principal hX hα).choose

theorem cauchy_discrete_le {X : Type _} {_ : UniformSpace X} (hX : uniformity X = 𝓟 idRel)
    {α : Filter X} (hα : Cauchy α) : α ≤ 𝓟 {cauchy_discrete_is_constant hX hα} :=
  Exists.choose_spec (cauchy_discrete_le_principal hX hα)

theorem neBot_unique_principal {X : Type _} [UniformSpace X] (hX : uniformity X = 𝓟 idRel)
    {α : Filter X} (hα : α.NeBot) {x y : X} (hx : α ≤ 𝓟 {x}) (hy : α ≤ 𝓟 {y}) : x = y := by
  have h_disc : DiscreteTopology X := by
    apply discreteTopology_of_discrete_uniformity hX
  have t2X := @DiscreteTopology.toT2Space X _ h_disc
  apply @eq_of_nhds_neBot X _ t2X x y
  simp only [discreteTopology_iff_nhds.mp h_disc]
  apply @neBot_of_le _ _ _ hα
  simp only [le_inf_iff, le_pure_iff]
  exact ⟨le_principal_iff.mp hx, le_principal_iff.mp hy⟩

end CauchyDiscrete
