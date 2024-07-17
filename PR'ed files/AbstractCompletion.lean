-- /-
-- Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-- -/
-- import Mathlib.Topology.UniformSpace.AbstractCompletion

-- #align_import for_mathlib.topology.uniform_space.abstract_completion

-- /-!
-- # Abstract completion
-- Let `f : α → β` be a continuous function between a uniform space `α` and a regular topological
-- space `β`, and let `pkg, pkg'` be two abstract completions of `α`. The main result is that
-- if for every point `a : pkg` the filter `f.map (coe⁻¹ (𝓝 a))` obtained by pushing forward with `f`
-- the preimage in `α` of `𝓝 a` tends to `𝓝 (f.extend a : β)`, then the comparison map
-- between `pkg` and `pkg'` composed with the extension of `f` to `pkg`` coincides with the
-- extension of `f` to `pkg'` -/

-- -- **FE** This is being PR'd in #12979

-- namespace AbstractCompletion

-- open scoped Topology

-- variable {α β : Type _} [UniformSpace α] [TopologicalSpace β]

-- variable (pkg : AbstractCompletion α) (pkg' : AbstractCompletion α)

-- theorem extend_compare_extend
--   [T3Space β] (f : α → β) (cont_f : Continuous f) :
--   let _ := pkg.uniformStruct.toTopologicalSpace
--   let _ := pkg'.uniformStruct.toTopologicalSpace
--   (_ : ∀ a : pkg.space,
--     Filter.Tendsto f (Filter.comap pkg.coe (𝓝 a)) (𝓝 ((pkg.denseInducing.extend f) a))) →
--     pkg.denseInducing.extend f ∘ pkg'.compare pkg = pkg'.denseInducing.extend f := by
--   let _ := pkg'.uniformStruct
--   let _ := pkg.uniformStruct
--   intro _ _ h
--   have : ∀ x : α, (pkg.denseInducing.extend f ∘ pkg'.compare pkg) (pkg'.coe x) = f x := by
--     simp only [Function.comp_apply, compare_coe, DenseInducing.extend_eq _ cont_f, implies_true]
--   apply (DenseInducing.extend_unique (AbstractCompletion.denseInducing _) this
--     (Continuous.comp _ (uniformContinuous_compare pkg' pkg).continuous )).symm
--   apply DenseInducing.continuous_extend
--   exact fun a => ⟨(pkg.denseInducing.extend f) a, h a⟩

-- end AbstractCompletion
