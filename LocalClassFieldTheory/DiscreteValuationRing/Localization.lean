/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import LocalClassFieldTheory.DiscreteValuationRing.Basic

/-!
# Global-to-local results.

Let `R` be a Dedekind domain which is not a field, let `K` be a fraction field of `R` and let `v`
be a maximal ideal of `R`. We also prove that the  `v`-adic valuation on `K` is discrete.

We also show that the adic valuation on the completion `K_v` of `K` with respect to the `v`-adic
valuation is discrete, and that its unit ball `R_v` is a discrete valuation ring.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Valuation DiscreteValuation

open scoped Multiplicative

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem adicValuedIsDiscrete : IsDiscrete (@adicValued R _ _ K _ _ _ v).v := by
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v
  apply isDiscrete_of_exists_isUniformizer (π := π)
  rw [isUniformizer_iff, ← hπ]
  rfl

local notation "R_v" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

local notation "K_v" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v

theorem valuation_completion_exists_uniformizer :
    ∃ π : K_v, Valued.v π = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  use ↑x
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_def, ← hx,
    @Valued.extension_extends K _ ℤₘ₀ _ (adicValued v)]
  rfl

theorem valuation_completion_integers_exists_uniformizer :
    ∃ π : R_v, Valued.v (π : K_v) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := valuation_completion_exists_uniformizer R K v
  refine ⟨⟨x, ?_⟩, hx⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx]
  exact le_of_lt WithZero.ofAdd_neg_one_lt_one

/-- The valuation on the `v`-adic completion `K_v` of `K` is discrete. -/
instance isDiscrete : IsDiscrete (@Valued.v K_v _ ℤₘ₀ _ _) :=
  isDiscrete_of_exists_isUniformizer
    (valuation_completion_integers_exists_uniformizer R K v).choose_spec

/-- The unit ball `R_v` of `K_v` is a discrete valuation ring. -/
instance discreteValuationRing : IsDiscreteValuationRing R_v :=
  DiscreteValuation.dvr_of_isDiscrete (Valued.v  (R := K_v))

end IsDedekindDomain.HeightOneSpectrum
