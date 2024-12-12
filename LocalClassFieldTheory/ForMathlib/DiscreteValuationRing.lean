/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
## Main result

* `RingEquiv.discreteValuationRing` shows that if a ring is equivalent to a DVR, it is itself
  a DVR
-/

theorem RingEquiv.discreteValuationRing {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [DiscreteValuationRing A] (e : A ≃+* B) : DiscreteValuationRing B where
  principal := (isPrincipalIdealRing_iff _).1 <| IsPrincipalIdealRing.of_surjective _ e.surjective
  __ : IsLocalRing B := e.isLocalRing
  not_a_field' := by
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr
      <| DiscreteValuationRing.not_a_field A)
    rw [Submodule.ne_bot_iff]
    refine ⟨e a, ⟨?_, by simpa only [map_ne_zero_iff e, ne_eq, Submodule.coe_eq_zero]⟩⟩
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e, ← IsLocalRing.mem_maximalIdeal]
    exact a.2
