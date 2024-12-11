/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
## Main result

* `ring_equiv.discrete_valuation_ring` shows that if a ring is equivalent to a DVR, it is itself
  a DVR
-/

theorem RingEquiv.discreteValuationRing {A B : Type _} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [DiscreteValuationRing A] (e : A ≃+* B) : DiscreteValuationRing B where
  principal := (isPrincipalIdealRing_iff _).1 <| IsPrincipalIdealRing.of_surjective
    e.toRingHom e.surjective
  __ : IsLocalRing B := e.isLocalRing
  not_a_field' := by
    have hA : IsLocalRing.maximalIdeal A ≠ ⊥ := DiscreteValuationRing.not_a_field A
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hA)
    rw [Submodule.ne_bot_iff]
    use e a
    constructor
    · erw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff (e : A →+* B), ←
        IsLocalRing.mem_maximalIdeal]
      exact a.2
    · apply (@map_ne_zero_iff _ _ _ _ e a).2
      simp only [ne_eq, Submodule.coe_eq_zero]; exact ha
