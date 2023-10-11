import RingTheory.DiscreteValuationRing.Basic

#align_import for_mathlib.discrete_valuation_ring

/-!
## Main result

* `ring_equiv.discrete_valuation_ring` shows that if a ring is equivalent to a DVR, it is itself
  a DVR
-/


theorem RingEquiv.discreteValuationRing {A B : Type _} [CommRing A] [IsDomain A]
    [DiscreteValuationRing A] [CommRing B] [IsDomain B] (e : A ≃+* B) : DiscreteValuationRing B :=
  { to_isPrincipalIdealRing := IsPrincipalIdealRing.of_surjective e.toRingHom e.Surjective
    to_localRing := e.LocalRing
    not_a_field' :=
      by
      have hA : LocalRing.maximalIdeal A ≠ ⊥ := DiscreteValuationRing.not_a_field A
      obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hA)
      rw [Submodule.ne_bot_iff]
      use e a
      constructor
      · erw [LocalRing.mem_maximalIdeal, map_mem_nonunits_iff (e : A →+* B), ←
          LocalRing.mem_maximalIdeal]
        exact a.2
      · rw [map_ne_zero_iff _ e.injective]
        simp only [Ne.def, Submodule.coe_eq_zero]; exact ha }

