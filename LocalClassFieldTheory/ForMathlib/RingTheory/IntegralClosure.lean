import RingTheory.IntegralClosure

#align_import for_mathlib.ring_theory.integral_closure

/-!
# Integral closure

This file contains two lemmas about integral closures. 

# Main Results

* `is_integral_iff_of_equiv` : if `R` and `T` are isomorphic commutative rings and `S` is an
  `R`-algebra and a `T`-algebra in a compatible way, then an element `a ∈ S` is integral over `R`
  if and only if it is integral over `T`.
-/


open RingHom

theorem mem_integralClosure_iff (R A : Type _) [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    a ∈ integralClosure R A ↔ IsIntegral R a :=
  Iff.rfl

/- If `R` and `T` are isomorphic commutative rings and `S` is an `R`-algebra and a `T`-algebra in 
  a compatible way, then an element `a ∈ S` is integral over `R` if and only if it is integral
  over `T`.-/
theorem isIntegral_iff_of_equiv {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra T S] (φ : R ≃+* T)
    (h : (algebraMap T S).comp φ.toRingHom = algebraMap R S) (a : S) :
    IsIntegral R a ↔ IsIntegral T a :=
  by
  constructor <;> intro ha
  · rw [← id_apply a]
    refine' isIntegral_map_of_comp_eq_of_isIntegral φ.to_ring_hom (RingHom.id S) _ ha
    rw [id_comp, h]
  · rw [← id_apply a]
    refine' isIntegral_map_of_comp_eq_of_isIntegral φ.symm.to_ring_hom (RingHom.id S) _ ha
    rw [id_comp, ← h, comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom, comp_id]

