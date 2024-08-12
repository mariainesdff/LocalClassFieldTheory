/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral closure

This file contains two lemmas about integral closures.

# Main Results

* `is_integral_iff_of_equiv` : if `R` and `T` are isomorphic commutative rings and `S` is an
  `R`-algebra and a `T`-algebra in a compatible way, then an element `a ∈ S` is integral over `R`
  if and only if it is integral over `T`.
-/

-- In PR #15738


open RingHom
-- [Mathlib.RingTheory.IntegralClosure.Algebra.Basic]
theorem mem_integralClosure_iff (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    a ∈ integralClosure R A ↔ IsIntegral R a :=
  Iff.rfl

-- [Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic]
/- If `R` and `T` are isomorphic commutative rings and `S` is an `R`-algebra and a `T`-algebra in
  a compatible way, then an element `a ∈ S` is integral over `R` if and only if it is integral
  over `T`.-/
theorem isIntegral_iff_of_equiv {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra T S] (φ : R ≃+* T)
    (h : (algebraMap T S).comp φ.toRingHom = algebraMap R S) (a : S) :
    IsIntegral R a ↔ IsIntegral T a := by
  constructor <;> intro ha
  · rw [← id_apply a]
    refine IsIntegral.map_of_comp_eq φ.toRingHom (RingHom.id S) ?_ ha
    rw [id_comp, h]
  · rw [← id_apply a]
    refine IsIntegral.map_of_comp_eq φ.symm.toRingHom (RingHom.id S) ?_ ha
    rw [id_comp, ← h, comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom, comp_id]
