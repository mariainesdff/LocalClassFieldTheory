/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Tower

-- In PR #23252

namespace Polynomial

section CommRing

variable {K : Type*} [CommRing K] [IsSimpleRing K] {L : Type*} [CommRing L] [Nontrivial L]
  [Algebra K L]

-- DONE
-- [Mathlib.Algebra.Polynomial.RingDivision]
theorem natDegree_pos_of_monic_of_root {p : K[X]} (hp : p.Monic) {x : L} (hx : aeval x p = 0) :
    0 < p.natDegree :=
  natDegree_pos_of_aeval_root (ne_zero_of_ne_zero_of_monic one_ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap K L)).mp (algebraMap K L).injective)

-- DONE
-- [Mathlib.Algebra.Polynomial.Lifts]
theorem monic_of_eq_finprod (p : K[X]) {n : ℕ} (b : Fin n → L)
    (hp : mapAlg K L p = finprod fun k : Fin n ↦ X - C (b k)) : p.Monic := by
  have hprod : (finprod fun k : Fin n ↦ X - C (b k)).Monic := by
    rw [finprod_eq_prod_of_fintype]
    exact monic_prod_of_monic _ _ fun m _ ↦ monic_X_sub_C (b m)
  rw [← hp, mapAlg_eq_map] at hprod
  exact monic_of_injective (algebraMap K L).injective hprod

-- DONE
-- [Mathlib.Algebra.Polynomial.Lifts]
theorem monic_of_eq_multiset_prod (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (Multiset.map (fun a : L ↦ X - C a) s).prod) : p.Monic := by
  have hprod : (Multiset.map (fun a : L ↦ X - C a) s).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun m _ ↦ monic_X_sub_C m
  rw [← hp, mapAlg_eq_map] at hprod
  exact monic_of_injective (algebraMap K L).injective hprod

end CommRing

-- DONE
-- [Mathlib.Algebra.Polynomial.Basic]
theorem C_finset_sum {α : Type*} (s : Finset α) {K : Type*} [Semiring K] (b : α → K) :
    (s.sum fun x : α ↦ C (b x)) = C (s.sum b) := by
  classical
  refine s.induction_on ?_ ?_
  · simp [Finset.sum_empty, _root_.map_zero]
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hs, C_add]

-- DONE
-- [Mathlib.Algebra.Polynomial.Basic]
theorem C_finset_prod {α : Type*} (s : Finset α) {K : Type*} [CommSemiring K] (b : α → K) :
    (s.prod fun x : α ↦ C (b x)) = C (s.prod b) := by
  classical
  refine s.induction_on ?_ ?_
  · simp [Finset.prod_empty, map_one]
  · intro a s ha hs
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hs, C_mul]

-- DONE
-- [Mathlib.Algebra.Polynomial.BigOperators]
theorem prod_X_sub_C_natDegree {L : Type*} [CommRing L] [Nontrivial L] [NoZeroDivisors L] {n : ℕ}
    (b : Fin n → L) : (Finset.univ.prod fun i : Fin n ↦ X - C (b i)).natDegree = n := by
  rw [natDegree_prod _ _ fun m _ ↦ X_sub_C_ne_zero (b m)]
  simp [natDegree_X_sub_C, Finset.sum_const, Finset.card_fin, Algebra.id.smul_eq_mul, mul_one]

-- DONE
-- [Mathlib.Algebra.Polynomial.Splits]
theorem aeval_root {K L : Type*} [CommSemiring K] [CommRing L] [Algebra K L] (s : Multiset L)
    {x : L} (hx : x ∈ s) {p : K[X]}
    (hp : mapAlg K L p = (Multiset.map (fun a : L ↦ X - C a) s).prod) : aeval x p = 0 := by
  have : aeval x (mapAlg K L p) = aeval x p := by rw [mapAlg_eq_map, aeval_map_algebraMap]
  rw [← this, hp, coe_aeval_eq_eval]
  have hy : X - C x ∣ (Multiset.map (fun a : L ↦ X - C a) s).prod := by
    apply Multiset.dvd_prod
    simp [Multiset.mem_map, sub_right_inj, C_inj, exists_eq_right]
    exact hx
  rw [eval_eq_zero_of_dvd_of_eval_eq_zero hy]
  simp [eval_sub, eval_X, eval_C, sub_self]

end Polynomial
