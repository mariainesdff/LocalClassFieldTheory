/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Polynomial.IrreducibleRing

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]

open Polynomial


section Polynomial

noncomputable def Polynomial.mapAlgHom  {A R S : Type*} [CommRing A] [Semiring R] [Algebra A R]
    [Semiring S] [Algebra A S] (f : R →+* S)
    (hf : ∀ a, f ((algebraMap A R) a) = (algebraMap A S) a) : R[X] →ₐ[A] S[X] where
  toFun := Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero'    := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one'     := Polynomial.map_one f
  commutes' a  := by simp only [algebraMap_apply, map_C, hf]

lemma Polynomial.mapAlgHom_eq {A R S : Type*} [CommRing A] [Semiring R] [Algebra A R]
    [Semiring S] [Algebra A S] (f : R →+* S)
    (hf : ∀ a, f ((algebraMap A R) a) = (algebraMap A S) a) :
    Polynomial.mapAlgHom f hf = Polynomial.map f := rfl

end Polynomial
namespace DiscreteValuationRing

local notation "k" => LocalRing.ResidueField A

namespace AdjoinRoot

lemma degree_ne_zero_of_irreducible {f : A[X]}
    (hf : Irreducible (map (algebraMap A k) f))  :
    f.degree ≠ 0 := by
  intro h0
  rw [eq_C_of_degree_eq_zero h0, map_C] at hf
  exact (Polynomial.not_irreducible_C _) hf

lemma irreducible_of_irreducible_quot {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (LocalRing.residue A) f)) : Irreducible f :=
  letI : (nilradical A).IsPrime := by
    simp only [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.isPrime_iff_bot_or_prime, true_or]
  Monic.irreducible_of_irreducible_map_of_isPrime_nilradical (LocalRing.residue A) f hf1 hf

lemma isDomain_of_irreducible {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (LocalRing.residue A) f)) :
    IsDomain (AdjoinRoot f) := by
  simp only [AdjoinRoot, Ideal.Quotient.isDomain_iff_prime]
  rw [Ideal.span_singleton_prime]
  · exact irreducible_iff_prime.mp (irreducible_of_irreducible_quot hf1 hf)
  · intro hf0
    simp only [hf0, Polynomial.map_zero, not_irreducible_zero] at hf

section Foo

noncomputable def ResidueField_to_AdjoinRoot_quot' (f : A[X]) (π : A) :
    k → AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} := fun x ↦
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))
    (AdjoinRoot.of f) (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose
namespace ResidueField_to_AdjoinRoot_quot'

protected lemma map_one (f : A[X]) {π : A} (hπ : Irreducible π) :
    ResidueField_to_AdjoinRoot_quot' f π 1 = 1 := by
  set x1 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 1).choose
  have h1 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 1).choose_spec
  simp only [ResidueField_to_AdjoinRoot_quot', RingHom.coe_comp, Function.comp_apply,
    ← map_one (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_one (AdjoinRoot.of f), ← map_sub,
    Ideal.mem_span_singleton]
  have hdvd : π ∣ (x1 - 1) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Irreducible.maximalIdeal_eq hπ, h1, map_one]
  rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
  obtain ⟨c, hc⟩ := hdvd
  use (AdjoinRoot.of f) c
  rw [← map_mul, ← hc]

protected lemma map_zero (f : A[X]) {π : A} (hπ : Irreducible π) :
    ResidueField_to_AdjoinRoot_quot' f π 0 = 0 := by
  set x0 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 0).choose
  have h0 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 0).choose_spec
  simp only [ResidueField_to_AdjoinRoot_quot', RingHom.coe_comp, Function.comp_apply,
    ← map_zero (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_zero (AdjoinRoot.of f), ← map_sub,
    Ideal.mem_span_singleton]
  have hdvd : π ∣ (x0 - 0) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Irreducible.maximalIdeal_eq hπ, h0, map_zero]
  rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
  obtain ⟨c, hc⟩ := hdvd
  use (AdjoinRoot.of f) c
  rw [← map_mul, ← hc]

protected lemma map_add (f : A[X]) {π : A} (hπ : Irreducible π)
    (x y : k) :  ResidueField_to_AdjoinRoot_quot' f π (x + y) =
      ResidueField_to_AdjoinRoot_quot' f π x + ResidueField_to_AdjoinRoot_quot' f π y := by
  letI : AddHomClass (AdjoinRoot f →+* AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π}) _ _ :=
    AddMonoidHomClass.toAddHomClass -- Otherwise this times out
  set x' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose
  set y' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose
  set xy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x + y)).choose
  set hx' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose_spec
  set hy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose_spec
  set hxy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x + y)).choose_spec
  simp only [ResidueField_to_AdjoinRoot_quot', RingHom.coe_comp, Function.comp_apply]
  rw [← map_add, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_add, ← map_sub,
    Ideal.mem_span_singleton]
  have hdvd : π ∣ (xy' - (x' + y')) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Irreducible.maximalIdeal_eq hπ, map_add, hx', hy', hxy']
  rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
  obtain ⟨c, hc⟩ := hdvd
  use (AdjoinRoot.of f) c
  rw [← map_mul, ← hc]

protected lemma map_mul (f : A[X]) {π : A} (hπ : Irreducible π)
    (x y : k) :  ResidueField_to_AdjoinRoot_quot' f π (x * y) =
      ResidueField_to_AdjoinRoot_quot' f π x * ResidueField_to_AdjoinRoot_quot' f π y := by
  set x' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose
  set y' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose
  set xy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x*y)).choose
  set hx' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose_spec
  set hy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose_spec
  set hxy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x*y)).choose_spec
  simp only [ResidueField_to_AdjoinRoot_quot', RingHom.coe_comp, Function.comp_apply, ← map_mul,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, Ideal.mem_span_singleton]
  have hdvd : π ∣ (xy' - x'*y') := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Irreducible.maximalIdeal_eq hπ, map_mul, hx', hy', hxy']
  rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
  obtain ⟨c, hc⟩ := hdvd
  use (AdjoinRoot.of f) c
  rw [← map_mul, ← hc]

end ResidueField_to_AdjoinRoot_quot'

noncomputable def ResidueField_to_AdjoinRoot_quot (f : A[X]) {π : A} (hπ : Irreducible π) :
    k →+* AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} where
  toFun     := ResidueField_to_AdjoinRoot_quot' f π
  map_one'  := ResidueField_to_AdjoinRoot_quot'.map_one f hπ
  map_mul'  := ResidueField_to_AdjoinRoot_quot'.map_mul f hπ
  map_zero' := ResidueField_to_AdjoinRoot_quot'.map_zero f hπ
  map_add'  := ResidueField_to_AdjoinRoot_quot'.map_add f hπ

noncomputable def foo (f : A[X]) (π : A) : AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} →
    AdjoinRoot (map (LocalRing.residue A) f) := fun p ↦
  let p'' := (Ideal.Quotient.mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) p).choose
  let p' := (Ideal.Quotient.mk_surjective (I := Ideal.span {f}) p'').choose
  Ideal.Quotient.mk (Ideal.span {(Polynomial.map (LocalRing.residue A) f)})
    (Polynomial.map (Ideal.Quotient.mk (LocalRing.maximalIdeal A)) p')

open Ideal.Quotient

lemma foo_aux1 (f : A[X]) : ∀ a ∈ Ideal.span {f},
    ((Ideal.Quotient.mkₐ ℤ (Ideal.span {map (LocalRing.residue A) f})).comp
      (mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) a = 0 := by
  intro a ha
  rw [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_left] at ha
  obtain ⟨c, hac⟩ := ha
  rw [hac, map_mul]
  apply mul_eq_zero_of_right
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_zero (Ideal.Quotient.mk
    (Ideal.span {map (LocalRing.residue A) f})), mk_eq_mk_iff_sub_mem, sub_zero]
  exact Ideal.mem_span_singleton_self _

lemma foo_aux2 (f : A[X]) (π : A) (hπ : Irreducible π) : ∀ a ∈ Ideal.span {(AdjoinRoot.of f) π},
    (liftₐ (Ideal.span {f}) ((mkₐ ℤ (Ideal.span {map (LocalRing.residue A) f})).comp
      (mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
    (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) (foo_aux1 f)) a = 0 := by
  intro a ha
  rw [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_left] at ha
  obtain ⟨c, hac⟩ := ha
  rw [hac, map_mul]
  apply mul_eq_zero_of_right

  have hC : C ((Ideal.Quotient.mk (LocalRing.maximalIdeal A)) π) = 0 := sorry

  have : ((mkₐ ℤ (Ideal.span {map (LocalRing.residue A) f})).comp
        (mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) (C π) = 0 := by

    simp only [AlgHom.coe_comp, mkₐ_eq_mk, Function.comp_apply]
    rw [Polynomial.mapAlgHom_eq]
    simp only [map_C]
    rw [← map_zero ((Ideal.Quotient.mk (Ideal.span {map (LocalRing.residue A) f})))]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_zero, Ideal.mem_span_singleton]


    sorry

  rw [← AdjoinRoot.mk_C]
  rw [Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  exact this
  /- have : (↑((mkₐ ℤ (Ideal.span {map (LocalRing.residue A) f})).comp
          (mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
          (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) : RingHom _ _) =
        ((mkₐ ℤ (Ideal.span {map (LocalRing.residue A) f})).toRingHom.comp
          (mapRingHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A)))) := rfl
  simp_rw [this]

  rw [lift]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.toAddMonoidHom_eq_coe, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] -/
  --rw [Ideal.Quotient.lift_mk]
  --erw [this]
  --rw [Ideal.Quotient.lift_mk]
  /- rw [← map_zero (liftₐ (Ideal.span {f}) _ (foo_aux1 f))]
  rw [← mk_singleton_self]
  simp only [liftₐ_apply]
  rw [lift_mk]
  --simp_rw [AlgHom.comp_apply]
  simp only [RingHom.coe_coe, AlgHom.coe_comp, mkₐ_eq_mk, Function.comp_apply]
  simp only [mapAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] -/
  --rw [Ideal.Quotient.lift_mk]
  --sorry
#exit
noncomputable def foo' (f : A[X]) (π : A) : AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} →+*
    AdjoinRoot (map (LocalRing.residue A) f) :=
  (Ideal.Quotient.liftₐ (Ideal.span {(AdjoinRoot.of f) π}) (Ideal.Quotient.liftₐ (Ideal.span {f})
    ((Ideal.Quotient.mkₐ ℤ (Ideal.span {(Polynomial.map (LocalRing.residue A) f)})).comp
      (Polynomial.mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) (foo_aux1 f))
        (foo_aux2 f π)).toRingHom


noncomputable def foo'' (f : A[X]) (π : A) : AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} →ₐ[ℤ]
    AdjoinRoot (map (LocalRing.residue A) f) := by
  refine Ideal.Quotient.liftₐ (Ideal.span {(AdjoinRoot.of f) π})
    (Ideal.Quotient.liftₐ (Ideal.span {f})
      ((Ideal.Quotient.mkₐ ℤ (Ideal.span {(Polynomial.map (LocalRing.residue A) f)})).comp
        (Polynomial.mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) ?_) ?_

  · intro a ha
    --simp? [ha]
    --rw [AlgHom.comp_apply]
    --simp? [Ideal.Quotient.mkₐ_eq_mk]
    sorry
  · intro a ha
    sorry
  --apply Ideal.Quotient.lift_m (Ideal.span {(AdjoinRoot.of f) π})
  /- let p'' := (Ideal.Quotient.mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) p).choose
  let p' := (Ideal.Quotient.mk_surjective (I := Ideal.span {f}) p'').choose
  Ideal.Quotient.mk (Ideal.span {(Polynomial.map (LocalRing.residue A) f)})
    (Polynomial.map (Ideal.Quotient.mk (LocalRing.maximalIdeal A)) p') -/

open Ideal.Quotient

noncomputable def bar (f : A[X]) (π : A) : AdjoinRoot (map (LocalRing.residue A) f) →
    AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} := fun q ↦
  let q'' := (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) q).choose
  let q'  := (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective q'').choose
  Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}) (Ideal.Quotient.mk (Ideal.span {f}) q')


lemma foo_one (f : A[X]) {π : A} (hπ : Irreducible π) : foo f π 1 = 1 := by
  set y := (mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) 1).choose
  set x := (mk_surjective (I := Ideal.span {f}) y).choose with hx
  have hy_spec := (mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) 1).choose_spec
  have hx_spec  := (mk_surjective (I := Ideal.span {f}) y).choose_spec
  have hydvd : (AdjoinRoot.of f) π ∣ y - 1 := by
    rw [← Ideal.mem_span_singleton, ← mk_eq_mk_iff_sub_mem, hy_spec, map_one]
  obtain ⟨c, hc⟩ := dvd_iff_exists_eq_mul_left.mp hydvd
  obtain ⟨d, hd⟩ := mk_surjective (I := Ideal.span {f}) c
  obtain ⟨e, he⟩ := mk_surjective (I := Ideal.span {f}) (AdjoinRoot.of f π)
  rw [← hx, sub_eq_iff_eq_add.mp hc, ← hd, ← he, ← map_mul (Ideal.Quotient.mk (Ideal.span {f})),
    ← sub_eq_iff_eq_add, ← map_one (Ideal.Quotient.mk (Ideal.span {f})),
    ← map_sub (Ideal.Quotient.mk (Ideal.span {f})), mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
    at hx_spec
  simp only [foo]
  rw [← hx, ← map_one (Ideal.Quotient.mk (Ideal.span {map (LocalRing.residue A) f})),
    mk_eq_mk_iff_sub_mem, ← Polynomial.map_one (Ideal.Quotient.mk ((LocalRing.maximalIdeal A))),
    ← Polynomial.map_sub, Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_left]
  -- f ∣ e - C π
  erw [← AdjoinRoot.mk_C, AdjoinRoot.mk, mk_eq_mk_iff_sub_mem (I := Ideal.span {f}) e (C π),
    Ideal.mem_span_singleton] at he
  obtain ⟨h, hh⟩ := dvd_iff_exists_eq_mul_left.mp he
  obtain ⟨g, hg⟩ := dvd_iff_exists_eq_mul_left.mp hx_spec
  rw [sub_eq_iff_eq_add] at hg
  have hC : map (Ideal.Quotient.mk (LocalRing.maximalIdeal A)) (C π) = 0 := by
    rw [map_C, C_eq_zero, Irreducible.maximalIdeal_eq hπ, mk_singleton_self]
  use map (LocalRing.residue A) (g + d*h)
  rw [hg, sub_eq_iff_eq_add.mp hh, mul_add, ← add_assoc, Polynomial.map_add, Polynomial.map_mul, hC,
    mul_zero, add_zero, ← Polynomial.map_mul, add_mul, mul_assoc]
  rfl

lemma bar_one (f : A[X]) {π : A} (hπ : Irreducible π) : bar f π 1 = 1 := by
  set y := (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) 1).choose with hy
  set hy_spec := (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) 1).choose_spec
  rw [← hy] at hy_spec
  set x := (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
    (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) 1).choose).choose with hx
  rw [← hy] at hx
  have hx_spec := (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
    (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) 1).choose).choose_spec

  rw [← hy, ← hx] at hx_spec
  have h1 : Ideal.Quotient.mk (Ideal.span {f}) 1 = 1 := by rw [map_one]

  /- have hsub : (Ideal.Quotient.mk (Ideal.span {f})) x1 - (Ideal.Quotient.mk (Ideal.span {f})) 1 =
    (Ideal.Quotient.mk (Ideal.span {f})) (x1 - (1 : A[X])) := by
      sorry -/

  have hdvd : (C π) ∣ x - (1 : A[X]) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]


    --rw [hx_spec]
    sorry

  simp only [bar]
  rw [← hx]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π})), mk_eq_mk_iff_sub_mem,
    ← h1]
  rw [← map_sub (Ideal.Quotient.mk (Ideal.span {f})), Ideal.mem_span_singleton]

  rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢

  obtain ⟨c, hc⟩ := hdvd

  use (Ideal.Quotient.mk (Ideal.span {f})) c
  simp only [hc, map_mul]
  rfl

variable (f : A[X]) {π : A} (hπ : Irreducible π) (p : A[X])

--#check Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}) ∘ (AdjoinRoot.mk f)
--#check (AdjoinRoot.mk (map (LocalRing.residue A) f)).toFun ∘ (Polynomial.map (LocalRing.residue A))

lemma comm_diag (f : A[X]) {π : A} (hπ : Irreducible π) :
    (foo f π) ∘ Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}) ∘ (AdjoinRoot.mk f) =
    (AdjoinRoot.mk (map (LocalRing.residue A) f)).toFun ∘ (Polynomial.map (LocalRing.residue A)) := by
  ext p
  simp only [Function.comp_apply, foo, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
  simp only [AdjoinRoot.mk]
  erw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Polynomial.map_sub, Ideal.mem_span_singleton]
  congr 1

  sorry


noncomputable def bar_equiv (f : A[X]) {π : A} (hπ : Irreducible π) :
    AdjoinRoot (map (LocalRing.residue A) f) ≃+*
      AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} where
  toFun     := bar f π
  invFun    := foo f π
  left_inv  := by
    intro x
    set b1 := (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) x).choose with hb1
    set b2  := (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective b1).choose with hb2

    have hb1_spec := (mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) x).choose_spec
    have hb2_spec  := (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective b1).choose_spec

    set y := ((Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))
      ((Ideal.Quotient.mk (Ideal.span {f})) b2))
    simp only [bar, ← hb2]
    rw [ ← hb1_spec, ← hb1, ← hb2_spec, ← hb2]

    set f1 := (Ideal.Quotient.mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) y).choose with hf1

    have hf1_spec := (Ideal.Quotient.mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) y).choose_spec

    set f2 := (Ideal.Quotient.mk_surjective (I := Ideal.span {f}) f1).choose with hf2

    have hf2_spec := (Ideal.Quotient.mk_surjective (I := Ideal.span {f}) f1).choose_spec
    simp only [foo, ← hf2]



    have hdvd : f ∣  f2 - b2  := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, hf2_spec]
      sorry

    rw [dvd_iff_exists_eq_mul_left] at hdvd

    have :  ∃ (c : A[X]) (d : A[X]) (hd : map (LocalRing.residue A) d = 0),
        f2 - b2 = c * f + d := by

      sorry

    obtain ⟨c, d, hd, hcd⟩ := this

    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Polynomial.map_sub, Ideal.mem_span_singleton]

    rw [dvd_iff_exists_eq_mul_left]

    use map (LocalRing.residue A) c

    rw [hcd, Polynomial.map_add, Polynomial.map_mul]
    erw [hd, add_zero]
    rfl

/-     obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {map (LocalRing.residue A) f}) x
    rw [← hz, Ideal.Quotient.mk_eq_mk_iff_sub_mem]

    obtain ⟨w, hw⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective z
    rw [← hw, ← Polynomial.map_sub, Ideal.mem_span_singleton]

    have hdvd : f∣  f2 - w  := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, hf2_spec]


      sorry

    rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢

    obtain ⟨c, hc⟩ := hdvd

    use map (LocalRing.residue A) c

    simp only [hc, Polynomial.map_mul]
    rfl -/

    --rw [← RingHom.comp_apply]
  right_inv := sorry
  map_mul'  := sorry
  map_add'  := sorry

#exit


noncomputable def bar_equiv' (f : A[X]) {π : A} (hπ : Irreducible π) :
    AdjoinRoot (map (LocalRing.residue A) f) ≃+*
      AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} where
  toFun     := bar f π
  invFun    := foo f π
  left_inv  := by
    intro x
    obtain ⟨b1, hb1⟩ := mk_surjective (I := Ideal.span {(map (LocalRing.residue A) f)}) x
    obtain ⟨b2, hb2⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective b1
    set y := ((Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))
      ((Ideal.Quotient.mk (Ideal.span {f})) b2))
    simp only [bar]
    rw [← hb1, ← hb2]

    obtain ⟨f1, hf1⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(AdjoinRoot.of f) π}) y
    obtain ⟨f2, hf2⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) f1

    --simp only [foo, ← hf2]

    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {map (LocalRing.residue A) f}) x
    rw [← hz, Ideal.Quotient.mk_eq_mk_iff_sub_mem]

    obtain ⟨w, hw⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective z
    rw [← hw, ← Polynomial.map_sub, Ideal.mem_span_singleton]

    have hdvd : f∣  f2 - w  := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, hf2_spec]


      sorry

    rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢

    obtain ⟨c, hc⟩ := hdvd

    use map (LocalRing.residue A) c

    simp only [hc, Polynomial.map_mul]
    rfl

    --rw [← RingHom.comp_apply]


    sorry
  right_inv := sorry
  map_mul'  := sorry
  map_add'  := sorry

noncomputable def ResidueField_equiv_AdjoinRoot_quotAdjoinRoot (f : A[X]) {π : A}
    (hπ : Irreducible π) :
    k  ≃+* AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} :=
  { ResidueField_to_AdjoinRoot_quot f hπ with
    invFun    := sorry
    left_inv  := sorry
    right_inv := sorry}

end Foo

#exit

set_option maxHeartbeats 400000
lemma isMaximal_of_irreducible {f : A[X]}
    (hf : Irreducible (map (LocalRing.residue A) f)) {π : A} (hπ : Irreducible π) :
    (Ideal.span {AdjoinRoot.of f π}).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  set foo : k →+* AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} := {
    toFun    := fun x ↦ RingHom.comp (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))
      (AdjoinRoot.of f) (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose
    map_one' := by
      set x1 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 1).choose
      have h1 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 1).choose_spec
      simp only [RingHom.coe_comp, Function.comp_apply,
        ← map_one (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_one (AdjoinRoot.of f), ← map_sub,
        Ideal.mem_span_singleton]
      have hdvd : π ∣ (x1 - 1) := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          ← Irreducible.maximalIdeal_eq hπ, h1, map_one]
      rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
      obtain ⟨c, hc⟩ := hdvd
      use (AdjoinRoot.of f) c
      rw [← map_mul, ← hc]
    map_mul' := fun x y ↦ by
      sorry/- set x' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose
      set y' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose
      set xy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x*y)).choose
      set hx' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose_spec
      set hy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose_spec
      set hxy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x*y)).choose_spec
      simp only [RingHom.coe_comp, Function.comp_apply, ← map_mul,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, Ideal.mem_span_singleton]
      have hdvd : π ∣ (xy' - x'*y') := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          ← Irreducible.maximalIdeal_eq hπ, map_mul, hx', hy', hxy']
      rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
      obtain ⟨c, hc⟩ := hdvd
      use (AdjoinRoot.of f) c
      rw [← map_mul, ← hc] -/
    map_zero' := by
      set x0 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 0).choose
      have h0 := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) 0).choose_spec
      simp only [RingHom.coe_comp, Function.comp_apply,
        ← map_zero (Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_zero (AdjoinRoot.of f), ← map_sub,
        Ideal.mem_span_singleton]
      have hdvd : π ∣ (x0 - 0) := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          ← Irreducible.maximalIdeal_eq hπ, h0, map_zero]
      rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
      obtain ⟨c, hc⟩ := hdvd
      use (AdjoinRoot.of f) c
      rw [← map_mul, ← hc]
    map_add' := fun x y ↦ by
      set x' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose
      set y' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose
      set xy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x + y)).choose
      set hx' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) x).choose_spec
      set hy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) y).choose_spec
      set hxy' := (Ideal.Quotient.mk_surjective (I := LocalRing.maximalIdeal A) (x + y)).choose_spec
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← map_add, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, Ideal.mem_span_singleton]
      have hdvd : π ∣ (xy' - x'*y') := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          ← Irreducible.maximalIdeal_eq hπ, map_mul, hx', hy', hxy']
      rw [dvd_iff_exists_eq_mul_left] at hdvd ⊢
      obtain ⟨c, hc⟩ := hdvd
      use (AdjoinRoot.of f) c
      rw [← map_mul, ← hc]
  }
  -- TODO: extract as def
  set e : AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} ≃* k :=
  { toFun     := fun x ↦ by

      sorry
    invFun    := fun x ↦ by

      sorry
    left_inv  := sorry
    right_inv := sorry
    map_mul'  := sorry
  }
  exact MulEquiv.isField _ (Field.toIsField _) e

  /- rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    rw [Ideal.mem_span_singleton] at h
    sorry
  · intros J x hJ hxπ hxJ
    sorry -/

lemma localRing_of_irreducible {f : A[X]}
    (hf : Irreducible (map (LocalRing.residue A) f)) :
    LocalRing (AdjoinRoot f) := by
  apply LocalRing.of_unique_max_ideal
  obtain ⟨π, hπ⟩ := exists_irreducible A
  use Ideal.span {AdjoinRoot.of f π}
  refine ⟨isMaximal_of_irreducible hf hπ, ?_⟩
  intro I hI
  apply Ideal.IsMaximal.eq_of_le hI (isMaximal_of_irreducible hf hπ).ne_top
  sorry

lemma maximalIdeal_of_irreducible {f : A[X]}
    (hf : Irreducible (map (LocalRing.residue A) f))
    {π : A} (hπ : Irreducible π) :
    @LocalRing.maximalIdeal (AdjoinRoot f) _ (localRing_of_irreducible hf) =
      Ideal.span {AdjoinRoot.of f π} :=
  letI : LocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  (LocalRing.eq_maximalIdeal (isMaximal_of_irreducible hf hπ)).symm

lemma not_isField_of_irreducible {f : A[X]}
    (hf : Irreducible (map (LocalRing.residue A) f)) :
    ¬ IsField (AdjoinRoot f) := by
  letI : LocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  obtain ⟨π, hπ⟩ := exists_irreducible A
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero (degree_ne_zero_of_irreducible hf)
  rw [LocalRing.isField_iff_maximalIdeal_eq, maximalIdeal_of_irreducible hf hπ,
    Ideal.span_singleton_eq_bot]
  intro hf0
  rw [← map_zero (AdjoinRoot.of f)] at hf0
  exact hπ.ne_zero (hinj hf0)

-- Ch. I, Section 6, Prop. 15 of Serre's "Local Fields"
lemma discreteValuationRing_of_irreducible {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (LocalRing.residue A) f)) :
    @DiscreteValuationRing (AdjoinRoot f) _ (isDomain_of_irreducible hf1 hf) := by
  have not_field : ¬ IsField (AdjoinRoot f) := not_isField_of_irreducible hf
  letI : IsDomain (AdjoinRoot f) := isDomain_of_irreducible hf1 hf
  letI : LocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  have h := ((DiscreteValuationRing.TFAE (AdjoinRoot f) not_field).out 0 4)
  obtain ⟨π, hπ⟩ := exists_irreducible A
  rw [h]
  exact ⟨algebraMap A (AdjoinRoot f) π, maximalIdeal_of_irreducible hf hπ⟩

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_integral_closure_of_irreducible {f : A[X]}
    (hf : Irreducible (map (LocalRing.residue A) f)) :
    IsIntegralClosure (AdjoinRoot f) A (FractionRing (AdjoinRoot f)) :=
  sorry

end AdjoinRoot

local notation "K" => (FractionRing A)

variable (L : Type*) [Field L] [Algebra (FractionRing A) L]
  [FiniteDimensional (FractionRing A) L] [Algebra A L] [IsScalarTower A (FractionRing A) L]

open FiniteDimensional

local notation "B" => integralClosure A L

-- Serre's Proposition 16 in Chapter I, Section 6: we may want the algebra instance to become an
-- explicit variable so that when we use the definition we do not need `@`.
noncomputable def integralClosure_equiv_algebra_adjoin
    (hB : DiscreteValuationRing B)
    [h_alg : Algebra k (LocalRing.ResidueField B)]
    (hpb : PowerBasis k (LocalRing.ResidueField B))
    (hdeg : finrank (FractionRing A) L = hpb.dim) (x : B)
    (hx : Ideal.Quotient.mk (LocalRing.maximalIdeal B) x = hpb.gen) :
    B ≃+* Algebra.adjoin A ({x} : Set B) :=
  sorry

noncomputable def integralClosure_equiv_adjoinRoot
    (hB : DiscreteValuationRing B)
    [Algebra k (LocalRing.ResidueField B)]
    (hpb : PowerBasis k (LocalRing.ResidueField B))
    (hdeg : finrank (FractionRing A) L = hpb.dim) (x : B)
    (hx : Ideal.Quotient.mk (LocalRing.maximalIdeal B) x = hpb.gen) :
    (integralClosure A L) ≃+* AdjoinRoot (minpoly A x) :=
  sorry

end DiscreteValuationRing
