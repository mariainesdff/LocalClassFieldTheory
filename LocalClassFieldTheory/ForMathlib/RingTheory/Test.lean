import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Polynomial.IrreducibleRing

import Mathlib.RingTheory.Ideal.Maps

open Ideal.Quotient Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A[X]) (J : Ideal A)

instance : FunLike (A → A[X] ⧸ I) A (A[X] ⧸ I) := sorry
instance : FunLike (A[X] → (A ⧸ J)[X]) A[X] (A ⧸ J)[X]  := sorry

example (I : Ideal A[X]) (J : Ideal A) : Ideal (A[X] ⧸ I) :=
  J.map (Ideal.Quotient.mk I ∘ Polynomial.C)

example (I : Ideal A[X]) (J : Ideal A) : Ideal (A ⧸ J)[X] :=
  I.map (Polynomial.map (Ideal.Quotient.mk J))

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

noncomputable def Polynomial.mapIntAlgHom  {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) : R[X] →ₐ[ℤ] S[X] where
  toFun := Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero'    := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one'     := Polynomial.map_one f
  commutes' a  := by simp only [algebraMap_int_eq, eq_intCast, Polynomial.map_intCast]

lemma Polynomial.mapIntAlgHom_eq {R S : Type*} [Ring R] [Ring S]  (f : R →+* S) :
    Polynomial.mapIntAlgHom f = Polynomial.map f := rfl

lemma foo_aux1  (I : Ideal A[X]) (J : Ideal A) :
    ∀ a ∈ I, ((mkₐ ℤ (Ideal.map (map (mk J)) I)).comp (mapIntAlgHom (mk J))) a = 0 := by
  intro a ha
  simp only [AlgHom.coe_comp, mkₐ_eq_mk, Function.comp_apply]
  rw [← map_zero (Ideal.Quotient.mk (Ideal.map (map (mk J)) I))]
  rw [mk_eq_mk_iff_sub_mem, sub_zero, mapIntAlgHom_eq]
  convert Ideal.mem_map_of_mem (map (mk J)) ha -- Why doesn't this unify?
  sorry

lemma foo_aux2  (I : Ideal A[X]) (J : Ideal A) :
    ∀ a ∈ Ideal.map (⇑(mk I) ∘ ⇑C) J, (liftₐ I ((mkₐ ℤ (Ideal.map (map (mk J)) I)).comp
      (mapIntAlgHom (mk J))) (foo_aux1 I J)) a = 0 :=  by
  intro a ha
  simp only [liftₐ_apply]
  rw [← RingHom.mem_ker, Ideal.ker_quotient_lift]
  rw [Ideal.map] at ha ⊢
  have : ⇑(⇑(mk I) ∘ ⇑C) '' ↑J = ((mk I) ∘ C) '' ↑J := by
    ext
    simp only [Set.mem_image, SetLike.mem_coe, Function.comp_apply]
    constructor <;> rintro ⟨y, hyJ, hy⟩
    · use y, hyJ
      convert hy using 1

      sorry
    · sorry
  convert ha


  sorry
  /- constructor <;> intro hx
  · sorry
  · simp only [RingHom.coe_coe, AlgHom.coe_comp, mkₐ_eq_mk, Function.comp_apply]
    sorry -/

noncomputable def foo (I : Ideal A[X]) (J : Ideal A) :
    (A[X] ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I ∘ Polynomial.C)) →+*
      (A ⧸ J)[X] ⧸ I.map (Polynomial.map (Ideal.Quotient.mk J)) :=
  (Ideal.Quotient.liftₐ (J.map (Ideal.Quotient.mk I ∘ Polynomial.C))
    (Ideal.Quotient.liftₐ I
      ((Ideal.Quotient.mkₐ ℤ (I.map (Polynomial.map (Ideal.Quotient.mk J)))).comp
       (Polynomial.mapIntAlgHom (Ideal.Quotient.mk J))) (foo_aux1 I J))
        (by sorry)).toRingHom


  /- (Ideal.Quotient.liftₐ (Ideal.span {(AdjoinRoot.of f) π})
  (Ideal.Quotient.liftₐ (Ideal.span {f})
    ((Ideal.Quotient.mkₐ ℤ (Ideal.span {(Polynomial.map (LocalRing.residue A) f)})).comp
      (Polynomial.mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) (by sorry))
        (by sorry)).toRingHom -/

#exit


lemma foo_aux1 (f : A[X]) : ∀ a ∈ Ideal.span {f},
    ((Ideal.Quotient.mkₐ ℤ (Ideal.span {map (LocalRing.residue A) f})).comp
      (mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) a = 0 := by
  sorry/- intro a ha
  rw [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_left] at ha
  obtain ⟨c, hac⟩ := ha
  rw [hac, map_mul]
  apply mul_eq_zero_of_right
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_zero (Ideal.Quotient.mk
    (Ideal.span {map (LocalRing.residue A) f})), mk_eq_mk_iff_sub_mem, sub_zero] -/
  --exact Ideal.mem_span_singleton_self _

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

noncomputable def foo' (f : A[X]) (π : A) : AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} →+*
    AdjoinRoot (map (LocalRing.residue A) f) :=
  (Ideal.Quotient.liftₐ (Ideal.span {(AdjoinRoot.of f) π}) (Ideal.Quotient.liftₐ (Ideal.span {f})
    ((Ideal.Quotient.mkₐ ℤ (Ideal.span {(Polynomial.map (LocalRing.residue A) f)})).comp
      (Polynomial.mapAlgHom (Ideal.Quotient.mk (LocalRing.maximalIdeal A))
        (fun _ ↦ by simp only [algebraMap_int_eq, eq_intCast, map_intCast]))) (foo_aux1 f))
        (foo_aux2 f π)).toRingHom
