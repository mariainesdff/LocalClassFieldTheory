import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Polynomial.IrreducibleRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.Algebra.Polynomial.Induction

open Ideal.Quotient Polynomial

universe u v

variable {A : Type u} [CommRing A] [IsDomain A] (I : Ideal A[X]) (J : Ideal A)

noncomputable def fae_mem (I : Ideal A[X]) (f : A[X]) :
    (A[X] ⧸ I) ⧸ ((Ideal.span {f}).map (Ideal.Quotient.mk I)) ≃+*
    (A[X] ⧸ Ideal.span {f}) ⧸ (I.map (Ideal.Quotient.mk (Ideal.span {f}))) :=
  DoubleQuot.quotQuotEquivComm (R := A[X]) I (Ideal.span {f})
  /-
  · simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul, implies_true]
  · simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, map_add, implies_true] -/

noncomputable def fae_ideal (I J : Ideal A[X]) :
    (A[X] ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I)) ≃+* (A[X] ⧸ J) ⧸ (I.map (Ideal.Quotient.mk J)) :=
  @DoubleQuot.quotQuotEquivComm A[X] _ I J
  /- · simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul, implies_true]
  · simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, map_add, implies_true] -/

noncomputable def fae'_mem (f : A[X]) (ϖ : A) :
  (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ⧸
    ((Ideal.span {f}).map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))) ≃+*
    (A [X]⧸ Ideal.span {f}) ⧸
      ((Ideal.span {Polynomial.C ϖ}).map (Ideal.Quotient.mk (Ideal.span {f}))) :=
  fae_mem (Ideal.span {Polynomial.C ϖ}) f

noncomputable def fae'_ideal (I : Ideal A[X]) (ϖ : A) :
  (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ⧸
    (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))) ≃+*
    (A [X]⧸ I) ⧸
      ((Ideal.span {Polynomial.C ϖ}).map (Ideal.Quotient.mk I)) :=
  fae_ideal (Ideal.span {Polynomial.C ϖ}) I

noncomputable def fae'_ideal' (I : Ideal A[X]) (J : Ideal A) :
  (A[X] ⧸ Ideal.map Polynomial.C J) ⧸
    (I.map (Ideal.Quotient.mk (Ideal.map Polynomial.C J))) ≃+*
    (A [X]⧸ I) ⧸ ((Ideal.map Polynomial.C J).map (Ideal.Quotient.mk I)) :=
  fae_ideal (Ideal.map Polynomial.C J) I

open Polynomial

lemma quotientEquivQuotientMvPolynomial_rightInverse {R : Type*} [CommRing R] (I : Ideal R) :
    Function.RightInverse ((Polynomial.eval₂AlgHom'
      (Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R (Ideal.map C I : Ideal R[X])).comp CAlgHom)
      (fun _ ha ↦ Ideal.quotient_map_C_eq_zero _ ha))
      (Ideal.Quotient.mk (Ideal.map C I : Ideal R[X]) X)
      (fun a ↦ by rw [liftₐ_apply, commute_iff_eq, mul_comm])).toRingHom).toFun
    (Ideal.Quotient.liftₐ (Ideal.map C I : Ideal R[X])
        (eval₂AlgHom' (CAlgHom.comp (Ideal.Quotient.mkₐ R I)) X (fun a ↦ by simp  [commute_iff_eq]))
        (fun _ ha ↦ Ideal.eval₂_C_mk_eq_zero _ ha)) := by
  intro f
  induction f using Polynomial.induction_on with
  | h_C r =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, eval₂AlgHom'_apply, eval₂_C,
        liftₐ_apply, lift_mk, AlgHom.coe_comp, mkₐ_eq_mk, Function.comp_apply, CAlgHom_apply]
  | h_add p q hp hq =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, eval₂AlgHom'_apply, liftₐ_apply,
        map_add] at hp hq ⊢
      rw [hp, hq]
  | h_monomial p i hp =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, map_mul, MonoidHom.coe_coe, RingHom.coe_coe, eval₂AlgHom'_apply,
        eval₂_C, liftₐ_apply, map_pow, eval₂_X, lift_mk] at hp ⊢
      rw [pow_succ, ← mul_assoc, hp, mul_assoc]

lemma quotientEquivQuotientMvPolynomial_leftInverse {R : Type*} [CommRing R] (I : Ideal R) :
    Function.LeftInverse ((Polynomial.eval₂AlgHom'
      (Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R (Ideal.map C I : Ideal R[X])).comp CAlgHom)
      (fun _ ha ↦ Ideal.quotient_map_C_eq_zero _ ha))
      (Ideal.Quotient.mk (Ideal.map C I : Ideal R[X]) X)
      (fun a ↦ by rw [liftₐ_apply, commute_iff_eq, mul_comm])).toRingHom).toFun
    (Ideal.Quotient.liftₐ (Ideal.map C I : Ideal R[X])
        (eval₂AlgHom' (CAlgHom.comp (Ideal.Quotient.mkₐ R I)) X (fun a ↦ by simp  [commute_iff_eq]))
        (fun _ ha ↦ Ideal.eval₂_C_mk_eq_zero _ ha))  := by
  intro f
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  induction f using Polynomial.induction_on with
  | h_C r =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, liftₐ_apply, lift_mk,
      RingHom.coe_coe, eval₂AlgHom'_apply, eval₂_C, AlgHom.coe_comp, mkₐ_eq_mk, Function.comp_apply,
      CAlgHom_apply, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
  | h_add p q hp hq =>
    erw [Ideal.Quotient.lift_mk] at hp hq ⊢
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_coe,
      eval₂AlgHom'_apply, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
      map_add] at hp hq ⊢
    rw [hp, hq]
  | h_monomial p i hp =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, map_mul, map_pow, liftₐ_apply,
      lift_mk, RingHom.coe_coe, eval₂AlgHom'_apply, eval₂_C, AlgHom.coe_comp, mkₐ_eq_mk,
      Function.comp_apply, CAlgHom_apply, eval₂_X, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe] at hp ⊢

noncomputable def _root_.Polynomial.quotientEquivQuotientPolynomial {R : Type*} [CommRing R]
    (I : Ideal R) : (R ⧸ I)[X] ≃ₐ[R] R[X] ⧸ Ideal.map Polynomial.C I := by
  let e : (R ⧸ I)[X] →ₐ[R] R[X] ⧸ (Ideal.map C I : Ideal R[X]) :=
    Polynomial.eval₂AlgHom'
      (Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R (Ideal.map C I : Ideal R[X])).comp CAlgHom)
      (fun _ ha ↦ Ideal.quotient_map_C_eq_zero _ ha))
      (Ideal.Quotient.mk (Ideal.map C I : Ideal R[X]) X)
      (fun a ↦ by rw [liftₐ_apply, commute_iff_eq, mul_comm])
  exact { e with
    invFun   := Ideal.Quotient.liftₐ (Ideal.map C I : Ideal R[X])
        (eval₂AlgHom' (CAlgHom.comp (Ideal.Quotient.mkₐ R I)) X (fun a ↦ by simp  [commute_iff_eq]))
        (fun _ ha ↦ Ideal.eval₂_C_mk_eq_zero _ ha)
    left_inv  := quotientEquivQuotientMvPolynomial_rightInverse I
    right_inv := quotientEquivQuotientMvPolynomial_leftInverse I }

noncomputable def fae_ResidueField [DiscreteValuationRing A] {ϖ : A} (h : Irreducible ϖ) :
    (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ≃+* (LocalRing.ResidueField A)[X] := by
  let α := (MvPolynomial.pUnitAlgEquiv A).toRingEquiv
  let φ := (@MvPolynomial.quotientEquivQuotientMvPolynomial A Unit _
    (LocalRing.maximalIdeal A)).toRingEquiv.symm
  let β := Ideal.quotientEquiv (Ideal.map MvPolynomial.C (LocalRing.maximalIdeal A))
   ((Ideal.map Polynomial.C (LocalRing.maximalIdeal A))) α ?_
  let ψ := (β.symm).trans φ
  let γ := (MvPolynomial.pUnitAlgEquiv (LocalRing.ResidueField A)).toRingEquiv
  let ξ := ψ.trans γ
  convert ξ <;>
  · rw [Irreducible.maximalIdeal_eq h, Ideal.map_span]
    simp only [Set.image_singleton]
  · rw [Ideal.map_map]
    congr
    dsimp [α]
    ext g n
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      MvPolynomial.pUnitAlgEquiv_apply, MvPolynomial.eval₂_C]

noncomputable def fae_ResidueField' [DiscreteValuationRing A] {ϖ : A} (h : Irreducible ϖ) :
    (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ≃+* (LocalRing.ResidueField A)[X] := by
  let φ := (Polynomial.quotientEquivQuotientPolynomial (LocalRing.maximalIdeal A)).toRingEquiv.symm
  let β := Ideal.quotientEquiv (Ideal.map Polynomial.C (LocalRing.maximalIdeal A))
   ((Ideal.map Polynomial.C (LocalRing.maximalIdeal A))) (RingEquiv.refl A[X])
   (by rw [Ideal.map_map]; rfl)
  convert (β.symm).trans φ <;>
  · rw [Irreducible.maximalIdeal_eq h, Ideal.map_span]
    simp only [Set.image_singleton]

set_option profiler true

noncomputable def MariaInes [DiscreteValuationRing A] (ϖ : A) (h : Irreducible ϖ) (I : Ideal A[X]) :
    (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ⧸
      (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))) ≃+*
    (LocalRing.ResidueField A)[X] ⧸
      (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))).map (fae_ResidueField' h) := by
  apply Ideal.quotientEquiv _ _ (fae_ResidueField' h)
  norm_cast

#exit

noncomputable def MariaInes' [DiscreteValuationRing A] (ϖ : A) (h : Irreducible ϖ) (I : Ideal A[X]) :
    (A[X] ⧸ I) ⧸
      ((Ideal.span {Polynomial.C ϖ}).map (Ideal.Quotient.mk I)) ≃+*
    (LocalRing.ResidueField A)[X] ⧸
      (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))).map (fae_ResidueField h) :=
  RingEquiv.trans (DoubleQuot.quotQuotEquivComm I (Ideal.span {Polynomial.C ϖ})) (MariaInes ϖ h I)
