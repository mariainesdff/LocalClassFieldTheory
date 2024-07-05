import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Polynomial.IrreducibleRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.Algebra.Polynomial.Induction

open Ideal.Quotient Polynomial

universe u v

variable {A : Type u} [CommRing A] [IsDomain A] (I : Ideal A[X]) (J : Ideal A)

-- I don't think this is really needed
noncomputable def DoubleQuot.quotSpanQuotSpanEquivComm (f : A[X]) (ϖ : A) :
  (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ⧸
    ((Ideal.span {f}).map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))) ≃+*
    (A [X]⧸ Ideal.span {f}) ⧸
      ((Ideal.span {Polynomial.C ϖ}).map (Ideal.Quotient.mk (Ideal.span {f}))) :=
  DoubleQuot.quotQuotEquivComm (Ideal.span {Polynomial.C ϖ}) (Ideal.span {f})

open Polynomial

-- It could be good to add this to Mathlib, but here we only need the existing
-- Ideal.polynomialQuotientEquivQuotientPolynomial
noncomputable def _root_.Ideal.polynomialQuotientAlgEquivQuotientPolynomial {R : Type*} [CommRing R]
    (I : Ideal R) : Polynomial (R ⧸ I) ≃ₐ[R] Polynomial R ⧸ Ideal.map Polynomial.C I :=
  { Ideal.polynomialQuotientEquivQuotientPolynomial I with
    commutes' := fun r ↦ by
      simp only [Ideal.polynomialQuotientEquivQuotientPolynomial, coe_eval₂RingHom,
        RingEquiv.toEquiv_eq_coe, algebraMap_apply, Ideal.Quotient.algebraMap_eq,
        Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk, eval₂_C, lift_mk,
        RingHom.coe_comp, Function.comp_apply]
      rfl }

noncomputable def _root_.Ideal.polynomialQuotientIrreducibleAlgEquivResidueFieldPolynomial
    [DiscreteValuationRing A] {ϖ : A} (h : Irreducible ϖ) :
    (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ≃+* (LocalRing.ResidueField A)[X] :=
  let φ := ((LocalRing.maximalIdeal A).polynomialQuotientEquivQuotientPolynomial).symm
  let β := Ideal.quotientEquiv (Ideal.map Polynomial.C (LocalRing.maximalIdeal A))
   ((Ideal.map Polynomial.C (LocalRing.maximalIdeal A))) (RingEquiv.refl A[X])
   (by rw [Ideal.map_map]; rfl)
  Set.image_singleton ▸ Ideal.map_span C {ϖ} ▸ (Irreducible.maximalIdeal_eq h ▸  (β.symm).trans φ)

set_option profiler true

noncomputable def DoubleQuot.quotSpanQuotEquivResidueFieldPolynomialQuot [DiscreteValuationRing A]
    {ϖ : A} (h : Irreducible ϖ) (I : Ideal A[X]) :
    (A[X] ⧸ Ideal.span {Polynomial.C ϖ}) ⧸
      (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))) ≃+*
    (LocalRing.ResidueField A)[X] ⧸
      (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))).map
      (Ideal.polynomialQuotientIrreducibleAlgEquivResidueFieldPolynomial h) :=
  Ideal.quotientEquiv _ _ (Ideal.polynomialQuotientIrreducibleAlgEquivResidueFieldPolynomial h) rfl

noncomputable def DoubleQuot.quotQuotSpanEquivResidueFieldPolynomialQuot [DiscreteValuationRing A]
    {ϖ : A} (h : Irreducible ϖ) (I : Ideal A[X]) :
    (A[X] ⧸ I) ⧸ ((Ideal.span {Polynomial.C ϖ}).map (Ideal.Quotient.mk I)) ≃+*
    (LocalRing.ResidueField A)[X] ⧸
      (I.map (Ideal.Quotient.mk (Ideal.span {Polynomial.C ϖ}))).map
      (Ideal.polynomialQuotientIrreducibleAlgEquivResidueFieldPolynomial h) :=
  RingEquiv.trans (DoubleQuot.quotQuotEquivComm I (Ideal.span {Polynomial.C ϖ}))
    (DoubleQuot.quotSpanQuotEquivResidueFieldPolynomialQuot h I)
