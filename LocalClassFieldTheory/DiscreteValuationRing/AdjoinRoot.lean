/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import LocalClassFieldTheory.ForMathlib.RingTheory.Test
import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.IrreducibleRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

open Polynomial
section Polynomial

noncomputable def Polynomial.mapAlgHom' {A R S : Type*} [CommRing A] [Semiring R] [Algebra A R]
    [Semiring S] [Algebra A S] (f : R →+* S)
    (hf : ∀ a, f ((algebraMap A R) a) = (algebraMap A S) a) : R[X] →ₐ[A] S[X] where
  toFun := Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero'    := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one'     := Polynomial.map_one f
  commutes' a  := by simp only [algebraMap_apply, map_C, hf]

-- *FAE* Unfortunately in PR 14814 someone else defined `Polynomial.mapAlgHom'` and
-- I had to add a `'` to the above name to avoid duplication. Probably we should align the
-- above definition with the one in mathlib
lemma Polynomial.mapAlgHom_eq {A R S : Type*} [CommRing A] [Semiring R] [Algebra A R]
    [Semiring S] [Algebra A S] (f : R →+* S)
    (hf : ∀ a, f ((algebraMap A R) a) = (algebraMap A S) a) :
    Polynomial.mapAlgHom' f hf = Polynomial.map f := rfl

end Polynomial
namespace IsDiscreteValuationRing

open IsLocalRing

local notation "k" => ResidueField A

namespace AdjoinRoot

lemma degree_ne_zero_of_irreducible {f : A[X]} (hf : Irreducible (map (algebraMap A k) f)) :
    f.degree ≠ 0 := by
  intro h0
  rw [eq_C_of_degree_eq_zero h0, map_C] at hf
  exact (Polynomial.not_irreducible_C _) hf

lemma irreducible_of_irreducible_quot {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (residue A) f)) : Irreducible f :=
  letI : (nilradical A).IsPrime := by
    simp only [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.isPrime_iff_bot_or_prime, true_or]
  Monic.irreducible_of_irreducible_map_of_isPrime_nilradical (residue A) f hf1 hf

lemma isDomain_of_irreducible {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (residue A) f)) :
    IsDomain (AdjoinRoot f) := by
  simp only [AdjoinRoot, Ideal.Quotient.isDomain_iff_prime]
  rw [Ideal.span_singleton_prime]
  · exact irreducible_iff_prime.mp (irreducible_of_irreducible_quot hf1 hf)
  · intro hf0
    simp only [hf0, Polynomial.map_zero, not_irreducible_zero] at hf

noncomputable def ResidueField_to_AdjoinRoot_quot (f : A[X]) {π : A} (hπ : Irreducible π) :
    k →ₐ[A] AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} := by
  let g : A →ₐ[A] AdjoinRoot f :=
  { algebraMap A (AdjoinRoot f) with
    commutes' := fun r => rfl }
  apply Ideal.Quotient.liftₐ (maximalIdeal A)
    ((Ideal.Quotient.mkₐ (R₁ := A) (Ideal.span {(AdjoinRoot.of f) π})).comp g)
  intro a ha
  rw [AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, ← map_zero
    ((Ideal.Quotient.mk (Ideal.span {(AdjoinRoot.of f) π}))),Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    sub_zero]
  rw [Irreducible.maximalIdeal_eq hπ, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [Ideal.mem_span_singleton', map_mul]
  exact ⟨g c, rfl⟩

variable {π : A} (hπ : Irreducible π) (f : A[X])

noncomputable def fooEquiv {π : A} (hπ : Irreducible π) (f : A[X]) :
    AdjoinRoot f ⧸ Ideal.span {(AdjoinRoot.of f) π} ≃+*
    AdjoinRoot (map (residue A) f) := by
  --simp only [AdjoinRoot, AdjoinRoot.of, RingHom.coe_comp, Function.comp_apply]
  --Set.image_singleton ▸ Ideal.map_span C

  let _ := DoubleQuot.quotQuotSpanEquivResidueFieldPolynomialQuot hπ (Ideal.span {f})
  set this := AdjoinRoot.quotEquivQuotMap f (Ideal.span {π})
  rw [ ← Set.image_singleton,
    ← Ideal.map_span (AdjoinRoot.of f)]
  apply RingEquiv.trans this.toRingEquiv
  simp only [AdjoinRoot]
  all_goals
  · sorry

open Ideal.Quotient

variable (f : A[X]) {π : A} (hπ : Irreducible π) (p : A[X])

lemma isMaximal_of_irreducible {f : A[X]}
    (hf : Irreducible (map (residue A) f)) {π : A} (hπ : Irreducible π) :
    (Ideal.span {AdjoinRoot.of f π}).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (AdjoinRoot (map (residue A) f))
    (@AdjoinRoot.instField _ _ _ (fact_iff.mpr hf)).toIsField (fooEquiv hπ f))

lemma localRing_of_irreducible {f : A[X]}
    (hf : Irreducible (map (residue A) f)) :
    IsLocalRing (AdjoinRoot f) := by
  apply of_unique_max_ideal
  obtain ⟨π, hπ⟩ := exists_irreducible A
  use Ideal.span {AdjoinRoot.of f π}
  refine ⟨isMaximal_of_irreducible hf hπ, ?_⟩
  intro I hI
  apply Ideal.IsMaximal.eq_of_le hI (isMaximal_of_irreducible hf hπ).ne_top
  sorry

lemma maximalIdeal_of_irreducible {f : A[X]}
    (hf : Irreducible (map (residue A) f))
    {π : A} (hπ : Irreducible π) :
    @maximalIdeal (AdjoinRoot f) _ (localRing_of_irreducible hf) =
      Ideal.span {AdjoinRoot.of f π} :=
  let _ : IsLocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  (eq_maximalIdeal (isMaximal_of_irreducible hf hπ)).symm

lemma not_isField_of_irreducible {f : A[X]}
    (hf : Irreducible (map (residue A) f)) :
    ¬ IsField (AdjoinRoot f) := by
  let _ : IsLocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  obtain ⟨π, hπ⟩ := exists_irreducible A
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero (degree_ne_zero_of_irreducible hf)
  rw [isField_iff_maximalIdeal_eq, maximalIdeal_of_irreducible hf hπ,
    Ideal.span_singleton_eq_bot]
  intro hf0
  rw [← map_zero (AdjoinRoot.of f)] at hf0
  exact hπ.ne_zero (hinj hf0)

-- Ch. I, Section 6, Prop. 15 of Serre's "Local Fields"
lemma IsDiscreteValuationRing_of_irreducible {f : A[X]} (hf1 : f.Monic)
    (hf : Irreducible (map (residue A) f)) :
    @IsDiscreteValuationRing (AdjoinRoot f) _ (isDomain_of_irreducible hf1 hf) := by
  have not_field : ¬ IsField (AdjoinRoot f) := not_isField_of_irreducible hf
  let _ : IsDomain (AdjoinRoot f) := isDomain_of_irreducible hf1 hf
  let _ : IsLocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  have h := ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) not_field).out 0 4)
  obtain ⟨π, hπ⟩ := exists_irreducible A
  rw [h]
  exact ⟨algebraMap A (AdjoinRoot f) π, maximalIdeal_of_irreducible hf hπ⟩

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_integral_closure_of_irreducible {f : A[X]}
    (hf : Irreducible (map (residue A) f)) :
    IsIntegralClosure (AdjoinRoot f) A (FractionRing (AdjoinRoot f)) :=
  sorry

end AdjoinRoot

local notation "K" => (FractionRing A)

variable (L : Type*) [Field L] [Algebra (FractionRing A) L]
  [FiniteDimensional (FractionRing A) L] [Algebra A L] [IsScalarTower A (FractionRing A) L]

open Module

local notation "B" => integralClosure A L

-- Serre's Proposition 16 in Chapter I, Section 6: we may want the algebra instance to become an
-- explicit variable so that when we use the definition we do not need `@`.
noncomputable def integralClosure_equiv_algebra_adjoin
    (hB : IsDiscreteValuationRing B)
    [h_alg : Algebra k (ResidueField B)]
    (hpb : PowerBasis k (ResidueField B))
    (hdeg : finrank (FractionRing A) L = hpb.dim) (x : B)
    (hx : Ideal.Quotient.mk (maximalIdeal B) x = hpb.gen) :
    B ≃+* Algebra.adjoin A ({x} : Set B) :=
  sorry

noncomputable def integralClosure_equiv_adjoinRoot
    (hB : IsDiscreteValuationRing B)
    [Algebra k (ResidueField B)]
    (hpb : PowerBasis k (ResidueField B))
    (hdeg : finrank (FractionRing A) L = hpb.dim) (x : B)
    (hx : Ideal.Quotient.mk (maximalIdeal B) x = hpb.gen) :
    (integralClosure A L) ≃+* AdjoinRoot (minpoly A x) :=
  sorry

end IsDiscreteValuationRing
