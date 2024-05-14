/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import Mathlib.RingTheory.Polynomial.IrreducibleRing

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]

namespace DiscreteValuationRing

namespace AdjoinRoot

lemma degree_ne_zero_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (algebraMap A (LocalRing.ResidueField A)) f))  :
    f.degree ≠ 0 := by
  intro h0
  have hC := Polynomial.eq_C_of_degree_eq_zero h0
  rw [hC, Polynomial.map_C] at hf
  exact (Polynomial.not_irreducible_C _) hf

lemma irreducible_of_irreducible_quot {f : Polynomial A} (hf1 : f.Monic)
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f)) :
    Irreducible f :=
  letI : (nilradical A).IsPrime := by
    simp only [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.isPrime_iff_bot_or_prime, true_or]
  Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical (LocalRing.residue A)
    f hf1 hf

lemma isDomain_of_irreducible {f : Polynomial A} (hf1 : f.Monic)
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f)) :
    IsDomain (AdjoinRoot f) := by
  simp only [AdjoinRoot, Ideal.Quotient.isDomain_iff_prime]
  rw [Ideal.span_singleton_prime]
  · exact irreducible_iff_prime.mp (irreducible_of_irreducible_quot hf1 hf)
  · intro hf0
    simp only [hf0, Polynomial.map_zero, not_irreducible_zero] at hf

lemma isMaximal_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f))
    {π : A} (hπ : Irreducible π) :
    (Ideal.span {AdjoinRoot.of f π}).IsMaximal :=
  sorry

lemma localRing_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f)) :
    LocalRing (AdjoinRoot f) := by
  apply LocalRing.of_unique_max_ideal
  obtain ⟨π, hπ⟩ := exists_irreducible A
  use Ideal.span {AdjoinRoot.of f π}
  refine ⟨isMaximal_of_irreducible hf hπ, ?_⟩
  intro I hI
  apply Ideal.IsMaximal.eq_of_le hI (isMaximal_of_irreducible hf hπ).ne_top
  sorry

lemma maximalIdeal_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f))
    {π : A} (hπ : Irreducible π) :
    @LocalRing.maximalIdeal (AdjoinRoot f) _ (localRing_of_irreducible hf) =
      Ideal.span {AdjoinRoot.of f π} :=
  letI : LocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  (LocalRing.eq_maximalIdeal (isMaximal_of_irreducible hf hπ)).symm

lemma not_isField_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f)) :
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
lemma discreteValuationRing_of_irreducible {f : Polynomial A} (hf1 : f.Monic)
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f)) :
    @DiscreteValuationRing (AdjoinRoot f) _ (isDomain_of_irreducible hf1 hf) := by
  have not_field : ¬ IsField (AdjoinRoot f) := not_isField_of_irreducible hf
  letI : IsDomain (AdjoinRoot f) := isDomain_of_irreducible hf1 hf
  letI : LocalRing (AdjoinRoot f) := localRing_of_irreducible hf
  have h := ((DiscreteValuationRing.TFAE (AdjoinRoot f) not_field).out 0 4)
  obtain ⟨π, hπ⟩ := exists_irreducible A
  rw [h]
  exact ⟨algebraMap A (AdjoinRoot f) π, maximalIdeal_of_irreducible hf hπ⟩

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_integral_closure_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (LocalRing.residue A) f)) :
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
    [h_alg : Algebra (LocalRing.ResidueField A) (LocalRing.ResidueField B)]
    (hpb : PowerBasis (LocalRing.ResidueField A) (LocalRing.ResidueField B))
    (hdeg : finrank (FractionRing A) L = hpb.dim) (x : B)
    (hx : Ideal.Quotient.mk (LocalRing.maximalIdeal B) x = hpb.gen) :
    B ≃+* Algebra.adjoin A ({x} : Set B) :=
  sorry

noncomputable def integralClosure_equiv_adjoinRoot
    (hB : DiscreteValuationRing B)
    [Algebra (LocalRing.ResidueField A) (LocalRing.ResidueField B)]
    (hpb : PowerBasis (LocalRing.ResidueField A) (LocalRing.ResidueField B))
    (hdeg : finrank (FractionRing A) L = hpb.dim) (x : B)
    (hx : Ideal.Quotient.mk (LocalRing.maximalIdeal B) x = hpb.gen) :
    (integralClosure A L) ≃+* AdjoinRoot (minpoly A x) :=
  sorry

end DiscreteValuationRing
