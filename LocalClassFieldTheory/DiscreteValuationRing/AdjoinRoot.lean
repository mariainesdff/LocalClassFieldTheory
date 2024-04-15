/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]

namespace DiscreteValuationRing

namespace AdjoinRoot

lemma isDomain_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (algebraMap A (LocalRing.ResidueField A)) f)) :
    IsDomain (AdjoinRoot f) :=
  sorry

-- Ch. I, Section 6, Prop. 15 of Serre's "Local Fields"
lemma discreteValuationRing_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (algebraMap A (LocalRing.ResidueField A)) f)) :
    @DiscreteValuationRing (AdjoinRoot f) _ (isDomain_of_irreducible hf) :=
  sorry

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_integral_closure_of_irreducible {f : Polynomial A}
    (hf : Irreducible (Polynomial.map (algebraMap A (LocalRing.ResidueField A)) f)) :
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
