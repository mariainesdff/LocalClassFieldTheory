/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import Mathlib.NumberTheory.RamificationInertia

namespace DiscreteValuationRing

open Valuation

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]
-- We need to indicate in the doctring that h_alg is not an instance so when we apply it
-- with local fields...
variable {B : Type*} [CommRing B] [IsDomain B] [DiscreteValuationRing B] [Algebra A B] /-  (h_alg : Algebra A B) -/

scoped notation "e("B","A")" => Ideal.ramificationIdx (algebraMap A B)
  (LocalRing.maximalIdeal A) (LocalRing.maximalIdeal B)

--NOTE: Missing in Lean 4 (?)
instance : Coe A (FractionRing A) := ⟨fun a => Localization.mk a 1⟩

lemma uniformizer_iff_unramified {a : A} (ha : IsUniformizer Valued.v (a : FractionRing A)) :
  IsUniformizer Valued.v (↑(algebraMap A B a) : FractionRing B) ↔ e(B,A) = 1 :=
sorry

end DiscreteValuationRing
