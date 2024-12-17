/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import Mathlib.NumberTheory.RamificationInertia.Basic

namespace IsDiscreteValuationRing

open Valuation

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
-- We need to indicate in the docstring that h_alg is not an instance so when we apply it
-- with local fields...
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

scoped notation "e("B","A")" => Ideal.ramificationIdx (algebraMap A B)
  (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)

--NOTE: Missing in Lean 4 (?)
instance : Coe A (FractionRing A) := ⟨fun a => Localization.mk a 1⟩

lemma Extension_IsUniformizer_iff_unramified {a : A}
    (ha : IsUniformizer Valued.v (a : FractionRing A)) :
    IsUniformizer Valued.v (↑(algebraMap A B a) : FractionRing B) ↔ e(B,A) = 1 :=
sorry

end IsDiscreteValuationRing
