/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # Padic Integers
In this file we construct an isomorphism between the residue field of `ℤ_[p]` and the type `zmod p`
of integers modulo `p`.
-/


variable (p : outParam ℕ) [Fact p.Prime]

namespace PadicInt

/-- The equivalence between the residue field of the `p`-adic integers and `ℤ/pℤ` -/
noncomputable def residueField : LocalRing.ResidueField ℤ_[p] ≃+* ZMod p := by
  let α := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (@PadicInt.toZMod p _))
  rw [PadicInt.ker_toZMod] at α
  exact α

end PadicInt
