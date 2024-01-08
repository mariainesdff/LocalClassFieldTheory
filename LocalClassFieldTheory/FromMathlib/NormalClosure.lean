/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

#align_import from_mathlib.normal_closure

/-!
# Normal closures

## Main Results

- `normal_closure.is_algebraic` : If `L/K` is an algebraic field extension, then the normal closure
  of `L/K` in the algebraic closure of `L` is an algebraic extension of `K`.

## Tags

normal, normal_closure, algebraic, is_algebraic
-/


variable (K L : Type _) [Field K] [Field L] [Algebra K L]

namespace normalClosure

-- Porting note: I am using AlgebraicClosure instead of AlgebraicClosureAux

/-- If `L/K` is an algebraic field extension, then the normal closure of `L/K` in the algebraic
closure of `L` is an algebraic extension of `K`. -/
theorem isAlgebraic (h : Algebra.IsAlgebraic K L) :
    Algebra.IsAlgebraic K (normalClosure K L (AlgebraicClosure L)) :=
  Algebra.IsAlgebraic.trans h fun _ =>
    IntermediateField.isAlgebraic_iff.mpr (AlgebraicClosure.isAlgebraic L _)

end normalClosure
