/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Algebraic

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
instance isAlgebraic [Algebra.IsAlgebraic K L] :
    Algebra.IsAlgebraic K (normalClosure K L (AlgebraicClosure L)) :=
  @Algebra.IsAlgebraic.trans K L (normalClosure K L (AlgebraicClosure L)) _ _ _ _ _ _ _ _
    (Algebra.isAlgebraic_def.mpr (fun _ =>
     IntermediateField.isAlgebraic_iff.mpr ((AlgebraicClosure.isAlgebraic L).isAlgebraic _)))


end normalClosure
