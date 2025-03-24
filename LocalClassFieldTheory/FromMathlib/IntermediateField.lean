/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

-- In PR #23251

noncomputable section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)

-- DONE
-- Mathlib.FieldTheory.IntermediateField.Adjoin.Basic]
theorem AdjoinDouble.isAlgebraic {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    Algebra.IsAlgebraic K K⟮x, y⟯ := by
  apply IntermediateField.isAlgebraic_adjoin
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz
  · exact hz ▸ hx.isIntegral
  · exact hz ▸ hy.isIntegral

-- [Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure]
theorem AdjoinSimple.normal_algebraicClosure {x : L} (hx : IsAlgebraic K x) :
    Normal K (AlgebraicClosure K⟮x⟯) :=
  have h_alg' : Algebra.IsAlgebraic K (AlgebraicClosure ↥K⟮x⟯) := by
    letI : Algebra.IsAlgebraic K K⟮x⟯ := (isAlgebraic_adjoin_simple hx.isIntegral)
    exact Algebra.IsAlgebraic.trans K K⟮x⟯ (AlgebraicClosure ↥K⟮x⟯)
  normal_iff.mpr fun y ↦ ⟨(h_alg'.isAlgebraic _).isIntegral,
    IsAlgClosed.splits_codomain (minpoly K y)⟩

-- [Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure]
theorem AdjoinDouble.normal_algebraicClosure {x y : L} (hx : IsAlgebraic K x)
    (hy : IsAlgebraic K y) : Normal K (AlgebraicClosure K⟮x, y⟯) :=
  have h_alg' : Algebra.IsAlgebraic K (AlgebraicClosure ↥K⟮x, y⟯) := by
    letI := AdjoinDouble.isAlgebraic hx hy
    exact Algebra.IsAlgebraic.trans K K⟮x, y⟯ (AlgebraicClosure ↥K⟮x, y⟯)
  normal_iff.mpr fun y ↦ ⟨(h_alg'.isAlgebraic _).isIntegral,
    IsAlgClosed.splits_codomain (minpoly K y)⟩

--DONE
-- [Mathlib.FieldTheory.IntermediateField.Adjoin.Basic]
theorem AdjoinDouble.finiteDimensional {x y : L} (hx : IsIntegral K x) (hy : IsIntegral K y) :
    FiniteDimensional K K⟮x, y⟯ := by
  haveI hx_fd : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
  have hy' : IsIntegral K⟮x⟯ y := IsIntegral.tower_top hy
  haveI hy_fd : FiniteDimensional K⟮x⟯ K⟮x⟯⟮y⟯ := adjoin.finiteDimensional hy'
  rw [← adjoin_simple_adjoin_simple]
  apply FiniteDimensional.trans K K⟮x⟯ K⟮x⟯⟮y⟯

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (x y : E)

--DONE
theorem mem_adjoinDouble_left : x ∈ F⟮x, y⟯ := by
  rw [← adjoin_simple_adjoin_simple, adjoin_simple_comm]
  exact subset_adjoin F⟮y⟯ {x} (Set.mem_singleton x)

--DONE
theorem mem_adjoinDouble_right : y ∈ F⟮x, y⟯ := by
  rw [← adjoin_simple_adjoin_simple]
  exact subset_adjoin F⟮x⟯ {y} (Set.mem_singleton y)

--DONE
/-- The first generator of an intermediate field of the form `F⟮x, y⟯`. -/
def AdjoinDouble.gen₁ : F⟮x, y⟯ := ⟨x, mem_adjoinDouble_left F x y⟩

--DONE
/-- The second generator of an intermediate field of the form `F⟮x, y⟯`. -/
def AdjoinDouble.gen₂ : F⟮x, y⟯ := ⟨y, mem_adjoinDouble_right F x y⟩

--DONE
@[simp]
theorem AdjoinDouble.algebraMap_gen₁ :
    (algebraMap (↥F⟮x, y⟯) E) (IntermediateField.AdjoinDouble.gen₁ F x y) = x := rfl

--DONE
@[simp]
theorem AdjoinDouble.algebraMap_gen₂ :
    (algebraMap (↥F⟮x, y⟯) E) (IntermediateField.AdjoinDouble.gen₂ F x y) = y := rfl

end IntermediateField
