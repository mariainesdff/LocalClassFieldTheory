/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.FieldTheory.Normal

#align_import from_mathlib.minpoly

/-!
# Minpoly

We prove some auxiliary lemmas about minimal polynomials.

## Main Definitions

* `minpoly.alg_equiv` : the canonical `alg_equiv` between `K⟮x⟯`and `K⟮y⟯`, sending `x` to `y`, where
  `x` and `y` have the same minimal polynomial over `K`, sending `x` to `y`.


## Main Results

* `minpoly.eq_of_conj` : For any `σ : L ≃ₐ[K] L` and `x : L`, the minimal polynomials of `x` and
  `σ x` are equal.
* `minpoly.conj_of_root` :If `y : L` is a root of `minpoly K x`, then we can find `σ : L ≃ₐ[K] L)`
   with `σ x = y`. That is, `x` and `y` are Galois conjugates.

## Tags

minpoly, adjoin_root, conj
-/

-- In PR #12450

noncomputable section

open Polynomial IntermediateField AlgEquiv

open scoped Polynomial

section minpoly

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

namespace AdjoinRoot

/-- The canonical algebraic equivalence between `AdjoinRoot p` and `AdjoinRoot q`, where
  the two polynomial `p q : K[X]` are equal.-/
def id_algEquiv {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot q :=
  ofAlgHom (liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]))
    (liftHom q (root p) (by rw [h_eq, aeval_eq, mk_self]))
    (PowerBasis.algHom_ext (powerBasis hq)
      (by
        rw [powerBasis_gen hq, AlgHom.coe_comp, Function.comp_apply, liftHom_root, liftHom_root,
          AlgHom.coe_id, id_eq]))
    (PowerBasis.algHom_ext (powerBasis hp)
      (by
        rw [powerBasis_gen hp, AlgHom.coe_comp, Function.comp_apply, liftHom_root, liftHom_root,
          AlgHom.coe_id, id_eq]))



theorem id_algEquiv_def' {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
    (id_algEquiv hp hq h_eq).toFun = liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]) :=
  rfl

theorem id_algEquiv_def {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
    (id_algEquiv hp hq h_eq).toAlgHom = liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]) :=
  rfl

/-- `id_alg_equiv` sends `adjoin_root.root p` to `adjoin_root.root q`. -/
theorem id_algEquiv_apply_root {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
    id_algEquiv hp hq h_eq (root p) = root q := by
  rw [← coe_algHom, id_algEquiv_def, liftHom_root]

end AdjoinRoot


namespace minpoly

/-- Given any `σ : L ≃ₐ[K] L` and any `x : L`, the minimal polynomial of `x` vanishes at `σ x`. -/
@[simp]
theorem aeval_conj (σ : L ≃ₐ[K] L) (x : L) : (Polynomial.aeval (σ x)) (minpoly K x) = 0 := by
  rw [Polynomial.aeval_algEquiv, AlgHom.coe_comp, Function.comp_apply, aeval, map_zero]

/-- If `y : L` is a root of `minpoly K x`, then `minpoly K y = minpoly K x`. -/
theorem eq_of_root [Algebra.IsAlgebraic K L] {x y : L}
    (h_ev : (Polynomial.aeval y) (minpoly K x) = 0) : minpoly K y = minpoly K x :=
  Polynomial.eq_of_monic_of_associated (monic (Algebra.IsAlgebraic.isAlgebraic _).isIntegral)
    (monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
    (Irreducible.associated_of_dvd (irreducible (Algebra.IsAlgebraic.isAlgebraic _).isIntegral)
      (irreducible (Algebra.IsAlgebraic.isAlgebraic _).isIntegral) (dvd K y h_ev))


-- This is now `minpoly.algEquiv_eq` in Mathlib
/- For any `σ : L ≃ₐ[K] L` and `x : L`, the minimal polynomials of `x` and `σ x` are equal. -/
@[simp]
theorem eq_of_conj (σ : L ≃ₐ[K] L) (x : L) : minpoly K (σ x) = minpoly K x :=
  minpoly.algEquiv_eq σ x
  /- have h_dvd : minpoly K x ∣ minpoly K (σ x) :=
    by
    apply dvd
    have hx : σ.symm (σ x) = x := σ.left_inv x
    nth_rw 1 [← hx]
    rw [Polynomial.aeval_algEquiv, AlgHom.coe_comp, Function.comp_apply, aeval, map_zero]
  have h_deg : (minpoly K (σ x)).natDegree ≤ (minpoly K x).natDegree := by
    apply Polynomial.natDegree_le_natDegree
        (degree_le_of_ne_zero K _ (ne_zero (h_alg.isAlgebraic _).isIntegral)
          (aeval_conj σ x))
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (monic (h_alg.isAlgebraic _).isIntegral)
      (monic (h_alg.isAlgebraic _).isIntegral) h_dvd h_deg -/

/-- The canonical `algEquiv` between `K⟮x⟯`and `K⟮y⟯`, sending `x` to `y`, where `x` and `y` have
  the same minimal polynomial over `K`. -/
def algEquiv [Algebra.IsAlgebraic K L] {x y : L} (h_mp : minpoly K x = minpoly K y) :
    K⟮x⟯ ≃ₐ[K] K⟮y⟯ :=
  AlgEquiv.trans (adjoinRootEquivAdjoin K (Algebra.IsAlgebraic.isAlgebraic _).isIntegral).symm
    (AlgEquiv.trans (AdjoinRoot.id_algEquiv (ne_zero (Algebra.IsAlgebraic.isAlgebraic _).isIntegral)
        (ne_zero (Algebra.IsAlgebraic.isAlgebraic _).isIntegral) h_mp)
     (adjoinRootEquivAdjoin K (Algebra.IsAlgebraic.isAlgebraic _).isIntegral))

/-- `minpoly.algEquiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`. -/
theorem algEquiv_apply [Algebra.IsAlgebraic K L] {x y : L}
    (h_mp : minpoly K x = minpoly K y) :
    algEquiv h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y := by
  simp only [algEquiv]
  rw [trans_apply, ← adjoinRootEquivAdjoin_apply_root K
    (Algebra.IsAlgebraic.isAlgebraic _).isIntegral, symm_apply_apply, trans_apply,
      AdjoinRoot.id_algEquiv_apply_root,
      adjoinRootEquivAdjoin_apply_root K (Algebra.IsAlgebraic.isAlgebraic _).isIntegral]

/-- If `y : L` is a root of `minpoly K x`, then we can find `σ : L ≃ₐ[K] L)` with `σ x = y`.
  That is, `x` and `y` are Galois conjugates. -/
theorem exists_algEquiv_of_root [Algebra.IsAlgebraic K L] (hn : Normal K L) {x y : L}
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : ∃ σ : L ≃ₐ[K] L, σ x = y := by
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := algEquiv (eq_of_root h_ev)
  have hxy : (liftNormal f L) ((algebraMap (↥K⟮x⟯) L) (AdjoinSimple.gen K x)) = y := by
    rw [liftNormal_commutes f L, algEquiv_apply, AdjoinSimple.algebraMap_gen K y]
  exact ⟨(liftNormal f L), hxy⟩

/-- If `y : L` is a root of `minpoly K x`, then we can find `σ : L ≃ₐ[K] L)` with `σ y = x`.
  That is, `x` and `y` are Galois conjugates. -/
theorem exists_algEquiv_of_root' [Algebra.IsAlgebraic K L] (hn : Normal K L) {x y : L}
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : ∃ σ : L ≃ₐ[K] L, σ y = x :=
  by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_root hn h_ev
  use σ.symm
  rw [← hσ, symm_apply_apply]

end minpoly

end minpoly
