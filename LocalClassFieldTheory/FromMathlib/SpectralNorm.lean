/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Basic
import LocalClassFieldTheory.FromMathlib.AlgNormOfGalois
import LocalClassFieldTheory.FromMathlib.IntermediateField
import LocalClassFieldTheory.FromMathlib.NormalClosure
import LocalClassFieldTheory.FromMathlib.Polynomial
import LocalClassFieldTheory.FromMathlib.RingSeminorm

/-!
# The spectral norm and the norm extension theorem

We define the spectral value and the spectral norm. We prove the norm extension theorem
[BGR, Theorem 3.2.1/2] : given a nonarchimedean, multiplicative normed field `K` and an algebraic
extension `L/K`, the spectral norm is a power-multiplicative `K`-algebra norm on `L` extending
the norm on `K`. All `K`-algebra automorphisms of `L` are isometries with respect to this norm.
If `L/K` is finite, we get a formula relating the spectral norm on `L` with any other
power-multiplicative norm on `L` extending the norm on `K`.

As a prerequisite, we formalize the proof of [BGR, Proposition 3.1.2/1].

## Main Definitions

* `spectralValue` : the spectral value of a polynomial in `R[X]`.
* `spectralNorm` :The spectral norm `|y|_sp` is the spectral value of the minimal of `y` over `K`.
* `spectralAlgNorm` : the spectral norm is a `K`-algebra norm on `L`.

## Main Results

* `spectralNorm_ge_norm` : if `f` is a power-multiplicative `K`-algebra norm on `L` with `f 1 ≤ 1`,
  then `f` is bounded above by `spectralNorm K L`.
* `spectralNorm_aut_isom` : the `K`-algebra automorphisms of `L` are isometries with respect to
  the spectral norm.
* `spectralNorm_max_of_fd_normal` : iff `L/K` is finite and normal, then
  `spectralNorm K L x = supr (λ (σ : L ≃ₐ[K] L), f (σ x))`.
* `spectralNorm_is_pow_mul` : the spectral norm is power-multiplicative.
* `spectralNorm_is_nonarchimedean` : the spectral norm is nonarchimedean.
* `spectralNorm_extends` : the spectral norm extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, spectral value, seminorm, norm, nonarchimedean
-/

-- This file is PR in #23204, #23253, #23254

open Polynomial Multiset

open scoped Polynomial


noncomputable section

universe u_1 u_2

-- Auxiliary lemmas
section AuxLemmas

namespace List

variable {α : Type*} [LinearOrder α]

-- Mathlib.Order.Lattice. Try Mathlib.Data.List.MinMax?
-- Unused
/- theorem max_replicate {n : ℕ} (a : α) : foldr max a (replicate n a) = a := by
  induction n with
  | zero => simp only [List.replicate,  List.foldr_nil]
  | succ n hn =>
    simp only [foldr, replicate , foldr_cons, max_eq_left_iff]
    exact le_of_eq hn -/

-- In PR #23204
-- Mathlib.Order.MinMax. Try Mathlib.Data.List.MinMax?
theorem le_max_of_le' {l : List α} {a x : α} (b : α) (hx : x ∈ l) (h : a ≤ x) :
    a ≤ l.foldr max b := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil _)
  | cons y l IH =>
    simp only [List.foldr, List.foldr_cons]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

end List

-- In PR #23254
-- [Mathlib.Data.NNReal.Basic]
theorem multiset_prod_le_pow_card {F L : Type*} [AddCommGroup L] [FunLike F L ℝ]
    [AddGroupSeminormClass F L ℝ] {f : F} {y : L} {t : Multiset L}
    (hf : ∀ x : ℝ, x ∈ Multiset.map f t → x ≤ f y) :
    (Multiset.map f t).prod ≤ f y ^ card (map f t) := by
  set g : L → NNReal := fun x : L ↦ ⟨f x, apply_nonneg _ _⟩
  have hg_le : (Multiset.map g t).prod ≤ g y ^ card (map g t) := by
    apply prod_le_pow_card
    intro x hx
    obtain ⟨a, hat, hag⟩ := mem_map.mp hx
    rw [Subtype.ext_iff, Subtype.coe_mk] at hag
    exact hf (x : ℝ) (mem_map.mpr ⟨a, hat, hag⟩)
  rw [← NNReal.coe_le_coe] at hg_le
  convert hg_le
  · simp [NNReal.coe_multiset_prod, Multiset.map_map, Function.comp_apply, NNReal.coe_mk, g]
  · simp [card_map, g]

/--[Mathlib.Topology.Instances.Sign, Mathlib.Data.Nat.Factorization.Basic,
Mathlib.Algebra.Star.Subalgebra, Mathlib.Algebra.BigOperators.Expect,
Mathlib.Data.Matrix.ConjTranspose, Mathlib.Data.Nat.Choose.Sum, Mathlib.Algebra.GeomSum,
Mathlib.Topology.EMetricSpace.Basic, Mathlib.GroupTheory.Perm.Cycle.Type,
Mathlib.Algebra.Order.ToIntervalMod, Mathlib.Analysis.Convex.Function,
Mathlib.Algebra.Field.Periodic, Mathlib.Algebra.CharP.Algebra,
 Mathlib.Topology.Algebra.Group.Basic, Mathlib.RingTheory.TensorProduct.Basic,
 Mathlib.Algebra.Field.NegOnePow, Mathlib.Data.Real.EReal] -/
theorem map_multiset_prod_le_of_submultiplicative {α β : Type*} [CommMonoid α] [LinearOrderedCommSemiring β] {f : α → β}
    (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) : f s.prod ≤ (s.map f).prod := by
  set g : α → {b : β // 0 ≤ b} := fun x : α ↦ ⟨f x, h_nonneg _⟩
  have hg_le : g s.prod ≤ (s.map g).prod := by
    apply Multiset.le_prod_of_submultiplicative
    · ext
      simp [g, Nonneg.coe_one, h_one]
    · intro a b
      rw [← Subtype.coe_le_coe, Nonneg.mk_mul_mk]
      exact h_mul _ _
  rw [← Subtype.coe_le_coe] at hg_le
  convert hg_le
  apply Multiset.induction_on s (p := fun s ↦ (Multiset.map f s).prod = ↑(Multiset.map g s).prod)
  · simp [Multiset.map_zero, prod_zero, Nonneg.coe_one, g]
  · intro a s hs
    simp only [map_cons, prod_cons, Nonneg.coe_mul, g, hs]

namespace Multiset

section Decidable

variable {α : Type*} [DecidableEq α]

/- [Mathlib.Topology.EMetricSpace.Defs, Mathlib.Topology.Algebra.Order.LiminfLimsup,
Mathlib.Data.NNReal.Basic, Mathlib.Data.Complex.BigOperators,
Mathlib.Data.Complex.Module, Mathlib.Topology.Order.Real]-/
theorem exists_max (f : α → ℝ) {s : Multiset α} (hs : s.toFinset.Nonempty) :
    ∃ y : α, y ∈ s ∧ ∀ z : α, z ∈ s → f z ≤ f y := by
  have hsf : (map f s).toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hs.exists_mem
    exact ⟨f x, mem_toFinset.mpr (mem_map.mpr ⟨x, mem_toFinset.mp hx, rfl⟩)⟩
  have h := (s.map f).toFinset.max'_mem hsf
  rw [mem_toFinset, mem_map] at h
  obtain ⟨y, hys, hymax⟩ := h
  use y, hys
  intro z hz
  rw [hymax]
  exact Finset.le_max' _ _ (mem_toFinset.mpr (mem_map.mpr ⟨z, hz, rfl⟩))

-- try import Mathlib.Data.Multiset.ZeroCons
/- [Mathlib.Topology.EMetricSpace.Defs, Mathlib.Topology.Algebra.Order.LiminfLimsup,
Mathlib.Data.NNReal.Basic, Mathlib.Data.Complex.BigOperators,
Mathlib.Data.Complex.Module, Mathlib.Topology.Order.Real]-/
theorem card_toFinset_pos {m : Multiset α} (hm : 0 < card m) : 0 < m.toFinset.card := by
  obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp hm
  exact Finset.card_pos.mpr ⟨x, mem_toFinset.mpr hx⟩

end Decidable

@[to_additive existing le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred_of_nonneg {α β : Type*} [CommMonoid α]
    [OrderedCommRing β] (f : α → β) (p : α → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1)
    (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine Multiset.induction (by simp [le_of_eq h_one]) ?_
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx ↦ hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans
    (mul_le_mul_of_nonneg_left (hs hps) (h_nonneg _))

-- Try Mathlib.Algebra.Order.BigOperators.Group.Multiset or ring version
theorem le_prod_of_submultiplicative_of_nonneg {α β : Type*} [CommMonoid α] [OrderedCommRing β]
    (f : α → β)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) : f s.prod ≤ (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ ↦ True) h_nonneg h_one trivial
    (fun x y _ _ ↦ h_mul x y) (by simp) s (by simp)

--#find_home! le_prod_of_submultiplicative_of_nonneg

end Multiset

namespace Finset

-- Try Mathlib.Algebra.Order.BigOperators.Group.Finset or
-- Mathlib.Algebra.Order.BigOperators.Ring.Finset,
/-- [Mathlib.Algebra.BigOperators.Finprod, Mathlib.RingTheory.Coprime.Lemmas,
 Mathlib.SetTheory.Cardinal.Basic, Mathlib.Algebra.BigOperators.WithTop,
 Mathlib.Algebra.Order.BigOperators.Ring.Finset, Mathlib.RingTheory.Multiplicity,
 Mathlib.RingTheory.UniqueFactorizationDomain.Basic, Mathlib.Algebra.BigOperators.Intervals,
 Mathlib.RingTheory.Localization.Defs, Mathlib.Algebra.Star.Module, Mathlib.GroupTheory.Perm.Sign,
  Mathlib.Topology.EMetricSpace.Basic, Mathlib.Data.Sign, Mathlib.Data.Finsupp.Order,
  Mathlib.RingTheory.Ideal.Lattice, Mathlib.NumberTheory.Divisors]-/
theorem le_prod_of_submultiplicative_of_nonneg {ι M N : Type*} [CommMonoid M] [OrderedCommRing N]
    (f : M → N) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1)
    (h_mul : ∀ x y : M, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (s.prod fun i : ι ↦ g i) ≤ s.prod fun i : ι ↦ f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

end Finset

section IsNonarchimedean

--variable {K L : Type*} [NormedCommRing K] [CommRing L] [Algebra K L]

-- In PR #23253
open Finset in
-- [Mathlib.Data.Real.IsNonarchimedean]
theorem isNonarchimedean_finset_powerset_image_add {F K : Type*} [CommRing K] [FunLike F K ℝ]
    [AddGroupSeminormClass F K ℝ] {f : F}
    (hf_na : IsNonarchimedean f) {n : ℕ} (b : Fin n → K) (m : ℕ) :
    ∃ s : powersetCard (Fintype.card (Fin n) - m) (@univ (Fin n) _),
      f ((powersetCard (Fintype.card (Fin n) - m) univ).sum fun t : Finset (Fin n) ↦
        t.prod fun i : Fin n ↦ -b i) ≤ f (s.val.prod fun i : Fin n ↦ -b i) := by
  set g := fun t : Finset (Fin n) ↦ t.prod fun i : Fin n ↦ - b i
  obtain ⟨b, hb_in, hb⟩ := IsNonarchimedean.finset_image_add hf_na g
      (powersetCard (Fintype.card (Fin n) - m) univ)
  have hb_ne : (powersetCard (Fintype.card (Fin n) - m) (univ : Finset (Fin n))).Nonempty := by
    rw [Fintype.card_fin]
    have hmn : n - m ≤ (univ : Finset (Fin n)).card := by
      rw [card_fin]
      exact Nat.sub_le n m
    exact powersetCard_nonempty.mpr hmn
  use ⟨b, hb_in hb_ne⟩, hb

-- In PR #23253
open Multiset in
-- [Mathlib.Data.Real.IsNonarchimedean]
theorem isNonarchimedean_multiset_powerset_image_add {F K : Type*} [CommRing K] [FunLike F K ℝ]
    [AddGroupSeminormClass F K ℝ] {f : F}
    (hf_na : IsNonarchimedean f) (s : Multiset K) (m : ℕ) :
    ∃ t : Multiset K, card t = card s - m ∧ (∀ x : K, x ∈ t → x ∈ s) ∧
      f (map prod (powersetCard (card s - m) s)).sum ≤ f t.prod := by
  set g := fun t : Multiset K ↦ t.prod
  obtain ⟨b, hb_in, hb_le⟩ :=
    IsNonarchimedean.multiset_image_add hf_na g (powersetCard (card s - m) s)
  have hb : b ≤ s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    apply hb_in
    refine card_pos.mp ?_
    rw [card_powersetCard]
    exact Nat.choose_pos ((card s).sub_le m)
  exact ⟨b, hb.2, fun x hx ↦ mem_of_le hb.left hx, hb_le⟩

end IsNonarchimedean

/- Not needed anymore

 namespace AuxiliaryInstances

open IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)

--attribute [local instance 1001] Algebra.id

/- -- MI: I am not sure if this is the right thing to remove now, the file is really slow.
attribute [-instance]
  --Subalgebra.instSMulSubtypeMemSubalgebraInstMembershipInstSetLikeSubalgebra
  Subalgebra.instSMulSubtypeMem
  Subsemiring.smul
  Submonoid.smul
  IntermediateField.module'
  Subalgebra.isScalarTower_left
  Subsemiring.isScalarTower
  Submonoid.isScalarTower -/


-- Auxiliary instances to avoid timeouts

--set_option synthInstance.maxHeartbeats 400000
--instance : Algebra E ↥(normalClosure K E (AlgebraicClosure E)) := inferInstance
  --normalClosure.algebra K (↥E) (AlgebraicClosure ↥E) -- inferInstance used to work

--instance :  SMul ↥E ↥(normalClosure K (↥E) (AlgebraicClosure ↥E)) := inferInstance
  --Algebra.toSMul -- inferInstance used to work

--instance : AddGroup ↥(normalClosure K E (AlgebraicClosure E)) := inferInstance

--set_option maxHeartbeats 300000
--instance : IsScalarTower K E (normalClosure K (↥E) (AlgebraicClosure ↥E)) := inferInstance

/- instance : MonoidHomClass (E →+* ↥(normalClosure K E (AlgebraicClosure E))) E
  ↥(normalClosure K E (AlgebraicClosure E)) :=
  inferInstance  -//- by exact MonoidHomClass.mk -/

-- MI: timeout
/- instance : AddHomClass (E →+* ↥(normalClosure K E (AlgebraicClosure E))) E
  ↥(normalClosure K E (AlgebraicClosure E)) := inferInstance --AddMonoidHomClass.toAddHomClass

instance : MulHomClass (E →+* ↥(normalClosure K E (AlgebraicClosure E))) E
  ↥(normalClosure K E (AlgebraicClosure E)) := inferInstance

instance : AddHomClass (E →+* L) E L := inferInstance -/

-- End of auxiliary instances

end AuxiliaryInstances -/

section

variable {K L : Type*} [NormedField K] [Ring L] [Algebra K L]

theorem extends_is_norm_le_one_class {f : L → ℝ} (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) :
    f 1 ≤ 1 := by rw [← (algebraMap K L).map_one, hf_ext, norm_one]

theorem extends_is_norm_one_class {f : L → ℝ} (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) :
    f 1 = 1 := by rw [← (algebraMap K L).map_one, hf_ext, norm_one]

end

end AuxLemmas

variable {R : Type*}

section spectralValue

section Seminormed

variable [SeminormedRing R]

/-- The function `ℕ → ℝ` sending `n` to `‖ p.coeff n ‖^(1/(p.natDegree - n : ℝ))`, if
  `n < p.natDegree`, or to `0` otherwise. -/
def spectralValueTerms (p : R[X]) : ℕ → ℝ := fun n : ℕ ↦
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) else 0

theorem spectralValueTerms_of_lt_natDegree (p : R[X]) {n : ℕ} (hn : n < p.natDegree) :
    spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) := by
  simp only [spectralValueTerms, if_pos hn]

theorem spectralValueTerms_of_natDegree_le (p : R[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    spectralValueTerms p n = 0 := by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

/-- The spectral value of a polynomial in `R[X]`. -/
def spectralValue (p : R[X]) : ℝ :=
  iSup (spectralValueTerms p)

/-- The sequence `spectralValue_terms p` is bounded above. -/
theorem spectralValueTerms_bddAbove (p : R[X]) : BddAbove (Set.range (spectralValueTerms p)) := by
  use List.foldr max 0
      (List.map (fun n ↦ ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ))) (List.range p.natDegree))
  · rw [mem_upperBounds]
    intro r hr
    obtain ⟨n, hn⟩ := Set.mem_range.mpr hr
    simp only [spectralValueTerms] at hn
    split_ifs at hn  with hd
    · have h : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) ∈
        List.map (fun n : ℕ ↦ ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)))
          (List.range p.natDegree) :=  by
        simp only [List.mem_map, List.mem_range]
        exact ⟨n, hd, rfl⟩
      exact List.le_max_of_le' 0 h (ge_of_eq hn)
    · rw [← hn]
      by_cases hd0 : p.natDegree = 0
      · rw [hd0, List.range_zero, List.map_nil, List.foldr_nil]
      · have h :
          ‖p.coeff 0‖ ^ (1 / (p.natDegree - 0 : ℝ)) ∈
            List.map (fun n : ℕ ↦ ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)))
              (List.range p.natDegree) := by
          simp only [List.mem_map, List.mem_range]
          exact ⟨0, Nat.pos_of_ne_zero hd0, by rw [Nat.cast_zero]⟩
        refine List.le_max_of_le' 0 h ?_
        exact Real.rpow_nonneg (norm_nonneg _) _

/-- The range of `spectralValue_terms p` is a finite set. -/
theorem spectralValueTerms_finite_range (p : R[X]) : (Set.range (spectralValueTerms p)).Finite :=
  haveI h_ss :
    Set.range (spectralValueTerms p) ⊆
      (Set.range fun n : Fin p.natDegree ↦ ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ))) ∪
        {(0 : ℝ)} := by
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_range.mpr hx
    by_cases hm_lt : m < p.natDegree
    · simp only [spectralValueTerms_of_lt_natDegree p hm_lt] at hm
      rw [← hm]
      exact Set.mem_union_left _ ⟨⟨m, hm_lt⟩, rfl⟩
    · simp only [spectralValueTerms_of_natDegree_le p (le_of_not_lt hm_lt)] at hm
      rw [hm]
      exact Set.mem_union_right _ (Set.mem_singleton _)
  Set.Finite.subset (Set.Finite.union (Set.finite_range _) (Set.finite_singleton _)) h_ss

/-- The sequence `spectralValue_terms p` is nonnegative. -/
theorem spectralValueTerms_nonneg (p : R[X]) (n : ℕ) : 0 ≤ spectralValueTerms p n := by
  simp only [spectralValueTerms]
  split_ifs with h
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · exact le_refl _

/-- The spectral value of a polyomial is nonnegative. -/
theorem spectralValue_nonneg (p : R[X]) : 0 ≤ spectralValue p :=
  Real.iSup_nonneg (spectralValueTerms_nonneg p)

variable [Nontrivial R]

/-- The polynomial `X - r` has spectral value `‖ r ‖`. -/
theorem spectralValue_x_sub_c (r : R) : spectralValue (X - C r) = ‖r‖ := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp only [natDegree_X_sub_C, Nat.lt_one_iff, coeff_sub, Nat.cast_one, one_div]
  suffices (⨆ n : ℕ, ite (n = 0) ‖r‖ 0) = ‖r‖ by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, Nat.cast_zero, sub_zero, coeff_X_zero, coeff_C_zero, zero_sub,
        norm_neg, inv_one, Real.rpow_one]
    · rw [if_neg hn, if_neg hn]
  · apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    · intro n
      split_ifs
      exact le_refl _
      exact norm_nonneg _
    · intro x hx; use 0
      simp only [eq_self_iff_true, if_true, hx]

/-- The polynomial `X^n` has spectral value `0`. -/
theorem spectralValue_x_pow (n : ℕ) : spectralValue (X ^ n : R[X]) = 0 := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp_rw [coeff_X_pow n, natDegree_X_pow]
  convert ciSup_const using 2
  ext m
  by_cases hmn : m < n
  · rw [if_pos hmn, Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (ne_of_lt hmn),
      norm_zero, one_div, ne_eq, inv_eq_zero, ← Nat.cast_sub (le_of_lt hmn), Nat.cast_eq_zero,
      Nat.sub_eq_zero_iff_le]
    exact ⟨Eq.refl _, not_le_of_lt hmn⟩
  · rw [if_neg hmn]
  infer_instance

end Seminormed

section Normed

variable [NormedRing R]

/-- The spectral value of `p` equals zero if and only if `p` is of the form `X^n`. -/
theorem spectralValue_eq_zero_iff [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    spectralValue p = 0 ↔ p = X ^ p.natDegree := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [spectralValue] at h
    ext n
    rw [coeff_X_pow]
    by_cases hn : n = p.natDegree
    · rw [if_pos hn, hn, coeff_natDegree]; exact hp
    · rw [if_neg hn]
      · by_cases hn' : n < p.natDegree
        · have h_le : iSup (spectralValueTerms p) ≤ 0 := le_of_eq h
          have h_exp : 0 < 1 / ((p.natDegree : ℝ) - n) :=
            by
            rw [one_div_pos, ← Nat.cast_sub (le_of_lt hn'), Nat.cast_pos]
            exact Nat.sub_pos_of_lt hn'
          have h0 : (0 : ℝ) = 0 ^ (1 / ((p.natDegree : ℝ) - n)) := by
            rw [Real.zero_rpow (ne_of_gt h_exp)]
          rw [iSup, csSup_le_iff (spectralValueTerms_bddAbove p) (Set.range_nonempty _)] at h_le
          specialize h_le (spectralValueTerms p n) ⟨n, rfl⟩
          simp only [spectralValueTerms, if_pos hn'] at h_le
          rw [h0, Real.rpow_le_rpow_iff (norm_nonneg _) (le_refl _) h_exp] at h_le
          exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _))
        · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn))
  · convert spectralValue_x_pow p.natDegree
    infer_instance

end Normed

end spectralValue

-- In this section we prove Proposition 3.1.2/1 from BGR.
section BddBySpectralValue

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]

/-- Part (1): the norm of any root of p is bounded by the spectral value of p. -/
theorem root_norm_le_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 ≤ 1) {p : K[X]} (hp : p.Monic) {x : L}
    (hx : aeval x p = 0) : f x ≤ spectralValue p := by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra h_ge
    have hn_lt : ∀ (n : ℕ) (_ : n < p.natDegree), ‖p.coeff n‖ < f x ^ (p.natDegree - n) := by
      intro n hn
      have hexp : (‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ))) ^ (p.natDegree - n) =
        ‖p.coeff n‖ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_comm,
          Real.rpow_mul (norm_nonneg _), Real.rpow_natCast, ← Nat.cast_sub (le_of_lt hn), one_div,
          Real.pow_rpow_inv_natCast (norm_nonneg _) (ne_of_gt (tsub_pos_of_lt hn))]
      have h_base : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) < f x := by
        rw [spectralValue, iSup, not_le, Set.Finite.csSup_lt_iff (spectralValueTerms_finite_range p)
            (Set.range_nonempty (spectralValueTerms p))] at h_ge
        have h_rg : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) ∈ Set.range (spectralValueTerms p) :=
          by use n; simp only [spectralValueTerms, if_pos hn]
        exact h_ge (‖p.coeff n‖₊ ^ (1 / (p.natDegree - n : ℝ))) h_rg
      rw [← hexp, ← Real.rpow_natCast, ← Real.rpow_natCast]
      exact Real.rpow_lt_rpow (Real.rpow_nonneg (norm_nonneg _) _) h_base
        (Nat.cast_pos.mpr (tsub_pos_of_lt hn))
    have h_deg : 0 < p.natDegree := Polynomial.natDegree_pos_of_monic_of_root hp hx
    have : ‖(1 : K)‖ = 1 := norm_one
    have h_lt :
      f ((Finset.range p.natDegree).sum fun i : ℕ ↦ p.coeff i • x ^ i) < f (x ^ p.natDegree) := by
      have hn' : ∀ (n : ℕ) (_ : n < p.natDegree), f (p.coeff n • x ^ n) < f (x ^ p.natDegree) := by
        intro n hn
        by_cases hn0 : n = 0
        · rw [hn0, pow_zero, map_smul_eq_mul, hf_pm _ (Nat.succ_le_iff.mpr h_deg), ←
            Nat.sub_zero p.natDegree, ← hn0]
          exact (mul_le_of_le_one_right (norm_nonneg _) hf1).trans_lt (hn_lt n hn)
        · have : p.natDegree = p.natDegree - n + n := by rw [Nat.sub_add_cancel (le_of_lt hn)]
          rw [map_smul_eq_mul, hf_pm _ (Nat.succ_le_iff.mp (pos_iff_ne_zero.mpr hn0)),
            hf_pm _ (Nat.succ_le_iff.mpr h_deg), this, pow_add]
          exact
            (mul_lt_mul_right (pow_pos (lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hx0)) _)).mpr
              (hn_lt n hn)
      set g := fun i : ℕ ↦ p.coeff i • x ^ i
      obtain ⟨m, hm_in, hm⟩ : ∃ (m : ℕ) (_ : 0 < p.natDegree → m < p.natDegree),
          f ((Finset.range p.natDegree).sum g) ≤ f (g m) := by
        obtain ⟨m, hm, h⟩ := IsNonarchimedean.finset_image_add hf_na g (Finset.range p.natDegree)
        rw [Finset.nonempty_range_iff, ← zero_lt_iff, Finset.mem_range] at hm
        exact ⟨m, hm, h⟩
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg))
    have h0 : f 0 ≠ 0 := by
      have h_eq : f 0 = f (x ^ p.natDegree) := by
        rw [← hx, aeval_eq_sum_range, Finset.sum_range_succ, add_comm, hp.coeff_natDegree,
          one_smul, ← max_eq_left_of_lt h_lt]
        exact IsNonarchimedean.add_eq_max_of_ne hf_na (ne_of_gt h_lt)
      rw [h_eq]
      exact ne_of_gt (lt_of_le_of_lt (apply_nonneg _ _) h_lt)
    exact h0 (map_zero _)

open scoped Classical

open Multiset

/- Part (2): if p splits into linear factors over B, then its spectral value equals the maximum
  of the norms of its roots. -/
/- theorem max_root_norm_eq_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) {n : ℕ} (hn : 0 < n) (b : Fin n → L)
    (hp : mapAlg K L p = finprod fun k : Fin n ↦ X - C (b k)) :
    iSup (f ∘ b) = spectralValue p := by
  apply le_antisymm
  · haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    apply ciSup_le
    rintro m
    have hm : aeval (b m) p = 0 := by
      have hm' : aeval (b m) ((mapAlg K L) p) = 0 := by
        have hd1 : (aeval (b m)) (X - C (b m)) = 0 := by
          rw [coe_aeval_eq_eval, eval_sub, eval_X, eval_C, sub_self]
        rw [hp, finprod_eq_prod_of_fintype, aeval_def, eval₂_finset_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ m) hd1
      rw [mapAlg_eq_map, aeval_map_algebraMap] at hm'
      exact hm'
    rw [Function.comp_apply]
    exact root_norm_le_spectralValue hf_pm hf_na (le_of_eq hf1) (p.monic_of_eq_finprod b hp) hm
  · have : Nonempty (Fin n) := by
      exact Fin.pos_iff_nonempty.mp hn
    have h_supr : 0 ≤ iSup (f ∘ b) := by
      exact Real.iSup_nonneg fun x ↦ apply_nonneg f (b x)
    apply ciSup_le
    intro m
    by_cases hm : m < p.natDegree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.natDegree - m : ℝ) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg (norm_nonneg _) _) h_supr h, ←
        Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (ne_of_gt h), Real.rpow_one, ←
        Nat.cast_sub (le_of_lt hm), Real.rpow_natCast]
      have hpn : n = p.natDegree := by
        rw [← natDegree_map (algebraMap K L), ← mapAlg_eq_map, hp, finprod_eq_prod_of_fintype,
          Polynomial.prod_x_add_c_natDegree]
      have hc : ‖p.coeff m‖ = f (((mapAlg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1, mapAlg_eq_map, coeff_map]
      rw [hc, hp, finprod_eq_prod_of_fintype]
      simp_rw [sub_eq_add_neg, ← C_neg, Finset.prod_eq_multiset_prod, ← Pi.neg_apply]
      have : (fun x ↦ X + C ((-b) x)) = (fun y ↦ ((fun x : L ↦ X + C x) ∘ (-b)) y) := rfl
      rw [this, ← Multiset.map_map (fun x : L ↦ X + C x) (-b)]
      have hm_le' : m ≤ card (Multiset.map (-b) Finset.univ.val) := by
        have : card Finset.univ.val = Finset.card (Finset.univ : Finset (Fin n)) := rfl
        rw [card_map, this, Finset.card_fin n, hpn]
        exact le_of_lt hm
      rw [prod_X_add_C_coeff _ hm_le']
      have : m < n := by rw [hpn]; exact hm
      obtain ⟨s, hs⟩ := isNonarchimedean_finset_powerset_image_add hf_na b m
      rw [Finset.esymm_map_val]
      have h_card : card (Multiset.map (-b) Finset.univ.val) = Fintype.card (Fin n) := by
        rw [card_map]; rfl
      rw [h_card]
      apply le_trans hs
      have h_pr : f (s.val.prod fun i : Fin n ↦ -b i) ≤ s.val.prod fun i : Fin n ↦ f (-b i) :=
        Finset.le_prod_of_submultiplicative' f (apply_nonneg _) hf1 (map_mul_le_mul _) _ _
      apply le_trans h_pr
      have : (s.val.prod fun i : Fin n ↦ f (-b i)) ≤ s.val.prod fun _ : Fin n ↦ iSup (f ∘ b) :=
        by
        apply Finset.prod_le_prod
        · intro i _; exact apply_nonneg _ _
        · intro i _
          rw [map_neg_eq_map]
          exact le_ciSup (Set.Finite.bddAbove (Set.range (f ∘ b)).toFinite) _
      apply le_trans this
      apply le_of_eq
      simp only [Finset.prod_const]
      suffices h_card : (s : Finset (Fin n)).card = p.natDegree - m by
        rw [h_card]
      have hs' := s.property
      simp only [Fintype.card_fin, Finset.mem_powersetCard] at hs'
      rw [hs'.right, hpn]
    rw [spectralValueTerms_of_natDegree_le _ (le_of_not_lt hm)]
    exact h_supr -/

/-- If `f` is a nonarchimedean, power-multiplicative `K`-algebra norm on `L`, then the spectral
  value of a polynomial `p : K[X]` that decomposes into linear factos in `L` is equal to the
  maximum of the norms of the roots. -/
theorem max_root_norm_eq_spectralValue' {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (Multiset.map (fun a : L ↦ X - C a) s).prod) :
    (iSup fun x : L ↦ if x ∈ s then f x else 0) = spectralValue p := by
  have h_le : 0 ≤ ⨆ x : L, ite (x ∈ s) (f x) 0 := by
    apply Real.iSup_nonneg
    intro x
    split_ifs
    exacts [apply_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le
    rintro x
    by_cases hx : x ∈ s
    · have hx0 : aeval x p = 0 := Polynomial.aeval_root s hx hp
      rw [if_pos hx]
      exact root_norm_le_spectralValue hf_pm hf_na (le_of_eq hf1) (p.monic_of_eq_multiset_prod s hp) hx0
    · rw [if_neg hx]
      exact spectralValue_nonneg _
  · apply ciSup_le
    intro m
    by_cases hm : m < p.natDegree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.natDegree - m : ℝ) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg (norm_nonneg _) _) h_le h, ←
        Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (ne_of_gt h), Real.rpow_one, ←
        Nat.cast_sub (le_of_lt hm), Real.rpow_natCast]
      have hps : card s = p.natDegree := by
        rw [← natDegree_map (algebraMap K L), ← mapAlg_eq_map, hp,
          natDegree_multiset_prod_X_sub_C_eq_card]
      have hc : ‖p.coeff m‖ = f (((mapAlg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1, mapAlg_eq_map, coeff_map]
      rw [hc, hp]
      have hm_le' : m ≤ card s := by rw [hps]; exact le_of_lt hm
      rw [prod_X_sub_C_coeff s hm_le']
      have h : f ((-1) ^ (card s - m) * s.esymm (card s - m)) = f (s.esymm (card s - m)) := by
        cases' neg_one_pow_eq_or L (card s - m) with h1 hn1
        · rw [h1, one_mul]
        · rw [hn1, neg_mul, one_mul, map_neg_eq_map]
      rw [h, Multiset.esymm]
      have ht :
        ∃ t : Multiset L,
          card t = card s - m ∧
            (∀ x : L, x ∈ t → x ∈ s) ∧
              f (Multiset.map Multiset.prod (powersetCard (card s - m) s)).sum ≤ f t.prod :=
        haveI hm' : m < card s := by rw [hps]; exact hm
        isNonarchimedean_multiset_powerset_image_add hf_na s m
      obtain ⟨t, ht_card, hts, ht_ge⟩ := ht
      apply le_trans ht_ge
      have h_pr : f t.prod ≤ (t.map f).prod :=
        map_multiset_prod_le_of_submultiplicative (apply_nonneg _) hf1 (map_mul_le_mul _) _
      apply le_trans h_pr
      have hs_ne : s.toFinset.Nonempty :=
        Finset.card_pos.mp (card_toFinset_pos (hps ▸ lt_of_le_of_lt (zero_le _) hm))
      have hy : ∃ y : L, y ∈ s ∧ ∀ z : L, z ∈ s → f z ≤ f y := Multiset.exists_max f hs_ne
      obtain ⟨y, hyx, hy_max⟩ := hy
      have : (Multiset.map f t).prod ≤ f y ^ (p.natDegree - m) := by
        have h_card : p.natDegree - m = card (t.map f) := by rw [card_map, ht_card, ← hps]
        have hx_le : ∀ x : ℝ, x ∈ Multiset.map f t → x ≤ f y := by
          intro r hr
          obtain ⟨_, hzt, hzr⟩ := Multiset.mem_map.mp hr
          exact hzr ▸ hy_max _ (hts _ hzt)
        rw [h_card]
        exact multiset_prod_le_pow_card hx_le
      have h_bdd : BddAbove (Set.range fun x : L ↦ ite (x ∈ s) (f x) 0) := by
        use f y
        rw [mem_upperBounds]
        intro r hr
        obtain ⟨z, hz⟩ := Set.mem_range.mpr hr
        simp only at hz
        rw [← hz]
        split_ifs with h
        · exact hy_max _ h
        · exact apply_nonneg _ _
      apply le_trans this
      apply pow_le_pow_left₀ (apply_nonneg _ _)
      apply le_trans _ (le_ciSup h_bdd y)
      rw [if_pos hyx]
    · simp only [spectralValueTerms]
      rw [if_neg hm]
      exact h_le

end BddBySpectralValue

section AlgEquiv

variable {S A B C : Type*} [CommSemiring S] [Semiring A] [Semiring B] [Semiring C] [Algebra S A]
  [Algebra S B] [Algebra S C]

/-- The algebra equivalence obtained by composing two algebra equivalences. -/
def AlgEquiv.comp (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C) : A ≃ₐ[S] C where
  toFun := g.toFun ∘ f.toFun
  invFun := f.invFun ∘ g.invFun
  left_inv x := by
    simp only [toEquiv_eq_coe, Equiv.invFun_as_coe, symm_toEquiv_eq_symm, EquivLike.coe_coe,
      Equiv.toFun_as_coe, Function.comp_apply, symm_apply_apply]
  right_inv x := by
    simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
      symm_toEquiv_eq_symm, Function.comp_apply, apply_symm_apply]
  map_mul' x y := by simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Function.comp_apply, map_mul]
  map_add' x y := by simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Function.comp_apply, _root_.map_add]
  commutes' x := by simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Function.comp_apply, commutes]

theorem AlgEquiv.comp_apply (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C) (x : A) : f.comp g x = g (f x) :=
  rfl

end AlgEquiv

-- In this section we prove Theorem 3.2.1/2 from BGR.
section spectralNorm

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

/-- The spectral norm `|y|_sp` is the spectral value of the minimal of `y` over `K`. -/
def spectralNorm (y : L) : ℝ :=
  spectralValue (minpoly K y)

variable {K L}

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` equals its spectral norm
  when regarding `x` as an element of `L`. -/
theorem spectralValue.eq_of_tower {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    spectralNorm K E x = spectralNorm K L (algebraMap E L x) := by
  have hx :  minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  simp only [spectralNorm, hx]

variable (E : IntermediateField K L)

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` when regarded as an element
  of the normal closure of `E` equals its spectral norm when regarding `x` as an element of `L`. -/
theorem spectralValue.eq_normal (x : E) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
        (algebraMap E (normalClosure K E (AlgebraicClosure E)) x) =
      spectralNorm K L (algebraMap E L x) := by
  simp only [spectralNorm, spectralValue]
  have h_min : minpoly K (algebraMap (↥E) (↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) x) =
      minpoly K (algebraMap (↥E) L x) := by
    rw [minpoly.algebraMap_eq
        (algebraMap (↥E) ↥(normalClosure K E (AlgebraicClosure E))).injective x,
      ← minpoly.algebraMap_eq (algebraMap (↥E) L).injective x]
  simp_rw [h_min]

variable (y : L)

/-- `spectralNorm K L (0 : L) = 0`. -/
theorem spectralNorm_zero : spectralNorm K L (0 : L) = 0 := by
  rw [spectralNorm, spectralValue]
  unfold spectralValueTerms
  rw [minpoly.zero, natDegree_X]
  convert ciSup_const using 2
  · ext m
    by_cases hm : m < 1
    · rw [if_pos hm, Nat.lt_one_iff.mp hm, Nat.cast_one, Nat.cast_zero, sub_zero, div_one,
        Real.rpow_one, coeff_X_zero, norm_zero]
    · rw [if_neg hm]
  · infer_instance


/-- `spectralNorm K L y` is nonnegative. -/
theorem spectralNorm_nonneg (y : L) : 0 ≤ spectralNorm K L y :=
  le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

/-- `spectralNorm K L y` is positive if `y ≠ 0`. -/
theorem spectralNorm_zero_lt {y : L} (hy : y ≠ 0) (hy_alg : IsAlgebraic K y) :
    0 < spectralNorm K L y := by
  rw [lt_iff_le_and_ne]
  refine ⟨spectralNorm_nonneg _, ?_⟩
  rw [spectralNorm, ne_eq, eq_comm,
    spectralValue_eq_zero_iff (minpoly.monic hy_alg.isIntegral)]
  have h0 : coeff (minpoly K y) 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero hy_alg.isIntegral hy
  intro h
  have h0' : (minpoly K y).coeff 0 = 0 := by
    rw [h, coeff_X_pow,
      if_neg (ne_of_lt (minpoly.natDegree_pos hy_alg.isIntegral))]
  exact h0 h0'

/-- If `spectralNorm K L x = 0`, then `x = 0`. -/
theorem eq_zero_of_map_spectralNorm_eq_zero {x : L} (hx : spectralNorm K L x = 0)
  (hx_alg : IsAlgebraic K x) : x = 0 := by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h0 hx_alg)) hx

/-- If `f` is a power-multiplicative `K`-algebra norm on `L` with `f 1 ≤ 1`, then `f`
  is bounded above by `spectralNorm K L`. -/
theorem spectralNorm_ge_norm {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 ≤ 1) {x : L} (hx_alg : IsAlgebraic K x) :
    f x ≤ spectralNorm K L x := by
  apply root_norm_le_spectralValue hf_pm hf_na hf1 (minpoly.monic hx_alg.isIntegral)
  rw [minpoly.aeval]

/-- The `K`-algebra automorphisms of `L` are isometries with respect to the spectral norm. -/
theorem spectralNorm_aut_isom (σ : L ≃ₐ[K] L) (x : L) :
    spectralNorm K L x = spectralNorm K L (σ x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

-- We first assume that the extension is finite and normal
section Finite

section Normal

/--
If `L/K` is finite and normal, then `spectralNorm K L x = supr (λ (σ : L ≃ₐ[K] L), f (σ x))`. -/
theorem spectralNorm_max_of_fd_normal (h_fin : FiniteDimensional K L) (hn : Normal K L)
    {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : FunctionExtends (fun x : K ↦ ‖x‖₊) f) (x : L) :
    spectralNorm K L x = iSup fun σ : L ≃ₐ[K] L ↦ f (σ x) := by
  refine le_antisymm ?_ (ciSup_le fun σ ↦
    root_norm_le_spectralValue hf_pm hf_na (extends_is_norm_le_one_class hf_ext)
      (minpoly.monic (Normal.isIntegral hn x)) (minpoly.aeval_algHom _ σ.toAlgHom _))
  · set p := minpoly K x
    have hp_sp : Splits (algebraMap K L) (minpoly K x) := hn.splits x
    obtain ⟨s, hs⟩ := (splits_iff_exists_multiset _).mp hp_sp
    have : mapAlg K L p = map (algebraMap K L) p := rfl
    have h_lc : (algebraMap K L) (minpoly K x).leadingCoeff = 1 := by
      have h1 : (minpoly K x).leadingCoeff = 1 := by
        rw [← Monic]
        exact minpoly.monic (Normal.isIntegral hn x)
      rw [h1, map_one]
    rw [h_lc, map_one, one_mul] at hs
    simp only [spectralNorm]
    rw [← max_root_norm_eq_spectralValue' hf_pm hf_na (extends_is_norm_one_class hf_ext) _ _ hs]
    apply ciSup_le
    intro y
    split_ifs with h
    · have hy : ∃ σ : L ≃ₐ[K] L, σ x = y :=
        minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic x)
          (Polynomial.aeval_root s h hs)
      obtain ⟨σ, hσ⟩ := hy
      rw [← hσ]
      convert le_ciSup (Finite.bddAbove_range _) σ using 1
      · rfl
      · exact instNonemptyOfInhabited
      · exact SemilatticeSup.to_isDirected_le
      --exact le_ciSup (Fintype.bddAbove_range _) σ
    · exact Real.iSup_nonneg fun σ ↦ apply_nonneg _ _

/-- If `L/K` is finite and normal, then `spectralNorm K L = alg_norm_of_galois h_fin hna`. -/
theorem spectralNorm_eq_algNorm_of_galois (h_fin : FiniteDimensional K L) (hn : Normal K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : spectralNorm K L = algNorm_of_galois h_fin hna := by
  ext x
  set f := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
  have hf_pow : IsPowMul f :=
    (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).1
  have hf_ext : FunctionExtends _ f :=
    (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.1
  have hf_na : IsNonarchimedean f :=
    (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.2
  rw [spectralNorm_max_of_fd_normal h_fin hn hf_pow hf_na hf_ext]
  rfl

/-- If `L/K` is finite and normal, then `spectralNorm K L` is power-multiplicative. -/
theorem spectralNorm_isPowMul_of_fd_normal (h_fin : FiniteDimensional K L) (hn : Normal K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : IsPowMul (spectralNorm K L) := by
  rw [spectralNorm_eq_algNorm_of_galois h_fin hn hna]
  exact isPowMul_algNorm_of_galois h_fin hna

/-- The spectral norm is a `K`-algebra norm on `L` when `L/K` is finite and normal. -/
def spectralAlgNormOfFdNormal (h_fin : FiniteDimensional K L) (hn : Normal K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : AlgebraNorm K L where
  toFun     := spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_algNorm_of_galois h_fin hn hna]; exact map_zero _
  add_le'   := by rw [spectralNorm_eq_algNorm_of_galois h_fin hn hna]; exact map_add_le_add _
  neg'      := by rw [spectralNorm_eq_algNorm_of_galois h_fin hn hna]; exact map_neg_eq_map _
  mul_le'   :=  by
    simp only [spectralNorm_eq_algNorm_of_galois h_fin hn hna]
    exact map_mul_le_mul _
  smul'     := by
    simp only [spectralNorm_eq_algNorm_of_galois h_fin hn hna]
    exact AlgebraNormClass.map_smul_eq_mul _
  eq_zero_of_map_eq_zero' x := by
    simp only [spectralNorm_eq_algNorm_of_galois h_fin hn hna]
    exact eq_zero_of_map_eq_zero _

theorem spectralAlgNormOfFdNormal_def (h_fin : FiniteDimensional K L) (hn : Normal K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    spectralAlgNormOfFdNormal h_fin hn hna x = spectralNorm K L x := rfl

/-- The spectral norm is nonarchimedean when `L/K` is finite and normal. -/
theorem spectralNorm_isNonarchimedean_of_fd_normal (h_fin : FiniteDimensional K L) (hn : Normal K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : IsNonarchimedean (spectralNorm K L) := by
  rw [spectralNorm_eq_algNorm_of_galois  h_fin hn hna]
  exact isNonarchimedean_algNorm_of_galois h_fin hna

/-- The spectral norm extends the norm on `K` when `L/K` is finite and normal. -/
theorem spectralNorm_extends_norm_of_fd (h_fin : FiniteDimensional K L) (hn : Normal K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) :
    FunctionExtends (norm : K → ℝ) (spectralNorm K L) := by
  rw [spectralNorm_eq_algNorm_of_galois h_fin hn hna]
  exact algNorm_of_galois_extends h_fin hna

/-- If `L/K` is finite and normal, and `f` is a power-multiplicative `K`-algebra norm on `L`
  extending the norm on `K`, then `f = spectralNorm K L`. -/
theorem spectralNorm_unique_of_fd_normal (h_fin : FiniteDimensional K L) (hn : Normal K L)
    {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : FunctionExtends (fun x : K ↦ ‖x‖₊) f)
    (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x : L), f x = f (σ x)) (x : L) : f x = spectralNorm K L x := by
  have h_sup : (iSup fun σ : L ≃ₐ[K] L ↦ f (σ x)) = f x := by
    rw [← @ciSup_const _ (L ≃ₐ[K] L) _ _ (f x)]
    exact iSup_congr fun σ ↦ by rw [hf_iso σ x]
  rw [spectralNorm_max_of_fd_normal h_fin hn hf_pm hf_na hf_ext, h_sup]

end Normal

end Finite

-- Now we let L/K be any algebraic extension
/-- The spectral norm is a power-multiplicative K-algebra norm on L extending the norm on K. -/
theorem spectralValue.eq_normal' {E : IntermediateField K L} {x : L} (g : E)
    (h_map : algebraMap E L g = x) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
        (algebraMap E (normalClosure K E (AlgebraicClosure E)) g) =
      spectralNorm K L x := by
  rw [← h_map]
  exact spectralValue.eq_normal E g

open scoped IntermediateField

instance : SeminormClass (AlgebraNorm K ↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) K
  ↥(normalClosure K (↥E) (AlgebraicClosure ↥E)) := AlgebraNormClass.toSeminormClass

/-- The spectral norm extends the norm on `K`. -/
theorem spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖ := by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective]
  exact spectralValue_x_sub_c k

theorem spectralNorm_is_norm_le_one_class : spectralNorm K L 1 ≤ 1 := by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1, spectralNorm_extends, norm_one]

theorem spectralNorm_is_norm_one_class : spectralNorm K L 1 = 1 := by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1, spectralNorm_extends, norm_one]

/-- `spectralNorm K L (-y) = spectralNorm K L y` . -/
theorem spectralNorm_neg (hna : IsNonarchimedean (norm : K → ℝ)) {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (-y) = spectralNorm K L y := by
  set E := K⟮y⟯
  haveI : Normal K (AlgebraicClosure ↥E) :=
    IntermediateField.AdjoinSimple.normal_algebraicClosure hy
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  --have h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic E
  set g := IntermediateField.AdjoinSimple.gen K y
  have hy : -y = (algebraMap K⟮y⟯ L) (-g) := rfl
  rw [← spectralValue.eq_normal' g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hy, ←
    spectralValue.eq_normal' (-g) hy, RingHom.map_neg,
    ← spectralAlgNormOfFdNormal_def (normalClosure.is_finiteDimensional K K⟮y⟯
    (AlgebraicClosure K⟮y⟯)) (normalClosure.normal K K⟮y⟯ _) hna]
  exact map_neg_eq_map _ _

/-- The spectral norm is compatible with the action of `K`. -/
theorem spectralNorm_smul (hna : IsNonarchimedean (norm : K → ℝ)) (k : K) {y : L}
    (hy : IsAlgebraic K y) : spectralNorm K L (k • y) = ‖k‖₊ * spectralNorm K L y := by
  set E := K⟮y⟯
  haveI : Normal K (AlgebraicClosure ↥E) :=
    IntermediateField.AdjoinSimple.normal_algebraicClosure hy
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  --letI h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic E
  set g := IntermediateField.AdjoinSimple.gen K y
  have hgy : k • y = (algebraMap (↥K⟮y⟯) L) (k • g) := rfl
  have h : algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) (k • g) =
      k • algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) g := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_assoc]
  rw [← spectralValue.eq_normal' g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hgy,
    ← spectralValue.eq_normal' (k • g) rfl, h]
  rw [← spectralAlgNormOfFdNormal_def (normalClosure.is_finiteDimensional K K⟮y⟯
    (AlgebraicClosure K⟮y⟯)) (normalClosure.normal K E _) hna]
  apply map_smul_eq_mul

/-- The spectral norm is submultiplicative. -/
theorem spectralNorm_mul (hna : IsNonarchimedean (norm : K → ℝ)) {x y : L} (hx : IsAlgebraic K x)
    (hy : IsAlgebraic K y) :
    spectralNorm K L (x * y) ≤ spectralNorm K L x * spectralNorm K L y := by
  set E := K⟮x, y⟯
  haveI : Normal K (AlgebraicClosure ↥E) :=
    IntermediateField.AdjoinDouble.normal_algebraicClosure hx hy
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.AdjoinDouble.finiteDimensional hx.isIntegral hy.isIntegral
  --haveI h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic E
  set gx := IntermediateField.AdjoinDouble.gen₁ K x y
  set gy := IntermediateField.AdjoinDouble.gen₂ K x y
  have hxy : x * y = (algebraMap K⟮x, y⟯ L) (gx * gy) := rfl
  rw [hxy, ← spectralValue.eq_normal' (gx * gy) hxy,
    ← spectralValue.eq_normal' gx (IntermediateField.AdjoinDouble.algebraMap_gen₁ K x y),
    ← spectralValue.eq_normal' gy (IntermediateField.AdjoinDouble.algebraMap_gen₂ K x y), map_mul,
    ← spectralAlgNormOfFdNormal_def (normalClosure.is_finiteDimensional K K⟮x, y⟯
      (AlgebraicClosure K⟮x, y⟯)) (normalClosure.normal K K⟮x, y⟯ _) hna]
  exact map_mul_le_mul _ _ _

section IsAlgebraic

variable [h_alg : Algebra.IsAlgebraic K L]

/-- The spectral norm is power-multiplicative. -/
theorem spectralNorm_isPowMul (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (spectralNorm K L) := by
  intro x n hn
  set E := K⟮x⟯
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (h_alg.isAlgebraic x).isIntegral
  --haveI h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic E
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  haveI h_normal : Normal K (AlgebraicClosure ↥K⟮x⟯) :=
    IntermediateField.AdjoinSimple.normal_algebraicClosure (Algebra.IsAlgebraic.isAlgebraic x)
  rw [← spectralValue.eq_normal' _ (IntermediateField.AdjoinSimple.algebraMap_gen K x),
    ← spectralValue.eq_normal' (g ^ n) h_map, map_pow]
  --haveI h_alg := normalClosure.isAlgebraic K E
  rw [← hg]
  set g' := (algebraMap ↥K⟮x⟯ ↥(normalClosure K (↥K⟮x⟯) (AlgebraicClosure ↥K⟮x⟯))) g
  apply spectralNorm_isPowMul_of_fd_normal _ _ hna g' hn -- This solves the timeout
  · exact (normalClosure.is_finiteDimensional K E _)
  · exact (normalClosure.normal K E _)
  /- exact spectralNorm_isPowMul_of_fd_normal
    (normalClosure.is_finiteDimensional K E _) (normalClosure.normal K E _) hna _ n hn -/

/-- The spectral norm is nonarchimedean. -/
theorem spectralNorm_isNonarchimedean (h : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (spectralNorm K L) := by
  intro x y
  set E := K⟮x, y⟯
  haveI : Normal K (AlgebraicClosure ↥E) :=
    IntermediateField.AdjoinDouble.normal_algebraicClosure (Algebra.IsAlgebraic.isAlgebraic x)
      (Algebra.IsAlgebraic.isAlgebraic y)
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.AdjoinDouble.finiteDimensional (h_alg.isAlgebraic x).isIntegral
       (h_alg.isAlgebraic y).isIntegral
  --haveI h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic E
  set gx := IntermediateField.AdjoinDouble.gen₁ K x y
  set gy := IntermediateField.AdjoinDouble.gen₂ K x y
  have hxy : x + y = (algebraMap K⟮x, y⟯ L) (gx + gy) := rfl
  rw [hxy, ← spectralValue.eq_normal' (gx + gy) hxy,
    ← spectralValue.eq_normal' gx (IntermediateField.AdjoinDouble.algebraMap_gen₁ K x y),
    ← spectralValue.eq_normal' gy (IntermediateField.AdjoinDouble.algebraMap_gen₂ K x y),
    _root_.map_add]
  apply spectralNorm_isNonarchimedean_of_fd_normal _ _ h
  · exact normalClosure.is_finiteDimensional K K⟮x, y⟯ _
  · exact normalClosure.normal K K⟮x, y⟯ _

/-- The spectral norm is a `K`-algebra norm on `L`. -/
def spectralAlgNorm (hna : IsNonarchimedean (norm : K → ℝ)) :
    AlgebraNorm K L where
  toFun       := spectralNorm K L
  map_zero'   := spectralNorm_zero
  add_le' _ _ := IsNonarchimedean.add_le spectralNorm_nonneg (spectralNorm_isNonarchimedean hna)
  mul_le' x y := spectralNorm_mul hna (h_alg.isAlgebraic x) (h_alg.isAlgebraic y)
  smul' k x   := spectralNorm_smul hna k (h_alg.isAlgebraic x)
  neg' x      := spectralNorm_neg hna (h_alg.isAlgebraic x)
  eq_zero_of_map_eq_zero' x hx := eq_zero_of_map_spectralNorm_eq_zero hx (h_alg.isAlgebraic x)

theorem spectralAlgNorm_def (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    spectralAlgNorm hna x = spectralNorm K L x := rfl

theorem spectralAlgNorm_extends (k : K) (hna : IsNonarchimedean (norm : K → ℝ)) :
    spectralAlgNorm hna (algebraMap K L k) = ‖k‖ := spectralNorm_extends k

theorem spectralAlgNorm_is_norm_le_one_class (hna : IsNonarchimedean (norm : K → ℝ)) :
    spectralAlgNorm hna (1 : L) ≤ 1 := spectralNorm_is_norm_le_one_class

theorem spectralAlgNorm_is_norm_one_class (hna : IsNonarchimedean (norm : K → ℝ)) :
    spectralAlgNorm hna (1 : L) = 1 := spectralNorm_is_norm_one_class

theorem spectralAlgNorm_isPowMul (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (spectralAlgNorm (L := L) hna) := spectralNorm_isPowMul hna

end IsAlgebraic

/- /-- The restriction of a `K`-algebra norm on `L` to an intermediate field `K⟮x⟯`. -/
def Adjoin.algebraNorm (f : AlgebraNorm K L) (x : L) : AlgebraNorm K K⟮x⟯ where
  toFun := f ∘ algebraMap (↥K⟮x⟯) L
  map_zero' := by simp only [Function.comp_apply, IntermediateField.algebraMap_apply,
    ZeroMemClass.coe_zero, _root_.map_zero]
  add_le' a b := by simp only [Function.comp_apply, _root_.map_add, map_add_le_add]
  mul_le' a b := by simp only [Function.comp_apply, IntermediateField.algebraMap_apply,
    MulMemClass.coe_mul, map_mul_le_mul]
  smul' r a := by
    simp only [Function.comp_apply, Algebra.smul_def]
    rw [map_mul, ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq, ← Algebra.smul_def,
      map_smul_eq_mul _ _]
  neg' a := by
    have : AddMonoidHomClass (K⟮x⟯ →+* L) (K⟮x⟯) L := RingHomClass.toAddMonoidHomClass
    simp only [Function.comp_apply, map_neg, map_neg_eq_map]
  eq_zero_of_map_eq_zero' a ha := by
    simp only [Function.comp_apply, IntermediateField.algebraMap_apply, map_eq_zero_iff_eq_zero,
      ZeroMemClass.coe_eq_zero] at ha
    exact ha -/

end spectralNorm

section SpectralValuation

variable {K : Type*} [NormedField K] [CompleteSpace K] {L : Type*} [hL : Field L] [Algebra K L]

-- Theorem 3.2.4/2
section

/-- The `normed_ring` stucture on a ring `A` determined by a `ring_norm`. -/
def normToNormedRing {A : Type*} [Ring A] (f : RingNorm A) : NormedRing A where
  norm x := f x
  dist x y := f (x - y)
  dist_self x := by simp only [sub_self, AddGroupSeminorm.toFun_eq_coe, _root_.map_zero]
  dist_comm x y := by
    simp only [dist, AddGroupSeminorm.toFun_eq_coe]
    rw [← neg_sub x y, map_neg_eq_map]
  dist_triangle x y z := by
    have hxyz : x - z = x - y + (y - z) := by abel
    simp only [AddGroupSeminorm.toFun_eq_coe, hxyz, map_add_le_add]
  dist_eq x y := rfl
  norm_mul_le x y := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe, map_mul_le_mul]
  edist_dist x y := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe]
    rw [eq_comm, ENNReal.ofReal_eq_coe_nnreal]
  eq_of_dist_eq_zero hxy := by
    simp only [dist, AddGroupSeminorm.toFun_eq_coe] at hxy
    exact eq_of_sub_eq_zero (RingNorm.eq_zero_of_map_eq_zero' _ _ hxy)

end

end SpectralValuation

#exit

-- We are not using these

/-- The `normed_field` stucture on a field `L` determined by a `mul_ring_norm`. -/
def mulNormToNormedField (f : AbsoluteValue L ℝ) : NormedField L where
  norm x := f x
  dist x y := f (x - y)
  dist_self x := by simp only [sub_self, AddGroupSeminorm.toFun_eq_coe, _root_.map_zero]
  dist_comm x y := by
    simp only [dist, AddGroupSeminorm.toFun_eq_coe]
    rw [← neg_sub x y, map_neg_eq_map]
  dist_triangle x y z := by
    have hxyz : x - z = x - y + (y - z) := by ring
    simp only [AddGroupSeminorm.toFun_eq_coe, hxyz, map_add_le_add]
  eq_of_dist_eq_zero hxy := (AbsoluteValue.map_sub_eq_zero_iff f _ _).mp hxy
  dist_eq x y := rfl
  norm_mul x y := by simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
    map_mul]
  edist_dist x y := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe]
    rw [eq_comm, ENNReal.ofReal_eq_coe_nnreal]

theorem mulNormToNormedField.norm (f : AbsoluteValue L ℝ) :
    (mulNormToNormedField f).norm = fun x ↦ (f x : ℝ) := rfl
