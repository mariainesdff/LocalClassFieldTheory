/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import RingTheory.Polynomial.Vieta
import FromMathlib.Minpoly
import FromMathlib.NormalClosure
import FromMathlib.AlgNormOfGalois

#align_import from_mathlib.spectral_norm

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

* `spectral_value` : the spectral value of a polynomial in `R[X]`. 
* `spectral_norm` :The spectral norm `|y|_sp` is the spectral value of the minimal of `y` over `K`.
* `spectral_alg_norm` : the spectral norm is a `K`-algebra norm on `L`.

## Main Results

* `spectral_norm_ge_norm` : if `f` is a power-multiplicative `K`-algebra norm on `L` with `f 1 ≤ 1`,
  then `f` is bounded above by `spectral_norm K L`. 
* `spectral_norm_aut_isom` : the `K`-algebra automorphisms of `L` are isometries with respect to 
  the spectral norm.
* `spectral_norm_max_of_fd_normal` : iff `L/K` is finite and normal, then 
  `spectral_norm K L x = supr (λ (σ : L ≃ₐ[K] L), f (σ x))`. 
* `spectral_norm_is_pow_mul` : the spectral norm is power-multiplicative.
* `spectral_norm_is_nonarchimedean` : the spectral norm is nonarchimedean. 
* `spectral_norm_extends` : the spectral norm extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, spectral value, seminorm, norm, nonarchimedean
-/


noncomputable section

open Polynomial Multiset

open scoped Polynomial

-- Auxiliary lemmas
section AuxLemmas

namespace List

variable {α : Type _} [LinearOrder α]

theorem max_repeat {n : ℕ} (a : α) : foldr max a (repeat a n) = a :=
  by
  induction' n with n hn
  · simp only [List.repeat, List.foldr_nil]
  · simp only [foldr, repeat, foldr_cons, max_eq_left_iff]
    exact le_of_eq hn

theorem le_max_of_exists_le {l : List α} {a x : α} (b : α) (hx : x ∈ l) (h : a ≤ x) :
    a ≤ l.foldr max b := by
  induction' l with y l IH
  · exact absurd hx (List.not_mem_nil _)
  · obtain rfl | hl := hx
    simp only [List.foldr, List.foldr_cons]
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

end List

namespace Polynomial

variable {K : Type _} [NormedField K] {L : Type _} [Field L] [Algebra K L]

theorem natDegree_pos_of_monic_of_root {p : K[X]} (hp : p.Monic) {x : L} (hx : aeval x p = 0) :
    0 < p.natDegree :=
  natDegree_pos_of_aeval_root (ne_zero_of_ne_zero_of_monic one_ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap K L)).mp (algebraMap K L).Injective)

theorem monic_of_prod (p : K[X]) {n : ℕ} (b : Fin n → L)
    (hp : mapAlg K L p = finprod fun k : Fin n => X - C (b k)) : p.Monic :=
  by
  have hprod : (finprod fun k : Fin n => X - C (b k)).Monic :=
    by
    rw [finprod_eq_prod_of_fintype]
    exact monic_prod_of_monic _ _ fun m hm => monic_X_sub_C (b m)
  rw [← hp, map_alg_eq_map] at hprod 
  exact monic_of_injective (algebraMap K L).Injective hprod

theorem monic_of_prod' (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (Multiset.map (fun a : L => X - C a) s).Prod) : p.Monic :=
  by
  have hprod : (Multiset.map (fun a : L => X - C a) s).Prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun m hm => monic_X_sub_C m
  rw [← hp, map_alg_eq_map] at hprod 
  exact monic_of_injective (algebraMap K L).Injective hprod

theorem c_finset_add {α : Type _} (s : Finset α) {K : Type _} [Semiring K] (b : α → K) :
    (s.Sum fun x : α => C (b x)) = C (s.Sum b) := by
  classical
  apply s.induction_on
  · simp only [Finset.sum_empty, _root_.map_zero]
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hs, C_add]

theorem c_finset_prod {α : Type _} (s : Finset α) {K : Type _} [CommRing K] (b : α → K) :
    (s.Prod fun x : α => C (b x)) = C (s.Prod b) := by
  classical
  apply s.induction_on
  · simp only [Finset.prod_empty, map_one]
  · intro a s ha hs
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hs, C_mul]

theorem prod_x_add_c_natDegree {L : Type _} [Field L] {n : ℕ} (b : Fin n → L) :
    (Finset.univ.Prod fun i : Fin n => X - C (b i)).natDegree = n :=
  by
  rw [nat_degree_prod _ _ fun m hm => X_sub_C_ne_zero (b m)]
  simp only [nat_degree_X_sub_C, Finset.sum_const, Finset.card_fin, Algebra.id.smul_eq_mul, mul_one]

theorem aeval_root (s : Multiset L) {x : L} (hx : x ∈ s) {p : K[X]}
    (hp : mapAlg K L p = (Multiset.map (fun a : L => X - C a) s).Prod) : aeval x p = 0 :=
  by
  have : aeval x (map_alg K L p) = aeval x p := by rw [map_alg_eq_map, aeval_map_algebra_map]
  rw [← this, hp, coe_aeval_eq_eval]
  have hy : X - C x ∣ (Multiset.map (fun a : L => X - C a) s).Prod :=
    by
    apply Multiset.dvd_prod
    simp only [Multiset.mem_map, sub_right_inj, C_inj, exists_eq_right]
    exact hx
  rw [eval_eq_zero_of_dvd_of_eval_eq_zero hy]
  simp only [eval_sub, eval_X, eval_C, sub_self]

end Polynomial

namespace Real

theorem multiset_prod_le_pow_card {K L : Type _} [SeminormedCommRing K] [Ring L] [Algebra K L]
    {t : Multiset L} {f : AlgebraNorm K L} {y : L} (hf : ∀ x : ℝ, x ∈ Multiset.map f t → x ≤ f y) :
    (map f t).Prod ≤ f y ^ card (map f t) :=
  by
  set g : L → NNReal := fun x : L => ⟨f x, map_nonneg _ _⟩
  have hg_le : (map g t).Prod ≤ g y ^ card (map g t) :=
    by
    apply prod_le_pow_card
    intro x hx
    obtain ⟨a, hat, hag⟩ := mem_map.mp hx
    rw [Subtype.ext_iff, Subtype.coe_mk] at hag 
    rw [← NNReal.coe_le_coe, Subtype.coe_mk]
    exact hf (x : ℝ) (mem_map.mpr ⟨a, hat, hag⟩)
  rw [← NNReal.coe_le_coe] at hg_le 
  convert hg_le
  · simp only [NNReal.coe_multiset_prod, Multiset.map_map, Function.comp_apply, Subtype.coe_mk]
  · simp only [card_map]

theorem multiset_le_prod_of_submultiplicative {α : Type _} [CommMonoid α] {f : α → ℝ}
    (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) : f s.Prod ≤ (s.map f).Prod :=
  by
  set g : α → NNReal := fun x : α => ⟨f x, h_nonneg _⟩
  have hg_le : g s.prod ≤ (s.map g).Prod :=
    by
    apply Multiset.le_prod_of_submultiplicative
    · ext; rw [Subtype.coe_mk, Nonneg.coe_one, h_one]
    · intro a b
      simp only [← NNReal.coe_le_coe, Subtype.coe_mk, Nonneg.mk_mul_mk]
      exact h_mul _ _
  rw [← NNReal.coe_le_coe] at hg_le 
  convert hg_le
  simp only [NNReal.coe_multiset_prod, Multiset.map_map, Function.comp_apply, Subtype.coe_mk]

end Real

namespace Multiset

section Decidable

variable {α : Type _} [DecidableEq α]

theorem max (f : α → ℝ) {s : Multiset α} (hs : s.toFinset.Nonempty) :
    ∃ y : α, y ∈ s ∧ ∀ z : α, z ∈ s → f z ≤ f y :=
  by
  have hsf : (map f s).toFinset.Nonempty :=
    by
    obtain ⟨x, hx⟩ := hs.bex
    exact ⟨f x, mem_to_finset.mpr (mem_map.mpr ⟨x, mem_to_finset.mp hx, rfl⟩)⟩
  have h := (s.map f).toFinset.max'_mem hsf
  rw [mem_to_finset, mem_map] at h 
  obtain ⟨y, hys, hymax⟩ := h
  use y, hys
  intro z hz
  rw [hymax]
  exact Finset.le_max' _ _ (mem_to_finset.mpr (mem_map.mpr ⟨z, hz, rfl⟩))

theorem card_toFinset_pos {m : Multiset α} (hm : 0 < m.card) : 0 < m.toFinset.card :=
  by
  obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp hm
  exact finset.card_pos.mpr ⟨x, mem_to_finset.mpr hx⟩

end Decidable

@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred' {α β : Type _} [CommMonoid α] [OrderedCommRing β]
    (f : α → β) (p : α → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.Prod ≤ (s.map f).Prod :=
  by
  revert s
  refine' Multiset.induction _ _
  · simp [le_of_eq h_one]
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx => hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  refine' (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans _
  exact mul_le_mul_of_nonneg_left (hs hps) (h_nonneg _)

@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative' {α β : Type _} [CommMonoid α] [OrderedCommRing β] (f : α → β)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) : f s.Prod ≤ (s.map f).Prod :=
  le_prod_of_submultiplicative_on_pred' f (fun i => True) h_nonneg h_one trivial
    (fun x y _ _ => h_mul x y) (by simp) s (by simp)

end Multiset

namespace Finset

theorem powersetLen_nonempty' {α : Type _} {n : ℕ} {s : Finset α} (h : n ≤ s.card) :
    (Finset.powersetLen n s).Nonempty := by
  classical
  induction' s using Finset.induction_on with x s hx IH generalizing n
  · rw [Finset.card_empty, le_zero_iff] at h 
    rw [h, Finset.powersetLen_zero]
    exact Finset.singleton_nonempty _
  · cases n
    · simp
    · rw [Finset.card_insert_of_not_mem hx, Nat.succ_le_succ_iff] at h 
      rw [Finset.powersetLen_succ_insert hx]
      refine' Finset.Nonempty.mono _ ((IH h).image (insert x))
      convert Finset.subset_union_right _ _

theorem le_prod_of_submultiplicative' {ι M N : Type _} [CommMonoid M] [OrderedCommRing N]
    (f : M → N) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1)
    (h_mul : ∀ x y : M, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (s.Prod fun i : ι => g i) ≤ s.Prod fun i : ι => f (g i) :=
  by
  refine' le_trans (Multiset.le_prod_of_submultiplicative' f h_nonneg h_one h_mul _) _
  rw [Multiset.map_map]
  rfl

end Finset

section IsNonarchimedean

variable {K L : Type _} [NormedCommRing K] [CommRing L] [Algebra K L]

theorem isNonarchimedean_finset_powerset_image_add {f : AlgebraNorm K L}
    (hf_na : IsNonarchimedean f) {n : ℕ} (b : Fin n → L) (m : ℕ) :
    ∃ s : Finset.powersetLen (Fintype.card (Fin n) - m) (@Finset.univ (Fin n) _),
      f
          ((Finset.powersetLen (Fintype.card (Fin n) - m) Finset.univ).Sum fun t : Finset (Fin n) =>
            t.Prod fun i : Fin n => -b i) ≤
        f (s.val.Prod fun i : Fin n => -b i) :=
  by
  set g := fun t : Finset (Fin n) => t.Prod fun i : Fin n => -b i with hg
  obtain ⟨b, hb_in, hb⟩ :=
    isNonarchimedean_finset_image_add hf_na g
      (Finset.powersetLen (Fintype.card (Fin n) - m) Finset.univ)
  have hb_ne :
    (Finset.powersetLen (Fintype.card (Fin n) - m) (Finset.univ : Finset (Fin n))).Nonempty :=
    by
    rw [Fintype.card_fin]
    have hmn : n - m ≤ (Finset.univ : Finset (Fin n)).card :=
      by
      rw [Finset.card_fin]
      exact Nat.sub_le n m
    exact Finset.powersetLen_nonempty' hmn
  use⟨b, hb_in hb_ne⟩, hb

theorem isNonarchimedean_multiset_powerset_image_add {f : AlgebraNorm K L}
    (hf_na : IsNonarchimedean f) (s : Multiset L) (m : ℕ) :
    ∃ t : Multiset L,
      t.card = s.card - m ∧
        (∀ x : L, x ∈ t → x ∈ s) ∧
          f (map Multiset.prod (powersetLen (s.card - m) s)).Sum ≤ f t.Prod :=
  by
  set g := fun t : Multiset L => t.Prod with hg
  obtain ⟨b, hb_in, hb_le⟩ :=
    isNonarchimedean_multiset_image_add hf_na g (powerset_len (s.card - m) s)
  have hb : b ≤ s ∧ b.card = s.card - m :=
    by
    rw [← Multiset.mem_powersetLen]
    apply hb_in
    rw [card_powerset_len]
    exact Nat.choose_pos (s.card.sub_le m)
  refine' ⟨b, hb.2, fun x hx => Multiset.mem_of_le hb.left hx, hb_le⟩

end IsNonarchimedean

namespace IntermediateField

variable {K L : Type _} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)

-- Auxiliary instances to avoid timeouts.
instance aux : IsScalarTower K E E :=
  inferInstance

instance aux' : IsScalarTower K E (AlgebraicClosureAux E) :=
  @AlgebraicClosureAux.isScalarTower E _ K E _ _ _ _ _ (IntermediateField.aux E)

instance : IsScalarTower K E (normalClosure K (↥E) (AlgebraicClosureAux ↥E)) :=
  inferInstance

instance : Normal K (AlgebraicClosureAux K) :=
  normal_iff.mpr fun x =>
    ⟨isAlgebraic_iff_isIntegral.mp (AlgebraicClosure.isAlgebraic K x),
      IsAlgClosed.splits_codomain (minpoly K x)⟩

theorem isAlgebraic (h_alg_L : Algebra.IsAlgebraic K L) (E : IntermediateField K L) :
    Algebra.IsAlgebraic K E := fun y =>
  by
  obtain ⟨p, hp0, hp⟩ := h_alg_L ↑y
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at hp 
  exact ⟨p, hp0, hp⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem AdjoinSimple.alg_closure_normal (h_alg : Algebra.IsAlgebraic K L) (x : L) :
    Normal K (AlgebraicClosureAux K⟮⟯) :=
  normal_iff.mpr fun y =>
    ⟨isAlgebraic_iff_isIntegral.mp
        (Algebra.isAlgebraic_trans (isAlgebraic h_alg K⟮⟯) (AlgebraicClosure.isAlgebraic K⟮⟯) y),
      IsAlgClosed.splits_codomain (minpoly K y)⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem AdjoinDouble.alg_closure_normal (h_alg : Algebra.IsAlgebraic K L) (x y : L) :
    Normal K (AlgebraicClosureAux K⟮⟯) :=
  normal_iff.mpr fun z =>
    ⟨isAlgebraic_iff_isIntegral.mp
        (Algebra.isAlgebraic_trans (isAlgebraic h_alg K⟮⟯) (AlgebraicClosure.isAlgebraic K⟮⟯) z),
      IsAlgClosed.splits_codomain (minpoly K z)⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem AdjoinAdjoin.finiteDimensional {x y : L} (hx : IsIntegral K x) (hy : IsIntegral K y) :
    FiniteDimensional K K⟮⟯ :=
  by
  haveI hx_fd : FiniteDimensional K K⟮⟯ := adjoin.finite_dimensional hx
  have hy' : IsIntegral K⟮⟯ y := isIntegral_of_isScalarTower hy
  haveI hy_fd : FiniteDimensional K⟮⟯ K⟮⟯⟮⟯ := adjoin.finite_dimensional hy'
  rw [← adjoin_simple_adjoin_simple]
  apply FiniteDimensional.trans K K⟮⟯ K⟮⟯⟮⟯

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem mem_adjoin_adjoin_left (F : Type u_1) [Field F] {E : Type u_2} [Field E] [Algebra F E]
    (x y : E) : x ∈ F⟮⟯ :=
  by
  rw [← adjoin_simple_adjoin_simple, adjoin_simple_comm]
  exact subset_adjoin F⟮⟯ {x} (Set.mem_singleton x)

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem mem_adjoin_adjoin_right (F : Type u_1) [Field F] {E : Type u_2} [Field E] [Algebra F E]
    (x y : E) : y ∈ F⟮⟯ := by
  rw [← adjoin_simple_adjoin_simple] <;> exact subset_adjoin F⟮⟯ {y} (Set.mem_singleton y)

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The first generator of an intermediate field of the form `F⟮x, y⟯`. -/
def AdjoinAdjoin.gen1 (F : Type u_1) [Field F] {E : Type u_2} [Field E] [Algebra F E] (x y : E) :
    F⟮⟯ :=
  ⟨x, mem_adjoin_adjoin_left F x y⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The second generator of an intermediate field of the form `F⟮x, y⟯`. -/
def AdjoinAdjoin.gen2 (F : Type u_1) [Field F] {E : Type u_2} [Field E] [Algebra F E] (x y : E) :
    F⟮⟯ :=
  ⟨y, mem_adjoin_adjoin_right F x y⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
@[simp]
theorem AdjoinAdjoin.algebraMap_gen1 (F : Type u_1) [Field F] {E : Type u_2} [Field E] [Algebra F E]
    (x y : E) : (algebraMap (↥F⟮⟯) E) (IntermediateField.AdjoinAdjoin.gen1 F x y) = x :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
@[simp]
theorem AdjoinAdjoin.algebraMap_gen2 (F : Type u_1) [Field F] {E : Type u_2} [Field E] [Algebra F E]
    (x y : E) : (algebraMap (↥F⟮⟯) E) (IntermediateField.AdjoinAdjoin.gen2 F x y) = y :=
  rfl

end IntermediateField

section

variable {K L : Type _} [NormedField K] [Ring L] [Algebra K L]

theorem extends_is_norm_le_one_class {f : L → ℝ} (hf_ext : FunctionExtends (norm : K → ℝ) f) :
    f 1 ≤ 1 := by rw [← (algebraMap K L).map_one, hf_ext, norm_one]

theorem extends_is_norm_one_class {f : L → ℝ} (hf_ext : FunctionExtends (norm : K → ℝ) f) :
    f 1 = 1 := by rw [← (algebraMap K L).map_one, hf_ext, norm_one]

end

end AuxLemmas

variable {R : Type _}

section spectralValue

section Seminormed

variable [SeminormedRing R]

/-- The function `ℕ → ℝ` sending `n` to `‖ p.coeff n ‖^(1/(p.nat_degree - n : ℝ))`, if 
  `n < p.nat_degree`, or to `0` otherwise. -/
def spectralValueTerms (p : R[X]) : ℕ → ℝ := fun n : ℕ =>
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) else 0

theorem spectralValueTerms_of_lt_natDegree (p : R[X]) {n : ℕ} (hn : n < p.natDegree) :
    spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) := by
  simp only [spectralValueTerms, if_pos hn]

theorem spectralValueTerms_of_natDegree_le (p : R[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    spectralValueTerms p n = 0 := by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

/-- The spectral value of a polynomial in `R[X]`. -/
def spectralValue (p : R[X]) : ℝ :=
  iSup (spectralValueTerms p)

/-- The sequence `spectral_value_terms p` is bounded above. -/
theorem spectralValueTerms_bddAbove (p : R[X]) : BddAbove (Set.range (spectralValueTerms p)) :=
  by
  use List.foldr max 0
      (List.map (fun n => ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ))) (List.range p.nat_degree))
  · rw [mem_upperBounds]
    intro r hr
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr
    simp only [spectralValueTerms] at hn 
    split_ifs at hn  with hd hd
    · have h :
        ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ)) ∈
          List.map (fun n : ℕ => ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ)))
            (List.range p.nat_degree) :=
        by
        simp only [List.mem_map, List.mem_range]
        exact ⟨n, hd, rfl⟩
      exact List.le_max_of_exists_le 0 h (ge_of_eq hn)
    · rw [← hn]
      by_cases hd0 : p.nat_degree = 0
      · rw [hd0, List.range_zero, List.map_nil, List.foldr_nil]
      · have h :
          ‖p.coeff 0‖ ^ (1 / (p.nat_degree - 0 : ℝ)) ∈
            List.map (fun n : ℕ => ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ)))
              (List.range p.nat_degree) :=
          by
          simp only [List.mem_map, List.mem_range]
          exact ⟨0, Nat.pos_of_ne_zero hd0, by rw [Nat.cast_zero]⟩
        refine' List.le_max_of_exists_le 0 h _
        exact Real.rpow_nonneg_of_nonneg (norm_nonneg _) _

/-- The range of `spectral_value_terms p` is a finite set. -/
theorem spectralValueTerms_finite_range (p : R[X]) : (Set.range (spectralValueTerms p)).Finite :=
  haveI h_ss :
    Set.range (spectralValueTerms p) ⊆
      (Set.range fun n : Fin p.nat_degree => ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ))) ∪
        {(0 : ℝ)} :=
    by
    intro x hx
    obtain ⟨m, hm⟩ := set.mem_range.mpr hx
    by_cases hm_lt : m < p.nat_degree
    · simp only [spectralValueTerms_of_lt_natDegree p hm_lt] at hm 
      rw [← hm]
      exact Set.mem_union_left _ ⟨⟨m, hm_lt⟩, rfl⟩
    · simp only [spectralValueTerms_of_natDegree_le p (le_of_not_lt hm_lt)] at hm 
      rw [hm]
      exact Set.mem_union_right _ (Set.mem_singleton _)
  Set.Finite.subset (Set.Finite.union (Set.finite_range _) (Set.finite_singleton _)) h_ss

/-- The sequence `spectral_value_terms p` is nonnegative. -/
theorem spectralValueTerms_nonneg (p : R[X]) (n : ℕ) : 0 ≤ spectralValueTerms p n :=
  by
  simp only [spectralValueTerms]
  split_ifs with h
  · exact Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
  · exact le_refl _

/-- The spectral value of a polyomial is nonnegative. -/
theorem spectralValue_nonneg (p : R[X]) : 0 ≤ spectralValue p :=
  Real.iSup_nonneg (spectralValueTerms_nonneg p)

variable [Nontrivial R]

/-- The polynomial `X - r` has spectral value `‖ r ‖`. -/
theorem spectralValue_x_sub_c (r : R) : spectralValue (X - C r) = ‖r‖ :=
  by
  rw [spectralValue]; rw [spectralValueTerms]
  simp only [nat_degree_X_sub_C, Nat.lt_one_iff, coeff_sub, Nat.cast_one, one_div]
  suffices (⨆ n : ℕ, ite (n = 0) ‖r‖ 0) = ‖r‖
    by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    ·
      rw [if_pos hn, if_pos hn, hn, Nat.cast_zero, sub_zero, coeff_X_zero, coeff_C_zero, zero_sub,
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
theorem spectralValue_x_pow (n : ℕ) : spectralValue (X ^ n : R[X]) = 0 :=
  by
  rw [spectralValue]; rw [spectralValueTerms]
  simp_rw [coeff_X_pow n, nat_degree_X_pow]
  convert ciSup_const
  ext m
  by_cases hmn : m < n
  · rw [if_pos hmn, Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (ne_of_lt hmn),
      norm_zero, one_div, Ne.def, inv_eq_zero, ← Nat.cast_sub (le_of_lt hmn), Nat.cast_eq_zero,
      Nat.sub_eq_zero_iff_le]
    exact ⟨Eq.refl _, not_le_of_lt hmn⟩
  · rw [if_neg hmn]
  infer_instance

end Seminormed

section Normed

variable [NormedRing R]

/-- The spectral value of `p` equals zero if and only if `p` is of the form `X^n`. -/
theorem spectralValue_eq_zero_iff [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    spectralValue p = 0 ↔ p = X ^ p.natDegree :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [spectralValue] at h 
    ext
    rw [coeff_X_pow]
    by_cases hn : n = p.nat_degree
    · rw [if_pos hn, hn, coeff_nat_degree]; exact hp
    · rw [if_neg hn]
      · by_cases hn' : n < p.nat_degree
        · have h_le : iSup (spectralValueTerms p) ≤ 0 := le_of_eq h
          have h_exp : 0 < 1 / ((p.nat_degree : ℝ) - n) :=
            by
            rw [one_div_pos, ← Nat.cast_sub (le_of_lt hn'), Nat.cast_pos]
            exact Nat.sub_pos_of_lt hn'
          have h0 : (0 : ℝ) = 0 ^ (1 / ((p.nat_degree : ℝ) - n)) := by
            rw [Real.zero_rpow (ne_of_gt h_exp)]
          rw [iSup, csSup_le_iff (spectralValueTerms_bddAbove p) (Set.range_nonempty _)] at h_le 
          specialize h_le (spectralValueTerms p n) ⟨n, rfl⟩
          simp only [spectralValueTerms, if_pos hn'] at h_le 
          rw [h0, Real.rpow_le_rpow_iff (norm_nonneg _) (le_refl _) h_exp] at h_le 
          exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _))
        · exact coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn))
  · convert spectralValue_x_pow p.nat_degree
    infer_instance

end Normed

end spectralValue

-- In this section we prove Proposition 3.1.2/1 from BGR.
section BddBySpectralValue

variable {K : Type _} [NormedField K] {L : Type _} [Field L] [Algebra K L]

/-- Part (1): the norm of any root of p is bounded by the spectral value of p. -/
theorem root_norm_le_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 ≤ 1) {p : K[X]} (hp : p.Monic) {x : L}
    (hx : aeval x p = 0) : f x ≤ spectralValue p :=
  by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra' h_ge
    have hn_lt : ∀ (n : ℕ) (hn : n < p.nat_degree), ‖p.coeff n‖ < f x ^ (p.nat_degree - n) :=
      by
      intro n hn
      have hexp : (‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ))) ^ (p.nat_degree - n) = ‖p.coeff n‖ :=
        by
        rw [← Real.rpow_nat_cast, ← Real.rpow_mul (norm_nonneg _), mul_comm,
          Real.rpow_mul (norm_nonneg _), Real.rpow_nat_cast, ← Nat.cast_sub (le_of_lt hn), one_div,
          Real.pow_nat_rpow_nat_inv (norm_nonneg _) (ne_of_gt (tsub_pos_of_lt hn))]
      have h_base : ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ)) < f x :=
        by
        rw [spectralValue, iSup,
          Set.Finite.cSup_lt_iff (spectralValueTerms_finite_range p)
            (Set.range_nonempty (spectralValueTerms p))] at
          h_ge 
        have h_rg : ‖p.coeff n‖ ^ (1 / (p.nat_degree - n : ℝ)) ∈ Set.range (spectralValueTerms p) :=
          by use n; simp only [spectralValueTerms, if_pos hn]
        exact h_ge (‖p.coeff n‖₊ ^ (1 / (↑p.nat_degree - ↑n))) h_rg
      rw [← hexp, ← Real.rpow_nat_cast, ← Real.rpow_nat_cast]
      exact
        Real.rpow_lt_rpow (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _) h_base
          (nat.cast_pos.mpr (tsub_pos_of_lt hn))
    have h_deg : 0 < p.nat_degree := Polynomial.natDegree_pos_of_monic_of_root hp hx
    have : ‖(1 : K)‖ = 1 := norm_one
    have h_lt :
      f ((Finset.range p.nat_degree).Sum fun i : ℕ => p.coeff i • x ^ i) < f (x ^ p.nat_degree) :=
      by
      have hn' : ∀ (n : ℕ) (hn : n < p.nat_degree), f (p.coeff n • x ^ n) < f (x ^ p.nat_degree) :=
        by
        intro n hn
        by_cases hn0 : n = 0
        · rw [hn0, pow_zero, map_smul_eq_mul, hf_pm _ (nat.succ_le_iff.mpr h_deg), ←
            Nat.sub_zero p.nat_degree, ← hn0]
          exact mul_lt_of_lt_of_le_one_of_nonneg (hn_lt n hn) hf1 (norm_nonneg _)
        · have : p.nat_degree = p.nat_degree - n + n := by rw [Nat.sub_add_cancel (le_of_lt hn)]
          rw [map_smul_eq_mul, hf_pm _ (nat.succ_le_iff.mp (pos_iff_ne_zero.mpr hn0)),
            hf_pm _ (nat.succ_le_iff.mpr h_deg), this, pow_add]
          exact
            (mul_lt_mul_right (pow_pos (lt_of_le_of_ne (map_nonneg _ _) (Ne.symm hx0)) _)).mpr
              (hn_lt n hn)
      obtain ⟨m, hm_in, hm⟩ :=
        isNonarchimedean_finset_range_add_le hf_na p.nat_degree fun i : ℕ => p.coeff i • x ^ i
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg))
    have h0 : f 0 ≠ 0 :=
      by
      have h_eq : f 0 = f (x ^ p.nat_degree) :=
        by
        rw [← hx, aeval_eq_sum_range, Finset.sum_range_succ, add_comm, hp.coeff_nat_degree,
          one_smul, ← max_eq_left_of_lt h_lt]
        exact isNonarchimedean_add_eq_max_of_ne hf_na (ne_of_lt h_lt)
      rw [h_eq]
      exact ne_of_gt (lt_of_le_of_lt (map_nonneg _ _) h_lt)
    exact h0 (map_zero _)

open scoped Classical

open Multiset

/-- Part (2): if p splits into linear factors over B, then its spectral value equals the maximum
  of the norms of its roots. -/
theorem max_root_norm_eq_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) {n : ℕ} (hn : 0 < n) (b : Fin n → L)
    (hp : mapAlg K L p = finprod fun k : Fin n => X - C (b k)) : iSup (f ∘ b) = spectralValue p :=
  by
  apply le_antisymm
  · haveI : Nonempty (Fin n) := fin.pos_iff_nonempty.mp hn
    apply ciSup_le
    rintro m
    have hm : aeval (b m) p = 0 :=
      by
      have hm' : aeval (b m) ((map_alg K L) p) = 0 :=
        by
        have hd1 : (aeval (b m)) (X - C (b m)) = 0 := by
          rw [coe_aeval_eq_eval, eval_sub, eval_X, eval_C, sub_self]
        rw [hp, finprod_eq_prod_of_fintype, aeval_def, eval₂_finset_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ m) hd1
      rw [map_alg_eq_map, aeval_map_algebra_map] at hm' 
      exact hm'
    rw [Function.comp_apply]
    exact root_norm_le_spectralValue hf_pm hf_na (le_of_eq hf1) (p.monic_of_prod b hp) hm
  · haveI : Nonempty (Fin n) := fin.pos_iff_nonempty.mp hn
    have h_supr : 0 ≤ iSup (f ∘ b) := Real.iSup_nonneg fun x => map_nonneg f (b x)
    apply ciSup_le
    intro m
    by_cases hm : m < p.nat_degree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.nat_degree - m : ℝ) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _) h_supr h, ←
        Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (ne_of_gt h), Real.rpow_one, ←
        Nat.cast_sub (le_of_lt hm), Real.rpow_nat_cast]
      have hpn : n = p.nat_degree := by
        rw [← nat_degree_map (algebraMap K L), ← map_alg_eq_map, hp, finprod_eq_prod_of_fintype,
          Polynomial.prod_x_add_c_natDegree]
      have hc : ‖p.coeff m‖ = f (((map_alg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1, map_alg_eq_map, coeff_map]
      rw [hc, hp, finprod_eq_prod_of_fintype]
      simp_rw [sub_eq_add_neg, ← C_neg, Finset.prod_eq_multiset_prod, ← Pi.neg_apply, ←
        map_map (fun x : L => X + C x) (-b)]
      have hm_le' : m ≤ card (map (-b) finset.univ.val) :=
        by
        have : card finset.univ.val = Finset.card Finset.univ := rfl
        rw [card_map, this, Finset.card_fin n, hpn]
        exact le_of_lt hm
      rw [prod_X_add_C_coeff _ hm_le']
      have : m < n := by rw [hpn]; exact hm
      obtain ⟨s, hs⟩ := isNonarchimedean_finset_powerset_image_add hf_na b m
      rw [Finset.esymm_map_val]
      have h_card : card (map (-b) finset.univ.val) = Fintype.card (Fin n) := by rw [card_map]; rfl
      rw [h_card]
      apply le_trans hs
      have h_pr : f (s.val.prod fun i : Fin n => -b i) ≤ s.val.prod fun i : Fin n => f (-b i) :=
        Finset.le_prod_of_submultiplicative' f (map_nonneg _) hf1 (map_mul_le_mul _) _ _
      apply le_trans h_pr
      have : (s.val.prod fun i : Fin n => f (-b i)) ≤ s.val.prod fun i : Fin n => iSup (f ∘ b) :=
        by
        apply Finset.prod_le_prod
        · intro i hi; exact map_nonneg _ _
        · intro i hi
          rw [map_neg_eq_map]
          exact le_ciSup (Set.Finite.bddAbove (Set.range (f ∘ b)).toFinite) _
      apply le_trans this
      apply le_of_eq
      simp only [Subtype.val_eq_coe, Finset.prod_const]
      suffices h_card : (s : Finset (Fin n)).card = p.nat_degree - m
      · rw [h_card]
      have hs' := s.property
      simp only [Subtype.val_eq_coe, Fintype.card_fin, Finset.mem_powersetLen] at hs' 
      rw [hs'.right, hpn]
    rw [spectralValueTerms_of_natDegree_le _ (le_of_not_lt hm)]
    exact h_supr

/-- If `f` is a nonarchimedean, power-multiplicative `K`-algebra norm on `L`, then the spectral
  value of a polynomial `p : K[X]` that decomposes into linear factos in `L` is equal to the
  maximum of the norms of the roots. -/
theorem max_root_norm_eq_spectral_value' {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (map (fun a : L => X - C a) s).Prod) :
    (iSup fun x : L => if x ∈ s then f x else 0) = spectralValue p :=
  by
  have h_le : 0 ≤ ⨆ x : L, ite (x ∈ s) (f x) 0 :=
    by
    apply Real.iSup_nonneg
    intro x
    split_ifs
    exacts [map_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le
    rintro x
    by_cases hx : x ∈ s
    · have hx0 : aeval x p = 0 := Polynomial.aeval_root s hx hp
      rw [if_pos hx]
      exact root_norm_le_spectralValue hf_pm hf_na (le_of_eq hf1) (p.monic_of_prod' s hp) hx0
    · rw [if_neg hx]
      exact spectralValue_nonneg _
  · apply ciSup_le
    intro m
    by_cases hm : m < p.nat_degree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.nat_degree - m : ℝ) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _) h_le h, ←
        Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (ne_of_gt h), Real.rpow_one, ←
        Nat.cast_sub (le_of_lt hm), Real.rpow_nat_cast]
      have hps : s.card = p.nat_degree := by
        rw [← nat_degree_map (algebraMap K L), ← map_alg_eq_map, hp,
          nat_degree_multiset_prod_X_sub_C_eq_card]
      have hc : ‖p.coeff m‖ = f (((map_alg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1, map_alg_eq_map, coeff_map]
      rw [hc, hp]
      have hm_le' : m ≤ s.card := by rw [hps]; exact le_of_lt hm
      rw [prod_X_sub_C_coeff s hm_le']
      have h : f ((-1) ^ (s.card - m) * s.esymm (s.card - m)) = f (s.esymm (s.card - m)) :=
        by
        cases' neg_one_pow_eq_or L (s.card - m) with h1 hn1
        · rw [h1, one_mul]
        · rw [hn1, neg_mul, one_mul, map_neg_eq_map]
      rw [h, Multiset.esymm]
      have ht :
        ∃ t : Multiset L,
          t.card = s.card - m ∧
            (∀ x : L, x ∈ t → x ∈ s) ∧
              f (map Multiset.prod (powerset_len (s.card - m) s)).Sum ≤ f t.Prod :=
        haveI hm' : m < card s := by rw [hps]; exact hm
        isNonarchimedean_multiset_powerset_image_add hf_na s m
      obtain ⟨t, ht_card, hts, ht_ge⟩ := ht
      apply le_trans ht_ge
      have h_pr : f t.prod ≤ (t.map f).Prod :=
        Real.multiset_le_prod_of_submultiplicative (map_nonneg _) hf1 (map_mul_le_mul _) _
      apply le_trans h_pr
      have hs_ne : s.to_finset.nonempty :=
        by
        rw [← Finset.card_pos]
        apply card_to_finset_pos
        rw [hps]
        exact lt_of_le_of_lt (zero_le _) hm
      have hy : ∃ y : L, y ∈ s ∧ ∀ z : L, z ∈ s → f z ≤ f y := Multiset.max f hs_ne
      obtain ⟨y, hyx, hy_max⟩ := hy
      have : (map f t).Prod ≤ f y ^ (p.nat_degree - m) :=
        by
        have h_card : p.nat_degree - m = (t.map f).card := by rw [card_map, ht_card, ← hps]
        have hx_le : ∀ x : ℝ, x ∈ map f t → x ≤ f y :=
          by
          intro r hr
          obtain ⟨z, hzt, hzr⟩ := multiset.mem_map.mp hr
          rw [← hzr]
          exact hy_max _ (hts _ hzt)
        rw [h_card]
        exact Real.multiset_prod_le_pow_card hx_le
      have h_bdd : BddAbove (Set.range fun x : L => ite (x ∈ s) (f x) 0) :=
        by
        use f y
        rw [mem_upperBounds]
        intro r hr
        obtain ⟨z, hz⟩ := set.mem_range.mpr hr
        simp only at hz 
        rw [← hz]
        split_ifs with h
        · exact hy_max _ h
        · exact map_nonneg _ _
      apply le_trans this
      apply pow_le_pow_of_le_left (map_nonneg _ _)
      apply le_trans _ (le_ciSup h_bdd y)
      rw [if_pos hyx]
    · simp only [spectralValueTerms]
      rw [if_neg hm]
      exact h_le

end BddBySpectralValue

section AlgEquiv

variable {S A B C : Type _} [CommSemiring S] [Semiring A] [Semiring B] [Semiring C] [Algebra S A]
  [Algebra S B] [Algebra S C]

/-- The algebra equivalence obtained by composing two algebra equivalences. -/
def AlgEquiv.comp (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C) : A ≃ₐ[S] C
    where
  toFun := g.toFun ∘ f.toFun
  invFun := f.invFun ∘ g.invFun
  left_inv x := by
    simp only [AlgEquiv.invFun_eq_symm, AlgEquiv.toFun_eq_coe, Function.comp_apply,
      AlgEquiv.symm_apply_apply]
  right_inv x := by
    simp only [AlgEquiv.toFun_eq_coe, AlgEquiv.invFun_eq_symm, Function.comp_apply,
      AlgEquiv.apply_symm_apply]
  map_mul' x y := by simp only [AlgEquiv.toFun_eq_coe, Function.comp_apply, map_mul]
  map_add' x y := by simp only [AlgEquiv.toFun_eq_coe, Function.comp_apply, _root_.map_add]
  commutes' x := by simp only [AlgEquiv.toFun_eq_coe, Function.comp_apply, AlgEquiv.commutes]

theorem AlgEquiv.comp_apply (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C) (x : A) : f.comp g x = g (f x) :=
  rfl

end AlgEquiv

-- In this section we prove Theorem 3.2.1/2 from BGR.
section spectralNorm

variable (K : Type _) [NormedField K] (L : Type _) [Field L] [Algebra K L]

/-- The spectral norm `|y|_sp` is the spectral value of the minimal of `y` over `K`. -/
def spectralNorm (y : L) : ℝ :=
  spectralValue (minpoly K y)

variable {K L}

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` equals its spectral norm
  when regarded as an element of `L`. -/
theorem spectralValue.eq_of_tower {E : Type _} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (h_alg_E : Algebra.IsAlgebraic K E) (x : E) :
    spectralNorm K E x = spectralNorm K L (algebraMap E L x) :=
  by
  have hx : minpoly K x = minpoly K (algebraMap E L x) :=
    minpoly.eq_of_algebraMap_eq (algebraMap E L).Injective
      (is_algebraic_iff_is_integral.mp (h_alg_E x)) rfl
  simp only [spectralNorm, hx]

variable (E : IntermediateField K L)

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` when regarded as an element 
  of the normal closure of `E` equals its spectral norm when regarded as an element of `L`. -/
theorem spectralValue.eq_normal (h_alg_L : Algebra.IsAlgebraic K L) (x : E) :
    spectralNorm K (normalClosure K E (AlgebraicClosureAux E))
        (algebraMap E (normalClosure K E (AlgebraicClosureAux E)) x) =
      spectralNorm K L (algebraMap E L x) :=
  by
  simp only [spectralNorm, spectralValue]
  have h_min :
    minpoly K (algebraMap (↥E) (↥(normalClosure K (↥E) (AlgebraicClosureAux ↥E))) x) =
      minpoly K (algebraMap (↥E) L x) :=
    by
    have hx : IsIntegral K x :=
      is_algebraic_iff_is_integral.mp (intermediate_field.is_algebraic_iff.mpr (h_alg_L ↑x))
    rw [←
      minpoly.eq_of_algebraMap_eq
        (algebraMap (↥E) ↥(normalClosure K E (AlgebraicClosureAux E))).Injective hx rfl,
      minpoly.eq_of_algebraMap_eq (algebraMap (↥E) L).Injective hx rfl]
  simp_rw [h_min]

variable (y : L)

/-- `spectral_norm K L (0 : L) = 0`. -/
theorem spectralNorm_zero : spectralNorm K L (0 : L) = 0 :=
  by
  have h_lr : List.range 1 = [0] := rfl
  rw [spectralNorm, spectralValue, spectralValueTerms, minpoly.zero, nat_degree_X]
  convert ciSup_const
  ext m
  by_cases hm : m < 1
  ·
    rw [if_pos hm, nat.lt_one_iff.mp hm, Nat.cast_one, Nat.cast_zero, sub_zero, div_one,
      Real.rpow_one, coeff_X_zero, norm_zero]
  · rw [if_neg hm]
  infer_instance

/-- `spectral_norm K L y` is nonnegative. -/
theorem spectralNorm_nonneg (y : L) : 0 ≤ spectralNorm K L y :=
  le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

/-- `spectral_norm K L y` is positive if `y ≠ 0`. -/
theorem spectralNorm_zero_lt (h_alg : Algebra.IsAlgebraic K L) {y : L} (hy : y ≠ 0) :
    0 < spectralNorm K L y := by
  rw [lt_iff_le_and_ne]
  refine' ⟨spectralNorm_nonneg _, _⟩
  rw [spectralNorm, Ne.def, eq_comm,
    spectralValue_eq_zero_iff (minpoly.monic (isAlgebraic_iff_isIntegral.mp (h_alg y)))]
  have h0 : coeff (minpoly K y) 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg y)) hy
  intro h
  have h0' : (minpoly K y).coeff 0 = 0 := by
    rw [h, coeff_X_pow,
      if_neg (ne_of_lt (minpoly.natDegree_pos (is_algebraic_iff_is_integral.mp (h_alg y))))]
  exact h0 h0'

/-- If `spectral_norm K L x = 0`, then `x = 0`. -/
theorem eq_zero_of_map_spectralNorm_eq_zero (h_alg : Algebra.IsAlgebraic K L) {x : L}
    (hx : spectralNorm K L x = 0) : x = 0 :=
  by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h_alg h0)) hx

/-- If `f` is a power-multiplicative `K`-algebra norm on `L` with `f 1 ≤ 1`, then `f`
  is bounded above by `spectral_norm K L`. -/
theorem spectralNorm_ge_norm (h_alg : Algebra.IsAlgebraic K L) {f : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f) (hf1 : f 1 ≤ 1) (x : L) :
    f x ≤ spectralNorm K L x :=
  by
  apply
    root_norm_le_spectralValue hf_pm hf_na hf1
      (minpoly.monic (isAlgebraic_iff_isIntegral.mp (h_alg x)))
  rw [minpoly.aeval]

/-- The `K`-algebra automorphisms of `L` are isometries with respect to the spectral norm. -/
theorem spectralNorm_aut_isom (h_alg : Algebra.IsAlgebraic K L) (σ : L ≃ₐ[K] L) (x : L) :
    spectralNorm K L x = spectralNorm K L (σ x) := by
  simp only [spectralNorm, minpoly.eq_of_conj h_alg]

-- We first assume that the extension is finite and normal
section Finite

section Normal

/--
If `L/K` is finite and normal, then `spectral_norm K L x = supr (λ (σ : L ≃ₐ[K] L), f (σ x))`. -/
theorem spectralNorm_max_of_fd_normal (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf_ext : FunctionExtends (fun x : K => ‖x‖₊) f) (x : L) :
    spectralNorm K L x = iSup fun σ : L ≃ₐ[K] L => f (σ x) :=
  by
  refine'
    le_antisymm _
      (ciSup_le fun σ =>
        root_norm_le_spectralValue hf_pm hf_na (extends_is_norm_le_one_class hf_ext)
          (minpoly.monic (Normal.isIntegral hn x)) (minpoly.aeval_conj _ _))
  · set p := minpoly K x with hp_def
    have hp_sp : splits (algebraMap K L) (minpoly K x) := hn.splits x
    obtain ⟨s, hs⟩ := (splits_iff_exists_multiset _).mp hp_sp
    have : map_alg K L p = map (algebraMap K L) p := rfl
    have h_lc : (algebraMap K L) (minpoly K x).leadingCoeff = 1 :=
      by
      have h1 : (minpoly K x).leadingCoeff = 1 := by rw [← monic];
        exact minpoly.monic (Normal.isIntegral hn x)
      rw [h1, map_one]
    rw [h_lc, map_one, one_mul] at hs 
    simp only [spectralNorm]
    rw [← max_root_norm_eq_spectral_value' hf_pm hf_na (extends_is_norm_one_class hf_ext) _ _ hs]
    apply ciSup_le
    intro y
    split_ifs
    · have hy : ∃ σ : L ≃ₐ[K] L, σ x = y :=
        minpoly.conj_of_root' h_alg hn (Polynomial.aeval_root s h hs)
      obtain ⟨σ, hσ⟩ := hy
      rw [← hσ]
      exact le_ciSup (Fintype.bddAbove_range _) σ
    · exact Real.iSup_nonneg fun σ => map_nonneg _ _

/-- If `L/K` is finite and normal, then `spectral_norm K L = alg_norm_of_galois h_fin hna`. -/
theorem spectralNorm_eq_algNormOfGalois (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    spectralNorm K L = algNormOfGalois h_fin hna :=
  by
  ext x
  set f := Classical.choose (finite_extension_pow_mul_seminorm h_fin hna) with hf
  have hf_pow : IsPowMul f :=
    (Classical.choose_spec (finite_extension_pow_mul_seminorm h_fin hna)).1
  have hf_ext : FunctionExtends _ f :=
    (Classical.choose_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.1
  have hf_na : IsNonarchimedean f :=
    (Classical.choose_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.2
  rw [spectralNorm_max_of_fd_normal h_alg h_fin hn hf_pow hf_na hf_ext]
  rfl

/-- If `L/K` is finite and normal, then `spectral_norm K L` is power-multiplicative. -/
theorem spectralNorm_isPowMul_of_fd_normal (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (spectralNorm K L) :=
  by
  rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]
  exact algNormOfGalois_isPowMul h_fin hna

/-- The spectral norm is a `K`-algebra norm on `L` when `L/K` is finite and normal. -/
def spectralAlgNormOfFdNormal (h_alg : Algebra.IsAlgebraic K L) (h_fin : FiniteDimensional K L)
    (hn : Normal K L) (hna : IsNonarchimedean (norm : K → ℝ)) : AlgebraNorm K L
    where
  toFun := spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]; exact map_zero _
  add_le' := by rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]; exact map_add_le_add _
  neg' := by rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]; exact map_neg_eq_map _
  hMul_le' := by rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]; exact map_mul_le_mul _
  eq_zero_of_map_eq_zero' x := by rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna];
    exact eq_zero_of_map_eq_zero _
  smul' := by
    rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]
    exact AlgebraNormClass.map_smul_eq_hMul _

theorem spectralAlgNormOfFdNormal_def (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) (hna : IsNonarchimedean (norm : K → ℝ))
    (x : L) : spectralAlgNormOfFdNormal h_alg h_fin hn hna x = spectralNorm K L x :=
  rfl

/-- The spectral norm is nonarchimedean when `L/K` is finite and normal. -/
theorem spectralNorm_isNonarchimedean_of_fd_normal (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (spectralNorm K L) :=
  by
  rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]
  exact algNormOfGalois_isNonarchimedean h_fin hna

/-- The spectral norm extends the norm on `K` when `L/K` is finite and normal. -/
theorem spectralNorm_extends_norm_of_fd (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    FunctionExtends (norm : K → ℝ) (spectralNorm K L) :=
  by
  rw [spectralNorm_eq_algNormOfGalois h_alg h_fin hn hna]
  exact algNormOfGalois_extends h_fin hna

/-- If `L/K` is finite and normal, and `f` is a power-multiplicative `K`-algebra norm on `L`
  extending the norm on `K`, then `f = spectral_norm K L`. -/
theorem spectralNorm_unique_of_fd_normal (h_alg : Algebra.IsAlgebraic K L)
    (h_fin : FiniteDimensional K L) (hn : Normal K L) {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf_ext : FunctionExtends (fun x : K => ‖x‖₊) f)
    (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x : L), f x = f (σ x)) (x : L) : f x = spectralNorm K L x :=
  by
  have h_sup : (iSup fun σ : L ≃ₐ[K] L => f (σ x)) = f x :=
    by
    rw [← @ciSup_const _ (L ≃ₐ[K] L) _ _ (f x)]
    exact iSup_congr fun σ => by rw [hf_iso σ x]
  rw [spectralNorm_max_of_fd_normal h_alg h_fin hn hf_pm hf_na hf_ext, h_sup]

end Normal

end Finite

-- Now we let L/K be any algebraic extension
/-- The spectral norm is a power-multiplicative K-algebra norm on L extending the norm on K. -/
theorem spectralValue.eq_normal' (h_alg_L : Algebra.IsAlgebraic K L) {E : IntermediateField K L}
    {x : L} (g : E) (h_map : algebraMap E L g = x) :
    spectralNorm K (normalClosure K E (AlgebraicClosureAux E))
        (algebraMap E (normalClosure K E (AlgebraicClosureAux E)) g) =
      spectralNorm K L x :=
  by
  rw [← h_map]
  exact spectralValue.eq_normal E h_alg_L g

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The spectral norm is power-multiplicative. -/
theorem spectralNorm_isPowMul (h_alg : Algebra.IsAlgebraic K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : IsPowMul (spectralNorm K L) :=
  by
  intro x n hn
  set E := K⟮⟯ with hE
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (is_algebraic_iff_is_integral.mp (h_alg x))
  have h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic h_alg E
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  haveI h_normal : Normal K (AlgebraicClosureAux ↥K⟮⟯) :=
    IntermediateField.AdjoinSimple.alg_closure_normal h_alg x
  rw [← spectralValue.eq_normal' h_alg _ (IntermediateField.AdjoinSimple.algebraMap_gen K x), ←
    spectralValue.eq_normal' h_alg (g ^ n) h_map, map_pow]
  exact
    spectralNorm_isPowMul_of_fd_normal (normalClosure.isAlgebraic K E h_alg_E)
      (normalClosure.is_finiteDimensional K E _) (normalClosure.normal K E _) hna _ hn

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The spectral norm is compatible with the action of `K`. -/
theorem spectralNorm_smul (h_alg : Algebra.IsAlgebraic K L) (hna : IsNonarchimedean (norm : K → ℝ))
    (k : K) (y : L) : spectralNorm K L (k • y) = ‖k‖₊ * spectralNorm K L y :=
  by
  set E := K⟮⟯ with hE
  haveI : Normal K (AlgebraicClosureAux ↥E) :=
    IntermediateField.AdjoinSimple.alg_closure_normal h_alg y
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (is_algebraic_iff_is_integral.mp (h_alg y))
  have h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic h_alg E
  set g := IntermediateField.AdjoinSimple.gen K y with hg
  have hgy : k • y = (algebraMap (↥K⟮⟯) L) (k • g) := rfl
  have h :
    algebraMap K⟮⟯ (normalClosure K K⟮⟯ (AlgebraicClosureAux K⟮⟯)) (k • g) =
      k • algebraMap K⟮⟯ (normalClosure K K⟮⟯ (AlgebraicClosureAux K⟮⟯)) g :=
    by rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_assoc]
  rw [← spectralValue.eq_normal' h_alg g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hgy, ←
    spectralValue.eq_normal' h_alg (k • g) rfl, h]
  have h_alg' := normalClosure.isAlgebraic K E h_alg_E
  rw [←
    spectralAlgNormOfFdNormal_def h_alg'
      (normalClosure.is_finiteDimensional K E (AlgebraicClosureAux E)) (normalClosure.normal K E _)
      hna]
  exact map_smul_eq_mul _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The spectral norm is nonarchimedean. -/
theorem spectralNorm_isNonarchimedean (h_alg : Algebra.IsAlgebraic K L)
    (h : IsNonarchimedean (norm : K → ℝ)) : IsNonarchimedean (spectralNorm K L) :=
  by
  intro x y
  set E := K⟮⟯ with hE
  haveI : Normal K (AlgebraicClosureAux ↥E) :=
    IntermediateField.AdjoinDouble.alg_closure_normal h_alg x y
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.AdjoinAdjoin.finiteDimensional (is_algebraic_iff_is_integral.mp (h_alg x))
      (is_algebraic_iff_is_integral.mp (h_alg y))
  have h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic h_alg E
  set gx := IntermediateField.AdjoinAdjoin.gen1 K x y with hgx
  set gy := IntermediateField.AdjoinAdjoin.gen2 K x y with hgy
  have hxy : x + y = (algebraMap K⟮⟯ L) (gx + gy) := rfl
  rw [hxy, ← spectralValue.eq_normal' h_alg (gx + gy) hxy, ←
    spectralValue.eq_normal' h_alg gx (IntermediateField.AdjoinAdjoin.algebraMap_gen1 K x y), ←
    spectralValue.eq_normal' h_alg gy (IntermediateField.AdjoinAdjoin.algebraMap_gen2 K x y),
    _root_.map_add]
  exact
    spectralNorm_isNonarchimedean_of_fd_normal (normalClosure.isAlgebraic K E h_alg_E)
      (normalClosure.is_finiteDimensional K E _) (normalClosure.normal K E _) h _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The spectral norm is submultiplicative. -/
theorem spectralNorm_hMul (h_alg : Algebra.IsAlgebraic K L) (hna : IsNonarchimedean (norm : K → ℝ))
    (x y : L) : spectralNorm K L (x * y) ≤ spectralNorm K L x * spectralNorm K L y :=
  by
  set E := K⟮⟯ with hE
  haveI : Normal K (AlgebraicClosureAux ↥E) :=
    IntermediateField.AdjoinDouble.alg_closure_normal h_alg x y
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.AdjoinAdjoin.finiteDimensional (is_algebraic_iff_is_integral.mp (h_alg x))
      (is_algebraic_iff_is_integral.mp (h_alg y))
  have h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic h_alg E
  set gx := IntermediateField.AdjoinAdjoin.gen1 K x y with hgx
  set gy := IntermediateField.AdjoinAdjoin.gen2 K x y with hgy
  have hxy : x * y = (algebraMap K⟮⟯ L) (gx * gy) := rfl
  rw [hxy, ← spectralValue.eq_normal' h_alg (gx * gy) hxy, ←
    spectralValue.eq_normal' h_alg gx (IntermediateField.AdjoinAdjoin.algebraMap_gen1 K x y), ←
    spectralValue.eq_normal' h_alg gy (IntermediateField.AdjoinAdjoin.algebraMap_gen2 K x y),
    map_mul, ←
    spectralAlgNormOfFdNormal_def (normalClosure.isAlgebraic K E h_alg_E)
      (normalClosure.is_finiteDimensional K E (AlgebraicClosureAux E)) (normalClosure.normal K E _)
      hna]
  exact map_mul_le_mul _ _ _

/-- The spectral norm extends the norm on `K`. -/
theorem spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖ :=
  by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).Injective]
  exact spectralValue_x_sub_c k

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- `spectral_norm K L (-y) = spectral_norm K L y` . -/
theorem spectralNorm_neg (h_alg : Algebra.IsAlgebraic K L) (hna : IsNonarchimedean (norm : K → ℝ))
    (y : L) : spectralNorm K L (-y) = spectralNorm K L y :=
  by
  set E := K⟮⟯ with hE
  haveI : Normal K (AlgebraicClosureAux ↥E) :=
    IntermediateField.AdjoinSimple.alg_closure_normal h_alg y
  haveI h_fd_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (is_algebraic_iff_is_integral.mp (h_alg y))
  have h_alg_E : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic h_alg E
  set g := IntermediateField.AdjoinSimple.gen K y with hg
  have hy : -y = (algebraMap K⟮⟯ L) (-g) := rfl
  rw [← spectralValue.eq_normal' h_alg g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hy, ←
    spectralValue.eq_normal' h_alg (-g) hy, map_neg, ←
    spectralAlgNormOfFdNormal_def (normalClosure.isAlgebraic K E h_alg_E)
      (normalClosure.is_finiteDimensional K E (AlgebraicClosureAux E)) (normalClosure.normal K E _)
      hna]
  exact map_neg_eq_map _ _

/-- The spectral norm is a `K`-algebra norm on `L`. -/
def spectralAlgNorm (h_alg : Algebra.IsAlgebraic K L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    AlgebraNorm K L where
  toFun := spectralNorm K L
  map_zero' := spectralNorm_zero
  add_le' :=
    add_le_of_isNonarchimedean spectralNorm_nonneg (spectralNorm_isNonarchimedean h_alg hna)
  hMul_le' := spectralNorm_hMul h_alg hna
  smul' := spectralNorm_smul h_alg hna
  neg' := spectralNorm_neg h_alg hna
  eq_zero_of_map_eq_zero' x hx := eq_zero_of_map_spectralNorm_eq_zero h_alg hx

theorem spectralAlgNorm_def (h_alg : Algebra.IsAlgebraic K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    spectralAlgNorm h_alg hna x = spectralNorm K L x :=
  rfl

theorem spectralAlgNorm_extends (h_alg : Algebra.IsAlgebraic K L) (k : K)
    (hna : IsNonarchimedean (norm : K → ℝ)) : spectralAlgNorm h_alg hna (algebraMap K L k) = ‖k‖ :=
  spectralNorm_extends k

theorem spectralNorm_is_norm_le_one_class : spectralNorm K L 1 ≤ 1 :=
  by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1, spectralNorm_extends, norm_one]

theorem spectralAlgNorm_is_norm_le_one_class (h_alg : Algebra.IsAlgebraic K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : spectralAlgNorm h_alg hna 1 ≤ 1 :=
  spectralNorm_is_norm_le_one_class

theorem spectralNorm_is_norm_one_class : spectralNorm K L 1 = 1 :=
  by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1, spectralNorm_extends, norm_one]

theorem spectralAlgNorm_is_norm_one_class (h_alg : Algebra.IsAlgebraic K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : spectralAlgNorm h_alg hna 1 = 1 :=
  spectralNorm_is_norm_one_class

theorem spectralAlgNorm_isPowMul (h_alg : Algebra.IsAlgebraic K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) : IsPowMul (spectralAlgNorm h_alg hna) :=
  spectralNorm_isPowMul h_alg hna

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- The restriction of a `K`-algebra norm on `L` to an intermediate field `K⟮x⟯`. -/
def Adjoin.algebraNorm (f : AlgebraNorm K L) (x : L) : AlgebraNorm K K⟮⟯
    where
  toFun := f ∘ algebraMap (↥K⟮⟯) L
  map_zero' := by simp only [Function.comp_apply, _root_.map_zero]
  add_le' a b := by simp only [Function.comp_apply, _root_.map_add, map_add_le_add]
  hMul_le' a b := by simp only [Function.comp_apply, map_mul, map_mul_le_mul]
  smul' r a := by
    simp only [Function.comp_apply, Algebra.smul_def]
    rw [map_mul, ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq, ← Algebra.smul_def,
      map_smul_eq_mul _ _]
  neg' a := by simp only [Function.comp_apply, map_neg, map_neg_eq_map]
  eq_zero_of_map_eq_zero' a ha :=
    by
    simp only [Function.comp_apply, map_eq_zero_iff_eq_zero, _root_.map_eq_zero] at ha 
    exact ha

end spectralNorm

section SpectralValuation

variable {K : Type _} [NormedField K] [CompleteSpace K] {L : Type _} [hL : Field L] [Algebra K L]
  (h_alg : Algebra.IsAlgebraic K L)

-- Theorem 3.2.4/2
section

/-- The `normed_ring` stucture on a ring `A` determined by a `ring_norm`. -/
def normToNormedRing {A : Type _} [Ring A] (f : RingNorm A) : NormedRing A
    where
  norm x := f x
  dist x y := f (x - y)
  dist_self x := by simp only [sub_self, _root_.map_zero]
  dist_comm x y := by simp only [← neg_sub x y, map_neg_eq_map]
  dist_triangle x y z := by
    have hxyz : x - z = x - y + (y - z) := by abel
    simp only [hxyz, map_add_le_add]
  eq_of_dist_eq_zero x y hxy := eq_of_sub_eq_zero (RingNorm.eq_zero_of_map_eq_zero' _ _ hxy)
  dist_eq x y := rfl
  norm_hMul x y := by simp only [map_mul_le_mul]

end

/-- The `normed_field` stucture on a field `L` determined by a `mul_ring_norm`. -/
def mulNormToNormedField (f : MulRingNorm L) : NormedField L
    where
  norm x := f x
  dist x y := f (x - y)
  dist_self x := by simp only [sub_self, _root_.map_zero]
  dist_comm x y := by simp only [← neg_sub x y, map_neg_eq_map]
  dist_triangle x y z := by
    have hxyz : x - z = x - y + (y - z) := by ring
    simp only [hxyz, map_add_le_add]
  eq_of_dist_eq_zero x y hxy := eq_of_sub_eq_zero (MulRingNorm.eq_zero_of_map_eq_zero' _ _ hxy)
  dist_eq x y := rfl
  norm_mul' x y := by simp only [map_mul]

theorem mulNormToNormedField.norm (f : MulRingNorm L) :
    (mulNormToNormedField f).norm = fun x => (f x : ℝ) :=
  rfl

end SpectralValuation

