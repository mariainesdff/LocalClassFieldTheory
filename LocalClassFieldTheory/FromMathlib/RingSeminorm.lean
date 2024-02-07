/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.Seminorm

#align_import from_mathlib.ring_seminorm

/-!
# Nonarchimedean ring seminorms and algebra norms

In this file, we define some properties of functions (power-multiplicative, extends,
nonarchimedean) which will be of special interest to us when applied to ring seminorms or
additive group seminorms.

We prove several properties of nonarchimedean functions.

We also define algebra norms and multiplicative algebra norms.

## Main Definitions
* `is_pow_mul` : `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`.
* `function_extends` : given an `α`-algebra `β`, a function `f : β → ℝ` extends a function
  `g : α → ℝ` if `∀ x : α, f (algebra_map α β x) = g x`.
* `is_nonarchimedean`: a function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong
  triangle inequality `f (r + s) ≤ max (f r) (f s)` for all `r s : R`.
* `algebra_norm` : an algebra norm on an `R`-algebra norm `S` is a ring norm on `S` compatible with
  the action of `R`.
* `mul_algebra_norm` : amultiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative
  ring norm on `S` compatible with the action of `R`.

## Main Results
* `is_nonarchimedean_multiset_image_add` : given a nonarchimedean additive group seminorm `f` on
  `α`, a function `g : β → α` and a multiset `s : multiset β`, we can always find `b : β`, belonging
  to `s` if `s` is nonempty, such that `f (t.sum g) ≤ f (g b)` .

## Tags

norm, nonarchimedean, pow_mul, power-multiplicative, algebra norm
-/


open Metric

namespace Nat

theorem one_div_cast_pos {n : ℕ} (hn : n ≠ 0) : 0 < 1 / (n : ℝ) := by
  rw [one_div, inv_pos, cast_pos]
  exact Nat.pos_of_ne_zero hn

theorem one_div_cast_nonneg (n : ℕ) : 0 ≤ 1 / (n : ℝ) := by
  by_cases hn : n = 0
  · rw [hn, cast_zero, div_zero]
  · refine' le_of_lt (one_div_cast_pos hn)

theorem one_div_cast_ne_zero {n : ℕ} (hn : n ≠ 0) : 1 / (n : ℝ) ≠ 0 :=
  _root_.ne_of_gt (one_div_cast_pos hn)

end Nat

/-- A function `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`. -/
def IsPowMul {R : Type _} [Ring R] (f : R → ℝ) :=
  ∀ (a : R) {n : ℕ} (_ : 1 ≤ n), f (a ^ n) = f a ^ n

/-- Given an `α`-algebra `β`, a function `f : β → ℝ` extends a function `g : α → ℝ` if
  `∀ x : α, f (algebra_map α β x) = g x`. -/
def FunctionExtends {α : Type _} [CommRing α] (g : α → ℝ) {β : Type _} [Ring β] [Algebra α β]
    (f : β → ℝ) : Prop :=
  ∀ x : α, f (algebraMap α β x) = g x

/-- A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong triangle inequality
  `f (r + s) ≤ max (f r) (f s)` for all `r s : R`. -/
def IsNonarchimedean {R : Type _} [AddGroup R] (f : R → ℝ) : Prop :=
  ∀ r s, f (r + s) ≤ max (f r) (f s)

/-- A nonarchimedean function satisfies the triangle inequality. -/
theorem add_le_of_isNonarchimedean {α : Type _} [AddCommGroup α] {f : α → ℝ} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) (a b : α) : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n • a) ≤ (f a)`. -/
theorem isNonarchimedean_nsmul {F α : Type _} [AddCommGroup α] [FunLike F α ℝ]
  [AddGroupSeminormClass F α ℝ] {f : F}
    (hna : IsNonarchimedean f) (n : ℕ) (a : α) : f (n • a) ≤ f a := by
  induction' n with n hn
  · rw [zero_nsmul, map_zero _]; exact map_nonneg _ _
  · have : n.succ • a = (n + 1) • a := rfl
    rw [this, add_smul, one_smul]
    exact le_trans (hna _ _) (max_le_iff.mpr ⟨hn, le_refl _⟩)

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n * a) ≤ (f a)`. -/
theorem isNonarchimedean_nmul {F α : Type _} [Ring α] [FunLike F α ℝ] [AddGroupSeminormClass F α ℝ]
  {f : F} (hna : IsNonarchimedean f) (n : ℕ) (a : α) : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact isNonarchimedean_nsmul hna _ _

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f y ≠ f x`, then `f (x + y) = max (f x) (f y)`. -/
theorem isNonarchimedean_add_eq_max_of_ne {F α : Type _} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f y ≠ f x) :
    f (x + y) = max (f x) (f y) := by
  wlog hle : f y ≤ f x generalizing y x with H
  · rw [add_comm, max_comm]
    exact H hne.symm (le_of_lt (not_le.mp hle))
  · have hlt : f y < f x := lt_of_le_of_ne hle hne
    have : f x ≤ max (f (x + y)) (f y) :=
      calc
        f x = f (x + y + -y) := by rw [add_neg_cancel_right]
        _ ≤ max (f (x + y)) (f (-y)) := (hna _ _)
        _ = max (f (x + y)) (f y) := by rw [map_neg_eq_map f y]
    have hnge : f y ≤ f (x + y) := by
      apply le_of_not_gt
      intro hgt
      rw [max_eq_right_of_lt hgt] at this
      apply not_lt_of_ge this
      assumption
    have : f x ≤ f (x + y) := by rwa [max_eq_left hnge] at this
    apply le_antisymm
    · exact hna _ _
    · rw [max_eq_left_of_lt hlt]
      assumption

open scoped Classical

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a finset
  `t : finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty, such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem isNonarchimedean_finset_image_add {F α : Type _} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {β : Type _} [hβ : Nonempty β]
    (g : β → α) (t : Finset β) :
    ∃ (b : β) (_ : t.Nonempty → b ∈ t), f (t.sum g) ≤ f (g b) := by
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      refine' ⟨hβ.some, by simp only [Finset.not_nonempty_empty, IsEmpty.forall_iff], _⟩
      rw [map_zero f]; exact map_nonneg f _
  | @insert a s has hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      rw [Finset.sum_insert has]
      by_cases hMa : f (g M) ≤ f (g a)
      · refine' ⟨a, _, le_trans (hna _ _) (max_le_iff.mpr ⟨le_refl _, le_trans hM hMa⟩)⟩
        simp only [Finset.nonempty_coe_sort, Finset.insert_nonempty, Finset.mem_insert,
          eq_self_iff_true, true_or_iff, forall_true_left]
      · rw [not_le] at hMa
        by_cases hs : s.Nonempty
        · refine' ⟨M, _, le_trans (hna _ _) (max_le_iff.mpr ⟨le_of_lt hMa, hM⟩)⟩
          simp only [Finset.nonempty_coe_sort, Finset.insert_nonempty, Finset.mem_insert,
            forall_true_left]
          exact Or.intro_right _ (hMs hs)
        · use a
          constructor
          · have h0 : f (s.sum g) = 0 := by
              rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty, map_zero]
            apply le_trans (hna _ _)
            rw [h0]
            exact max_le_iff.mpr ⟨le_refl _, map_nonneg _ _⟩
          · simp only [Finset.insert_nonempty, Finset.mem_insert, true_or, forall_true_left]

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  multiset `s : multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` . -/
theorem isNonarchimedean_multiset_image_add {F α : Type _} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {β : Type _} [hβ : Nonempty β]
    (g : β → α) (s : Multiset β) :
    ∃ (b : β) (_ : 0 < Multiset.card s → b ∈ s), f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero, map_zero f]
      refine' ⟨hβ.some, by simp only [not_lt_zero', IsEmpty.forall_iff], map_nonneg _ _⟩
  | @cons a t hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      by_cases hMa : f (g M) ≤ f (g a)
      · refine' ⟨a, _, _⟩
        · simp only [Multiset.card_cons, Nat.succ_pos', Multiset.mem_cons_self, forall_true_left]
        · rw [Multiset.map_cons, Multiset.sum_cons]
          exact le_trans (hna _ _) (max_le_iff.mpr ⟨le_refl _, le_trans hM hMa⟩)
      · rw [not_le] at hMa
        by_cases ht : 0 < Multiset.card t
        · refine' ⟨M, _, _⟩
          · simp only [Multiset.card_cons, Nat.succ_pos', Multiset.mem_cons, forall_true_left]
            exact Or.intro_right _ (hMs ht)
          rw [Multiset.map_cons, Multiset.sum_cons]
          exact le_trans (hna _ _) (max_le_iff.mpr ⟨le_of_lt hMa, hM⟩)
        · refine' ⟨a, _, _⟩
          · simp only [Multiset.card_cons, Nat.succ_pos', Multiset.mem_cons_self, forall_true_left]
          · have h0 : f (Multiset.map g t).sum = 0 :=
              by
              simp only [not_lt, le_zero_iff, Multiset.card_eq_zero] at ht
              rw [ht, Multiset.map_zero, Multiset.sum_zero, map_zero f]
            rw [Multiset.map_cons, Multiset.sum_cons]
            apply le_trans (hna _ _)
            rw [h0]
            exact max_le_iff.mpr ⟨le_refl _, map_nonneg _ _⟩

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a number `n : ℕ` and a function
  `g : ℕ → α`, there exists `m : ℕ` such that `f ((finset.range n).sum g) ≤ f (g m)`.
  If `0 < n`, this `m` satisfies `m < n`. -/
theorem isNonarchimedean_finset_range_add_le {F α : Type _} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) (n : ℕ) (g : ℕ → α) :
    ∃ (m : ℕ) (_ : 0 < n → m < n), f ((Finset.range n).sum g) ≤ f (g m) := by
  obtain ⟨m, hm, h⟩ := isNonarchimedean_finset_image_add hna g (Finset.range n)
  rw [Finset.nonempty_range_iff, ← zero_lt_iff, Finset.mem_range] at hm
  exact ⟨m, hm, h⟩

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
theorem isNonarchimedean_add_pow {F α : Type _} [CommRing α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) (n : ℕ) (a b : α) :
    ∃ (m : ℕ) (_ : m ∈ List.range (n + 1)), f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ :=
    isNonarchimedean_finset_image_add hna (fun m : ℕ => a ^ m * b ^ (n - m) * ↑(n.choose m))
      (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, Ne.def, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    if_true, forall_true_left] at hm_lt
  refine' ⟨m, List.mem_range.mpr hm_lt, _⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (isNonarchimedean_nmul hna _ _) (map_mul_le_mul _ _ _))

/-- If `f` is a ring seminorm on `a`, then `∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n`. -/
theorem map_pow_le_pow {F α : Type _} [Ring α] [FunLike F α ℝ] [RingSeminormClass F α ℝ] (f : F)
    (a : α) : ∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simp only [pow_one, le_refl]
  | n + 2, _ => by
    simp only [pow_succ _ (n + 1)];
      exact
        le_trans (map_mul_le_mul f a _)
          (mul_le_mul_of_nonneg_left (map_pow_le_pow _ _ n.succ_ne_zero) (map_nonneg f a))

/-- If `f` is a ring seminorm on `a` with `f 1 ≤ `, then `∀ (n : ℕ), f (a ^ n) ≤ f a ^ n`. -/
theorem map_pow_le_pow' {F α : Type _} [Ring α] [FunLike F α ℝ] [RingSeminormClass F α ℝ] {f : F}
  (hf1 : f 1 ≤ 1) (a : α) : ∀ n : ℕ, f (a ^ n) ≤ f a ^ n
  | 0 => by simp only [pow_zero, hf1]
  | n + 1 => by
    simp only [pow_succ _ n];
      exact le_trans (map_mul_le_mul f a _)
        (mul_le_mul_of_nonneg_left (map_pow_le_pow' hf1 _ n) (map_nonneg f a))

/-- An algebra norm on an `R`-algebra norm `S` is a ring norm on `S` compatible with the
  action of `R`. -/
structure AlgebraNorm (R : Type _) [SeminormedCommRing R] (S : Type _) [Ring S]
    [Algebra R S] extends RingNorm S, Seminorm R S

attribute [nolint docBlame] AlgebraNorm.toSeminorm AlgebraNorm.toRingNorm

instance (K : Type _) [NormedField K] : Inhabited (AlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      mul_le'   := norm_mul_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `algebra_norm_class F α` states that `F` is a type of algebra norms on the ring `β`.
You should extend this class when you extend `algebra_norm`. -/
class AlgebraNormClass (F : Type _) (R : outParam <| Type _) [SeminormedCommRing R]
    (S : outParam <| Type _) [Ring S] [Algebra R S] [FunLike F S ℝ] extends RingNormClass F S ℝ,
    SeminormClass F R S

-- `R` is an `out_param`, so this is a false positive.
--attribute [nolint DangerousInstance] AlgebraNormClass.toRingNormClass

namespace AlgebraNorm

variable {R : Type _} [SeminormedCommRing R] {S : Type _} [Ring S] [Algebra R S]
  {f : AlgebraNorm R S}

/-- The ring_seminorm underlying an algebra norm. -/
def toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S :=
  f.toRingNorm.toRingSeminorm

instance : FunLike (AlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective' f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr;
    simp only at h
    ext s
    erw [h]
    rfl

instance algebraNormClass : AlgebraNormClass (AlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_mul_le_mul f  := f.mul_le'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (AlgebraNorm R S) fun _ => S → ℝ :=
  DFunLike.hasCoeToFun

theorem toFun_eq_coe (p : AlgebraNorm R S) : p.toFun = p := rfl

@[ext]
theorem ext {p q : AlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
theorem extends_norm' {f : AlgebraNorm R S} (hf1 : f 1 = 1) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← hf1]; exact f.smul' _ _

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
theorem extends_norm {f : AlgebraNorm R S} (hf1 : f 1 = 1) (a : R) : f (algebraMap R S a) = ‖a‖ :=
  by rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

end AlgebraNorm

/-- A multiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative ring norm on `S`
  compatible with the action of `R`. -/
structure MulAlgebraNorm (R : Type _) [SeminormedCommRing R] (S : Type _) [Ring S]
    [Algebra R S] extends MulRingNorm S, Seminorm R S

attribute [nolint docBlame] MulAlgebraNorm.toSeminorm MulAlgebraNorm.toMulRingNorm

instance (K : Type _) [NormedField K] : Inhabited (MulAlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      map_one'  := norm_one
      map_mul'  := norm_mul
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `algebra_norm_class F α` states that `F` is a type of algebra norms on the ring `β`.
You should extend this class when you extend `algebra_norm`. -/
class MulAlgebraNormClass (F : Type _) (R : outParam <| Type _) [SeminormedCommRing R]
    (S : outParam <| Type _) [Ring S] [Algebra R S] [FunLike F S ℝ] extends MulRingNormClass F S ℝ,
    SeminormClass F R S


-- `R` is an `out_param`, so this is a false positive.
--attribute [nolint dangerous_instance] MulAlgebraNormClass.toMulRingNormClass

namespace MulAlgebraNorm

variable {R S : outParam <| Type _} [SeminormedCommRing R] [Ring S] [Algebra R S]
  {f : AlgebraNorm R S}

instance : FunLike (MulAlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective' f f' h:= by
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, DFunLike.coe_fn_eq] at h
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := f'; congr;

instance mulAlgebraNormClass : MulAlgebraNormClass (MulAlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_one f         := f.map_one'
  map_mul f         := f.map_mul'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (MulAlgebraNorm R S) fun _ => S → ℝ :=
  DFunLike.hasCoeToFun

theorem toFun_eq_coe (p : MulAlgebraNorm R S) : p.toFun = p := rfl

@[ext]
theorem ext {p q : MulAlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
theorem extends_norm' (f : MulAlgebraNorm R S) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← f.map_one', ← f.smul']; rfl

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
theorem extends_norm (f : MulAlgebraNorm R S) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' _ _

end MulAlgebraNorm

namespace MulRingNorm

variable {R : Type _} [NonAssocRing R]

/-- The ring norm underlying a multiplicative ring norm. -/
def toRingNorm (f : MulRingNorm R) : RingNorm R where
  toFun       := f
  map_zero'   := f.map_zero'
  add_le'     := f.add_le'
  neg'        := f.neg'
  mul_le' x y := le_of_eq (f.map_mul' x y)
  eq_zero_of_map_eq_zero' := f.eq_zero_of_map_eq_zero'

/-- A multiplicative ring norm is power-multiplicative. -/
theorem isPowMul {A : Type _} [Ring A] (f : MulRingNorm A) : IsPowMul f := fun x n hn => by
  cases n
  · exfalso; linarith
  · rw [map_pow]

end MulRingNorm

/-- The seminorm on a `semi_normed_ring`, as a `ring_seminorm`. -/
def SeminormedRing.toRingSeminorm (R : Type _) [SeminormedRing R] : RingSeminorm R where
  toFun     := norm
  map_zero' := norm_zero
  add_le'   := norm_add_le
  mul_le'   := norm_mul_le
  neg'      := norm_neg

/-- The norm on a `normed_ring`, as a `ring_norm`. -/
@[simps]
def NormedRing.toRingNorm (R : Type _) [NormedRing R] : RingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  add_le'   := norm_add_le
  mul_le'   := norm_mul_le
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

@[simp]
theorem NormedRing.toRingNorm_apply (R : Type _) [NormedRing R] (x : R) :
    (NormedRing.toRingNorm R) x = ‖x‖ :=
  rfl

/-- The norm on a `normed_field`, as a `mul_ring_norm`. -/
def NormedField.toMulRingNorm (R : Type _) [NormedField R] : MulRingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  map_one'  := norm_one
  add_le'   := norm_add_le
  map_mul'  := norm_mul
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx
