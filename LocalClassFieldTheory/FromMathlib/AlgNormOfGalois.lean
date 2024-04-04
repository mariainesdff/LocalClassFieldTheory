/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.Fintype.Order
import Mathlib.FieldTheory.Fixed
import LocalClassFieldTheory.FromMathlib.NormedSpace

#align_import from_mathlib.alg_norm_of_galois

/-!
# alg_norm_of_auto and alg_norm_of_galois

In the section `supr` we prove some lemmas about indexed supremums, which will be PRd to the
appropriate files in mathlib.

For the rest of the file, we let `K` be a nonarchimedean normed field and `L/K` be a finite
algebraic extension. In the comments, `‖ ⬝ ‖` denotes any power-multiplicative algebra norm on `L`
extending the norm  on `K`.

## Main Definitions

* `alg_norm_of_auto` : given `σ : L ≃ₐ[K] L`, the function `L → ℝ` sending `x : L` to `‖ σ x ‖` is
  an algebra norm on `K`.
* `alg_norm_of_galois` : the function `L → ℝ` sending `x : L` to the maximum of `‖ σ x ‖` over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`.

## Main Results
* `alg_norm_of_auto_is_pow_mul` : `alg_norm_of_auto` is power-multiplicative.
* `alg_norm_of_auto_is_nonarchimedean` : `alg_norm_of_auto` is nonarchimedean.
* `alg_norm_of_auto_extends` : `alg_norm_of_auto` extends the norm on `K`.
* `alg_norm_of_galois_is_pow_mul` : `alg_norm_of_galois` is power-multiplicative.
* `alg_norm_of_galois_is_nonarchimedean` : `alg_norm_of_galois` is nonarchimedean.
* `alg_norm_of_galois_extends` : `alg_norm_of_galois` extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

alg_norm_of_auto, alg_norm_of_galois, norm, nonarchimedean
-/


open scoped NNReal

noncomputable section

/-! ## supr
In this section we prove some lemmas about `supr`, most of them for real-valued functions. -/


section iSup

/--
If the function `f : ι → α` is bounded above and `a < f i` for some `i : ι`, then `a < supr f` -/
theorem lt_csupr_of_lt {α : Type _} {ι : Sort _} [ConditionallyCompleteLattice α] {a : α}
    {f : ι → α} (H : BddAbove (Set.range f)) (i : ι) (h : a < f i) : a < iSup f :=
  lt_of_lt_of_le h (le_ciSup H i)

theorem csupr_univ {α β : Type _} [Fintype β] [ConditionallyCompleteLattice α] {f : β → α} :
    (⨆ (x : β) (_ : x ∈ (Finset.univ : Finset β)), f x) = ⨆ x : β, f x := by
  simp only [Finset.mem_univ, ciSup_pos]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem csupr₂_le {ι : Sort _} [Nonempty ι] {κ : ι → Prop} {α : Type _}
    [ConditionallyCompleteLinearOrderBot α] {f : ∀ i, κ i → α} {a : α} (h : ∀ i j, f i j ≤ a) :
    (⨆ (i) (j), f i j) ≤ a := by
  apply ciSup_le
  intro x
  by_cases hx : κ x
  · haveI : Nonempty (κ x) := ⟨hx⟩
    exact ciSup_le fun hx' => h _ _
  · rw [← iff_false_iff] at hx
    simp only [hx, ciSup_false, bot_le]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_csupr₂_of_le' {ι : Sort _} [Finite ι] {κ : ι → Prop} {α : Type _}
    [ConditionallyCompleteLinearOrderBot α] {f : ∀ i, κ i → α} {a : α} (i : ι) (j : κ i)
    (h : a ≤ f i j) : a ≤ ⨆ (i) (j), f i j :=
  by
  apply le_ciSup_of_le _ i
  · apply le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range fun j : κ i => f i j)) j h
  · exact Set.Finite.bddAbove (Set.finite_range _)

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_csupr₂_of_le {ι : Sort _} {κ : ι → Prop} {α : Type _}
    [ConditionallyCompleteLinearOrderBot α] {f : ∀ i, κ i → α}
    (h_fin : (Set.range fun i : ι => ⨆ j : κ i, f i j).Finite) {a : α} (i : ι) (j : κ i)
    (h : a ≤ f i j) : a ≤ ⨆ (i) (j), f i j := by
  apply le_ciSup_of_le _ i
  · apply le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range fun j : κ i => f i j)) j h
  · apply Set.Finite.bddAbove h_fin

theorem Finset.sup_eq_csupr {α β : Type _} [Nonempty α] [ConditionallyCompleteLinearOrderBot β]
    (s : Finset α) (f : α → β) : s.sup f = ⨆ (a : α) (_ : a ∈ s), f a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    apply le_csupr₂_of_le _ a ha (le_refl (f a))
    have hrange : (Set.range fun a : α => ⨆ _ : a ∈ s, f a) ⊆
      (Set.range fun a : s => f a) ∪ {⊥} := by
      rintro y ⟨x, hxy⟩
      simp only [Set.mem_range, bot_eq_zero', Set.union_singleton, Set.mem_insert_iff] at y ⊢
      by_cases hx : x ∈ s
      · right; simp only [hx, ciSup_pos] at hxy ; exact ⟨⟨x, hx⟩, hxy⟩
      · left; simp only [hx, ciSup_false] at hxy ; exact hxy.symm
    exact Set.Finite.subset ((Set.range fun a : ↥s => f ↑a) ∪ {⊥}).toFinite hrange
  · exact csupr₂_le fun x => Finset.le_sup

/-- Given `f : ι → ℝ≥0` and `n : ℕ`, we have `(supr f)^n = supr (f^n)`. -/
theorem NNReal.iSup_pow {ι : Type _} [Nonempty ι] [Finite ι] (f : ι → ℝ≥0) (n : ℕ) :
    (⨆ i : ι, f i) ^ n = ⨆ i : ι, f i ^ n := by
  cases nonempty_fintype ι
  induction' n with n hn
  · simp only [pow_zero, ciSup_const]
  · rw [pow_succ, hn]
    apply le_antisymm
    · apply NNReal.iSup_mul_iSup_le
      intro i j
      by_cases hij : f i < f j
      · apply le_trans (mul_le_mul_right' (pow_le_pow_left' (le_of_lt hij) _) (f j))
        rw [← pow_succ]
        exact (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _))) j (le_refl _)
      · have h : f i ^ n * f j ≤ f i ^n.succ := by
          rw [pow_succ]
          apply mul_le_mul' (le_refl _) (le_of_not_lt hij)
        exact le_trans h <| le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) i <| le_refl _
    · have : Nonempty (Finset.univ : Finset ι) := Finset.nonempty_coe_sort.mpr Finset.univ_nonempty
      rw [← csupr_univ, ← Finset.sup_eq_csupr, ← csupr_univ, ← Finset.sup_eq_csupr,
        ← csupr_univ, ← Finset.sup_eq_csupr]
      simp only [pow_succ]
      apply Finset.sup_mul_le_mul_sup_of_nonneg <;> rintro i - <;> exact zero_le _

/-- If `f : ι → ℝ` and `g : ι → ℝ` are non-negative and `∀ i j, f i * g j ≤ a`, then
 `supr f * supr g ≤ a`. -/
theorem Real.iSup_hMul_iSup_le {ι : Type _} [Nonempty ι] {a : ℝ} {f g : ι → ℝ}
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) (H : ∀ i j, f i * g j ≤ a) :
    iSup f * iSup g ≤ a :=
  by
  rw [Real.iSup_mul_of_nonneg (Real.iSup_nonneg hg_nn)]
  apply ciSup_le
  intro i
  rw [Real.mul_iSup_of_nonneg (hf_nn _)]
  exact ciSup_le fun j => H i j

/-- If `f : ι → ℝ` and `g : ι → ℝ` are non-negative, then `supr (f*g) ≤ supr f * supr g`. -/
theorem Real.iSup_hMul_le_hMul_iSup_of_nonneg {ι : Type _} [Nonempty ι] [Finite ι] {f g : ι → ℝ}
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) : (⨆ i : ι, f i * g i) ≤ iSup f * iSup g :=
  by
  cases nonempty_fintype ι
  have hf : BddAbove (Set.range f) := Finite.bddAbove_range f
  have hg : BddAbove (Set.range g) := Finite.bddAbove_range g
  exact
    ciSup_le fun x => mul_le_mul (le_ciSup hf x) (le_ciSup hg x) (hg_nn x) (Real.iSup_nonneg hf_nn)

/-- Given a non-negative `f : ι → ℝ` and `n : ℕ`, we have `(supr f)^n = supr (f^n)`. -/
theorem Real.iSup_pow {ι : Type _} [Nonempty ι] [Finite ι] {f : ι → ℝ} (hf_nn : ∀ i, 0 ≤ f i)
    (n : ℕ) : (⨆ i : ι, f i) ^ n = ⨆ i : ι, f i ^ n := by
  cases nonempty_fintype ι
  induction' n with n hn
  · simp only [pow_zero, ciSup_const]
  · rw [pow_succ, hn]
    apply le_antisymm
    · refine' Real.iSup_hMul_iSup_le ((fun x => pow_nonneg (hf_nn x) n)) hf_nn _
      intro i j
      by_cases hij : f i < f j
      · have hj : f i ^n * f j ≤ f j ^ n.succ := by
          rw [pow_succ]
          exact mul_le_mul (pow_le_pow_left (hf_nn _) (le_of_lt hij) _) (le_refl _) (hf_nn _)
            (pow_nonneg (hf_nn _) _)
        exact le_trans hj (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) j (le_refl _))
      · have hi : f i ^ n * f j ≤ f i ^ n.succ := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left (le_of_not_lt hij) (pow_nonneg (hf_nn _) _)
        exact le_trans hi (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) i (le_refl _))
    · simp_rw [pow_succ]
      exact Real.iSup_hMul_le_hMul_iSup_of_nonneg (fun x => pow_nonneg (hf_nn x) n) hf_nn

end iSup

variable {K : Type _} [NormedField K] {L : Type _} [Field L] [Algebra K L]
  (h_alg : Algebra.IsAlgebraic K L) (h_fin : FiniteDimensional K L)

section algNormOfAuto

/-- Given a normed field `K`, a finite algebraic extension `L/K` and `σ : L ≃ₐ[K] L`, the function
`L → ℝ` sending `x : L` to `‖ σ x ‖`, where `‖ ⬝ ‖` is any power-multiplicative algebra norm on `L`
extending the norm on `K`, is an algebra norm on `K`. -/
def algNormOfAuto (hna : IsNonarchimedean (norm : K → ℝ)) (σ : L ≃ₐ[K] L) : AlgebraNorm K L
    where
  toFun x     := Classical.choose (finite_extension_pow_mul_seminorm h_fin hna) (σ x)
  map_zero'   := by simp only [map_eq_zero_iff_eq_zero, AddEquivClass.map_eq_zero_iff]
  add_le' x y := by simp only [map_add σ, map_add_le_add]
  neg' x      := by simp only [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp only [map_mul σ, map_mul_le_mul]
  smul' x y   := by simp only [map_smul σ, map_smul_eq_mul]
  eq_zero_of_map_eq_zero' x hx := (AddEquivClass.map_eq_zero_iff _).mp (eq_zero_of_map_eq_zero _ hx)

theorem algNormOfAuto_apply (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    algNormOfAuto h_fin hna σ x =
      Classical.choose (finite_extension_pow_mul_seminorm h_fin hna) (σ x) :=
  rfl

/-- The algebra norm `alg_norm_of_auto` is power-multiplicative. -/
theorem algNormOfAuto_isPowMul (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (algNormOfAuto h_fin hna σ) := by
  intro x n hn
  simp only [algNormOfAuto_apply, map_pow σ x n]
  exact (Classical.choose_spec (finite_extension_pow_mul_seminorm h_fin hna)).1 _ hn

/-- The algebra norm `alg_norm_of_auto` is nonarchimedean. -/
theorem algNormOfAuto_isNonarchimedean (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (algNormOfAuto h_fin hna σ) :=
  by
  intro x y
  simp only [algNormOfAuto_apply, map_add σ]
  exact (Classical.choose_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.2 _ _

/-- The algebra norm `alg_norm_of_auto` extends the norm on `K`. -/
theorem algNormOfAuto_extends (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    FunctionExtends (norm : K → ℝ) (algNormOfAuto h_fin hna σ) :=
  by
  intro r; simp only [algNormOfAuto_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.1 _

end algNormOfAuto

section algNormOfGalois

/-- The function `L → ℝ` sending `x : L` to the maximum of `alg_norm_of_auto h_fin hna σ` over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`. -/
def algNormOfGalois (hna : IsNonarchimedean (norm : K → ℝ)) : AlgebraNorm K L
    where
  toFun x := iSup fun σ : L ≃ₐ[K] L => algNormOfAuto h_fin hna σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y :=
    ciSup_le fun σ =>
      le_trans (map_add_le_add (algNormOfAuto h_fin hna σ) x y)
        (add_le_add (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (le_refl _))
          (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (le_refl _)))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y :=
    ciSup_le fun σ =>
      le_trans (map_mul_le_mul (algNormOfAuto h_fin hna σ) x y)
        (mul_le_mul (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (le_refl _))
          (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (le_refl _)) (apply_nonneg _ _)
          (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (apply_nonneg _ _)))
  eq_zero_of_map_eq_zero' x := by
    contrapose!
    exact fun hx =>
      ne_of_gt
        (lt_csupr_of_lt
          (Set.Finite.bddAbove
            (Set.range fun σ : L ≃ₐ[K] L => algNormOfAuto h_fin hna σ x).toFinite)
          AlgEquiv.refl (map_pos_of_ne_zero _ hx))
  smul' r x := by
    simp only [AlgebraNormClass.map_smul_eq_mul, NormedRing.toRingNorm_apply,
      Real.mul_iSup_of_nonneg (norm_nonneg _)]

@[simp]
theorem algNormOfGalois_apply (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    algNormOfGalois h_fin hna x = iSup fun σ : L ≃ₐ[K] L => algNormOfAuto h_fin hna σ x :=
  rfl

/-- The algebra norm `alg_norm_of_galois` is power-multiplicative. -/
theorem algNormOfGalois_isPowMul (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (algNormOfGalois h_fin hna) := by
  intro x n hn
  simp only [algNormOfGalois_apply]
  rw [Real.iSup_pow]
  exact iSup_congr fun σ => algNormOfAuto_isPowMul h_fin σ hna _ hn
  · exact fun σ => apply_nonneg (algNormOfAuto h_fin hna σ) x

/-- The algebra norm `alg_norm_of_galois` is nonarchimedean. -/
theorem algNormOfGalois_isNonarchimedean (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (algNormOfGalois h_fin hna) := fun x y =>
  ciSup_le fun σ =>
    le_trans ((algNormOfAuto_isNonarchimedean h_fin σ hna) x y)
      (max_le_max (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (le_refl _))
        (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) σ (le_refl _)))

/-- The algebra norm `alg_norm_of_galois` extends the norm on `K`. -/
theorem algNormOfGalois_extends (hna : IsNonarchimedean (norm : K → ℝ)) :
    FunctionExtends (norm : K → ℝ) (algNormOfGalois h_fin hna) := fun r => by
  rw [algNormOfGalois, ← AlgebraNorm.toFun_eq_coe]
  simp only [AlgebraNorm.toFun_eq_coe, algNormOfAuto_extends h_fin _ hna r, ciSup_const]

end algNormOfGalois
