/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.Fintype.Order
import Mathlib.FieldTheory.Fixed
import Mathlib.Analysis.Normed.Unbundled.FiniteExtension


/-!
# algNorm_of_auto and algNorm_of_galois

In the section `supr` we prove some lemmas about indexed supremums, which will be PRd to the
appropriate files in mathlib.

For the rest of the file, we let `K` be a nonarchimedean normed field and `L/K` be a finite
algebraic extension. In the comments, `‖ ⬝ ‖` denotes any power-multiplicative algebra norm on `L`
extending the norm  on `K`.

## Main Definitions

* `algNorm_of_auto` : given `σ : L ≃ₐ[K] L`, the function `L → ℝ` sending `x : L` to `‖ σ x ‖` is
  an algebra norm on `K`.
* `algNorm_of_galois` : the function `L → ℝ` sending `x : L` to the maximum of `‖ σ x ‖` over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`.

## Main Results
* `isPowMul_algNorm_of_auto` : `algNorm_of_auto` is power-multiplicative.
* `isNonarchimedean_algNorm_of_auto` : `algNorm_of_auto` is nonarchimedean.
* `algNorm_of_auto_extends` : `algNorm_of_auto` extends the norm on `K`.
* `isPowMul_algNorm_of_galois` : `algNorm_of_galois` is power-multiplicative.
* `isNonarchimedean_algNorm_of_galois` : `algNorm_of_galois` is nonarchimedean.
* `algNorm_of_galois_extends` : `algNorm_of_galois` extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

algNorm_of_auto, algNorm_of_galois, norm, nonarchimedean
-/


open scoped NNReal

noncomputable section

/-! ## supr
In this section we prove some lemmas about `supr`, most of them for real-valued functions. -/


section iSup

-- In PR #23178

--DONE [Mathlib.Order.ConditionallyCompleteLattice.Indexed]
/--
If the function `f : ι → α` is bounded above and `a < f i` for some `i : ι`, then `a < supr f` -/
theorem lt_ciSup_of_lt {α : Type*} {ι : Sort _} [ConditionallyCompleteLattice α] {a : α}
    {f : ι → α} (H : BddAbove (Set.range f)) (i : ι) (h : a < f i) : a < iSup f :=
  lt_of_lt_of_le h (le_ciSup H i)

/-DONE
 Mathlib.Order.ConditionallyCompleteLattice.Finset, -/
theorem Finset.ciSup_univ {α β : Type*} [Fintype β] [ConditionallyCompleteLattice α] {f : β → α} :
    (⨆ (x : β) (_ : x ∈ (Finset.univ : Finset β)), f x) = ⨆ x : β, f x := by
  simp only [Finset.mem_univ, ciSup_pos]

--DONE [Mathlib.Order.ConditionallyCompleteLattice.Indexed]
theorem ciSup₂_le {ι : Sort _} [Nonempty ι] {κ : ι → Prop} {α : Type*}
    [ConditionallyCompleteLinearOrderBot α] {f : ∀ i, κ i → α} {a : α} (h : ∀ i j, f i j ≤ a) :
    (⨆ (i) (j), f i j) ≤ a := by
  apply ciSup_le
  intro x
  by_cases hx : κ x
  · haveI : Nonempty (κ x) := ⟨hx⟩
    exact ciSup_le fun hx' ↦ h _ _
  · simp only [hx, ciSup_false, bot_le]

/- DONE
[Mathlib.Topology.EMetricSpace.Defs, Mathlib.Order.PartialSups,
 Mathlib.Order.Filter.Pointwise, Mathlib.Order.ConditionallyCompleteLattice.Finset,
 Mathlib.Order.LiminfLimsup, Mathlib.Data.NNReal.Basic, Mathlib.Algebra.MonoidAlgebra.Degree,
  Mathlib.Order.Filter.Ultrafilter.Basic, Mathlib.SetTheory.Cardinal.Pigeonhole,
   Mathlib.Topology.Order.LocalExtr]-/
/- theorem Finite.le_ciSup₂_of_le {ι : Sort _} [Finite ι] {κ : ι → Prop} {α : Type*}
    [ConditionallyCompleteLinearOrder α] {f : ∀ i, κ i → α} {a : α} (i : ι) (j : κ i)
    (h : a ≤ f i j) : a ≤ ⨆ (i) (j), f i j :=
  le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) i
    (le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range fun j : κ i ↦ f i j)) j h) -/

/- DONE [Mathlib.Topology.EMetricSpace.Defs, Mathlib.Order.PartialSups,
Mathlib.Order.Filter.Pointwise, Mathlib.Order.ConditionallyCompleteLattice.Finset,
Mathlib.Order.LiminfLimsup, Mathlib.Data.NNReal.Basic, Mathlib.Algebra.MonoidAlgebra.Degree,
Mathlib.Order.Filter.Ultrafilter.Basic, Mathlib.SetTheory.Cardinal.Pigeonhole,
 Mathlib.Topology.Order.LocalExtr]-/
theorem Set.Finite.le_ciSup₂_of_le {ι : Sort _} {κ : ι → Prop} {α : Type*}
    [ConditionallyCompleteLinearOrder α] {f : ∀ i, κ i → α}
    (h_fin : (Set.range fun i : ι ↦ ⨆ j : κ i, f i j).Finite) {a : α} (i : ι) (j : κ i)
    (h : a ≤ f i j) : a ≤ ⨆ (i) (j), f i j :=
  le_ciSup_of_le h_fin.bddAbove i
    (le_ciSup_of_le (Set.finite_range fun j : κ i ↦ f i j).bddAbove j h)

/-Mathlib.Order.ConditionallyCompleteLattice.Finset -/
theorem Finset.sup_eq_ciSup {α β : Type*} [Nonempty α] [ConditionallyCompleteLinearOrderBot β]
    (s : Finset α) (f : α → β) : s.sup f = ⨆ (a : α) (_ : a ∈ s), f a := by
  apply le_antisymm ?_ (ciSup₂_le fun x ↦ Finset.le_sup)
  · apply Finset.sup_le
    intro a ha
    apply Set.Finite.le_ciSup₂_of_le _ a ha (le_refl (f a))
    have hrange : (Set.range fun a : α ↦ ⨆ _ : a ∈ s, f a) ⊆
      (Set.range fun a : s ↦ f a) ∪ {⊥} := by
      rintro y ⟨x, hxy⟩
      simp only [Set.mem_range, bot_eq_zero', Set.union_singleton, Set.mem_insert_iff] at y ⊢
      by_cases hx : x ∈ s
      · right; simp only [hx, ciSup_pos] at hxy ; exact ⟨⟨x, hx⟩, hxy⟩
      · left; simp only [hx, ciSup_false] at hxy ; exact hxy.symm
    exact ((Set.range fun a : ↥s ↦ f ↑a) ∪ {⊥}).toFinite.subset hrange

-- This lemma is not used anywhere.
--[Mathlib.Analysis.Normed.Ring.Lemmas]
/-- Given `f : ι → ℝ≥0` and `n : ℕ`, we have `(supr f)^n = supr (f^n)`. -/
theorem NNReal.iSup_pow {ι : Type*} [Nonempty ι] [Fintype ι] (f : ι → ℝ≥0) (n : ℕ) :
    (⨆ i : ι, f i) ^ n = ⨆ i : ι, f i ^ n := by
  --cases nonempty_fintype ι
  induction n with
  | zero => simp only [pow_zero, ciSup_const]
  | succ n hn =>
    rw [pow_succ, hn]
    apply le_antisymm
    · apply NNReal.iSup_mul_iSup_le
      intro i j
      by_cases hij : f i < f j
      · exact le_trans (mul_le_mul_right' (pow_le_pow_left' (le_of_lt hij) n) (f j))
          ((le_ciSup_of_le (Set.finite_range _).bddAbove) j (le_refl _))
      · have h : f i ^ n * f j ≤ f i ^n.succ := mul_le_mul' (le_refl _) (le_of_not_lt hij)
        exact le_trans h <| le_ciSup_of_le (Set.finite_range _).bddAbove i <| le_refl _
    · have : Nonempty (Finset.univ : Finset ι) := Finset.nonempty_coe_sort.mpr Finset.univ_nonempty
      rw [← Finset.ciSup_univ, ← Finset.sup_eq_ciSup, ← Finset.ciSup_univ, ← Finset.sup_eq_ciSup,
        ← Finset.ciSup_univ, ← Finset.sup_eq_ciSup]
      simp only [pow_succ]
      exact Finset.sup_mul_le_mul_sup_of_nonneg (fun _ _ ↦ zero_le _) (fun _ _ ↦ zero_le _)

-- [Mathlib.Data.Real.Pointwise]
/-- If `f : ι → ℝ` and `g : ι → ℝ` are non-negative and `∀ i j, f i * g j ≤ a`, then
 `iSup f * iSup g ≤ a`. -/
theorem Real.iSup_mul_iSup_le_of_nonneg {ι : Type*} [Nonempty ι] {a : ℝ} {f g : ι → ℝ}
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) (H : ∀ i j, f i * g j ≤ a) :
    iSup f * iSup g ≤ a := by
  rw [Real.iSup_mul_of_nonneg (Real.iSup_nonneg hg_nn)]
  apply ciSup_le
  intro i
  rw [Real.mul_iSup_of_nonneg (hf_nn i)]
  exact ciSup_le fun j ↦ H i j

/-- If `f : ι → ℝ` and `g : ι → ℝ` are non-negative, then `supr (f*g) ≤ supr f * supr g`. -/
theorem Real.iSup_mul_le_mul_iSup_of_nonneg {ι : Type*} [Nonempty ι] [Finite ι] {f g : ι → ℝ}
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) : (⨆ i : ι, f i * g i) ≤ iSup f * iSup g :=
  ciSup_le fun x ↦ mul_le_mul (le_ciSup (Finite.bddAbove_range f) x)
    (le_ciSup (Finite.bddAbove_range g) x) (hg_nn x) (Real.iSup_nonneg hf_nn)

-- Try Mathlib.Data.Real.Archimedean
/- [Mathlib.Topology.EMetricSpace.Defs, Mathlib.Topology.Algebra.Order.LiminfLimsup,
Mathlib.Data.NNReal.Basic, Mathlib.Topology.Order.Real]-/
/-- Given a non-negative `f : ι → ℝ` and `n : ℕ`, we have `(supr f)^n = supr (f^n)`. -/
theorem Real.iSup_pow {ι : Type*} [Nonempty ι] [Finite ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (n : ℕ) : (⨆ i : ι, f i) ^ n = ⨆ i : ι, f i ^ n := by
  cases nonempty_fintype ι
  induction n with
  | zero => simp only [pow_zero, ciSup_const]
  | succ n hn =>
    rw [pow_succ, hn]
    apply le_antisymm _ (Real.iSup_mul_le_mul_iSup_of_nonneg (fun x ↦ pow_nonneg (hf x) n) hf)
    · refine Real.iSup_mul_iSup_le_of_nonneg ((fun x ↦ pow_nonneg (hf x) n)) hf ?_
      intro i j
      by_cases hij : f i < f j
      · have hj : f i ^n * f j ≤ f j ^ n.succ :=
          mul_le_mul (pow_le_pow_left₀ (hf _) (le_of_lt hij) _) (le_refl _) (hf _)
            (pow_nonneg (hf _) _)
        exact le_trans hj (le_ciSup_of_le (Set.finite_range _).bddAbove j (le_refl _))
      · have hi : f i ^ n * f j ≤ f i ^ n.succ :=
          mul_le_mul_of_nonneg_left (le_of_not_lt hij) (pow_nonneg (hf _) _)
        exact le_trans hi (le_ciSup_of_le (Set.finite_range _).bddAbove i (le_refl _))

end iSup

-- The rest of the file is in PR #23184

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]
  (h_fin : FiniteDimensional K L)
section algNorm_of_auto

/-- Given a normed field `K`, a finite algebraic extension `L/K` and `σ : L ≃ₐ[K] L`, the function
`L → ℝ` sending `x : L` to `‖ σ x ‖`, where `‖ ⬝ ‖` is any power-multiplicative algebra norm on `L`
extending the norm on `K`, is an algebra norm on `K`. -/
def algNorm_of_auto (hna : IsNonarchimedean (norm : K → ℝ)) (σ : L ≃ₐ[K] L) :
    AlgebraNorm K L where
  toFun x     := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna) (σ x)
  map_zero'   := by simp [map_eq_zero_iff_eq_zero, EmbeddingLike.map_eq_zero_iff]
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x      := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  smul' x y   := by simp [map_smul σ, map_smul_eq_mul]
  eq_zero_of_map_eq_zero' x hx := EmbeddingLike.map_eq_zero_iff.mp (eq_zero_of_map_eq_zero _ hx)

theorem algNorm_of_auto_apply (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    algNorm_of_auto h_fin hna σ x =
      Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
        (σ x) := rfl

/-- The algebra norm `algNorm_of_auto` is power-multiplicative. -/
theorem isPowMul_algNorm_of_auto (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (algNorm_of_auto h_fin hna σ) := by
  intro x n hn
  simp only [algNorm_of_auto_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna)).1 _ hn

/-- The algebra norm `algNorm_of_auto` is nonarchimedean. -/
theorem isNonarchimedean_algNorm_of_auto (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (algNorm_of_auto h_fin hna σ) := by
  intro x y
  simp only [algNorm_of_auto_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna)).2.2 _ _

/-- The algebra norm `algNorm_of_auto` extends the norm on `K`. -/
theorem algNorm_of_auto_extends (σ : L ≃ₐ[K] L) (hna : IsNonarchimedean (norm : K → ℝ)) (x : K) :
    (algNorm_of_auto h_fin hna σ) ((algebraMap K L) x) = ‖x‖ := by
  simp only [algNorm_of_auto_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hna)).2.1 _

end algNorm_of_auto

section algNorm_of_galois

/-- The function `L → ℝ` sending `x : L` to the maximum of `algNorm_of_auto h_fin hna σ` over
  all `σ : L ≃ₐ[K] L` is an algebra norm on `L`. -/
def algNorm_of_galois (hna : IsNonarchimedean (norm : K → ℝ)) : AlgebraNorm K L where
  toFun x := iSup fun σ : L ≃ₐ[K] L ↦ algNorm_of_auto h_fin hna σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ ↦ le_trans (map_add_le_add (algNorm_of_auto h_fin hna σ) x y)
    (add_le_add (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _))
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _)))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y := ciSup_le fun σ ↦ le_trans (map_mul_le_mul (algNorm_of_auto h_fin hna σ) x y)
    (mul_le_mul (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _))
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _)) (apply_nonneg _ _)
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (apply_nonneg _ _)))
  eq_zero_of_map_eq_zero' x := by
    contrapose!
    exact fun hx ↦ ne_of_gt (lt_ciSup_of_lt
      (Set.range fun σ : L ≃ₐ[K] L ↦ algNorm_of_auto h_fin hna σ x).toFinite.bddAbove
      AlgEquiv.refl (map_pos_of_ne_zero _ hx))
  smul' r x := by
    simp only [AlgebraNormClass.map_smul_eq_mul, NormedRing.toRingNorm_apply,
      Real.mul_iSup_of_nonneg (norm_nonneg _)]

@[simp]
theorem algNorm_of_galois_apply (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) :
    algNorm_of_galois h_fin hna x = iSup fun σ : L ≃ₐ[K] L ↦ algNorm_of_auto h_fin hna σ x :=
  rfl

/-- The algebra norm `algNorm_of_galois` is power-multiplicative. -/
theorem isPowMul_algNorm_of_galois (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsPowMul (algNorm_of_galois h_fin hna) := by
  intro x n hn
  rw [algNorm_of_galois_apply, algNorm_of_galois_apply, Real.iSup_pow
    (fun σ ↦ apply_nonneg (algNorm_of_auto h_fin hna σ) x)]
  exact iSup_congr fun σ ↦ isPowMul_algNorm_of_auto h_fin σ hna _ hn

/-- The algebra norm `algNorm_of_galois` is nonarchimedean. -/
theorem isNonarchimedean_algNorm_of_galois (hna : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (algNorm_of_galois h_fin hna) := fun x y ↦
  ciSup_le fun σ ↦ le_trans ((isNonarchimedean_algNorm_of_auto h_fin σ hna) x y)
    (max_le_max (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _))
      (le_ciSup_of_le (Set.finite_range _).bddAbove σ (le_refl _)))

/-- The algebra norm `algNorm_of_galois` extends the norm on `K`. -/
theorem algNorm_of_galois_extends (hna : IsNonarchimedean (norm : K → ℝ)) (x : K) :
    (algNorm_of_galois h_fin hna) (algebraMap K L x) = ‖x‖ := by
  rw [algNorm_of_galois, ← AlgebraNorm.toFun_eq_coe]
  simp [AlgebraNorm.toFun_eq_coe, algNorm_of_auto_extends h_fin _ hna x, ciSup_const]

end algNorm_of_galois
