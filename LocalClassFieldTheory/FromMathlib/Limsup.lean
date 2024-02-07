/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Order.Filter.ENNReal
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.NNReal

#align_import from_mathlib.limsup

/-!
# Limsup

We prove some auxiliary results about limsups, infis, and suprs.

## Main Results

* `ENNReal.le_infi_mul_infi` : if `f g : ι → ENNReal` take real values, and
  `∀ (i j : ι), a ≤ f i * g j`, then `a ≤ infi f * infi g`.
* `ENNReal.infi_mul_le_mul_infi` : if `u v : ι → ENNReal` take real values and are antitone, then
  `infi (u * v) ≤ infi u * infi v`.
* `ENNReal.limsup_mul_le` : if `u v : ℕ → ℝ≥0∞` are bounded above by real numbers, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top`.
* `Real.limsup_mul_le` : If `u v : ℕ → ℝ` are nonnegative and bounded above, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top `.

## Tags

limsup, Real, NNReal, ENNReal
-/


noncomputable section

namespace Filter

/-- If `u : β → α` is nonnegative and `isBoundedUnder has_le.le f u`, then `0 ≤ limsup u f`. -/
theorem limsup_nonneg_of_nonneg {α β : Type _} [Zero α] [ConditionallyCompleteLinearOrder α]
    {f : Filter β} [f.NeBot] {u : β → α} (hfu : IsBoundedUnder LE.le f u) (h : 0 ≤ u) :
    0 ≤ limsup u f :=
  le_limsup_of_frequently_le (frequently_of_forall h) hfu

/-- If `filter.limsup u at_top ≤ x`, then for all `ε > 0`, eventually we have `u a < x + ε`.  -/
theorem eventually_lt_add_pos_of_limsup_le {α : Type _} [Preorder α] {x : ℝ} {u : α → ℝ}
    (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : α in atTop, u a < x + ε :=
  eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

/-- If `filter.limsup u at_top ≤ x`, then for all `ε > 0`, there exists a positive natural
  number `n` such that `u n < x + ε`.  -/
theorem exists_lt_of_limsup_le {x : ℝ} {u : ℕ → ℝ} (hu_bdd : IsBoundedUnder LE.le atTop u)
    (hu : Filter.limsup u atTop ≤ x) {ε : ℝ} (hε : 0 < ε) : ∃ n : PNat, u n < x + ε := by
  have h : ∀ᶠ a : ℕ in atTop, u a < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε
  simp only [eventually_atTop, ge_iff_le] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

end Filter

open Filter

open scoped Topology NNReal ENNReal

theorem BddAbove.isBoundedUnder {α : Type _} [Preorder α] {u : α → ℝ}
    (hu_bdd : BddAbove (Set.range u)) : IsBoundedUnder LE.le atTop u := by
  obtain ⟨b, hb⟩ := hu_bdd
  use b
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact eventually_map.mpr (eventually_of_forall hb)

namespace NNReal

theorem coe_limsup {u : ℕ → ℝ} (hu : 0 ≤ u) :
    limsup u atTop = ((limsup (fun n => (⟨u n, hu n⟩ : ℝ≥0)) atTop : ℝ≥0) : ℝ) := by
  simp only [limsup_eq]
  norm_cast
  apply congr_arg
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  refine' ⟨fun hx => _, fun hx => _⟩
  · have hx' := hx
    simp only [eventually_atTop, ge_iff_le] at hx'
    obtain ⟨N, hN⟩ := hx'
    have hx0 : 0 ≤ x := le_trans (hu N) (hN N (le_refl _))
    exact ⟨⟨x, hx0⟩, hx, rfl⟩
  · obtain ⟨y, hy, hyx⟩ := hx
    simp_rw [← NNReal.coe_le_coe, NNReal.coe_mk, hyx] at hy
    exact hy

/-- If `u : ℕ → ℝ` is bounded above an nonnegative, it is also bounded above when regarded as
  a function to `ℝ≥0`. -/
theorem bdd_above' {u : ℕ → ℝ} (hu0 : 0 ≤ u) (hu_bdd : BddAbove (Set.range u)) :
    BddAbove (Set.range fun n : ℕ => (⟨u n, hu0 n⟩ : ℝ≥0)) := by
  obtain ⟨B, hB⟩ := hu_bdd
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hB
  have hB0 : 0 ≤ B := le_trans (hu0 0) (hB 0)
  use(⟨B, hB0⟩ : ℝ≥0)
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, Subtype.forall, Subtype.mk_le_mk]
  intros a _ n hn
  simp only [Subtype.mk.injEq] at hn
  rw [← hn]
  exact hB n

theorem eventually_le_of_bdd_above' {u : ℕ → ℝ≥0} (hu : BddAbove (Set.range u)) :
    {a : ℝ≥0 | ∀ᶠ n : ℕ in atTop, u n ≤ a}.Nonempty := by
  obtain ⟨B, hB⟩ := hu
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hB
  exact ⟨B, Set.mem_setOf_eq.mpr (eventually_of_forall hB)⟩

end NNReal

namespace ENNReal

/-- If `f g : ι → ℝ≥0∞` take real values, and `∀ (i j : ι), a ≤ f i * g j`, then
  `a ≤ infi f * infi g`. -/
theorem le_iInf_hMul_iInf {ι : Sort _} [hι : Nonempty ι] {a : ℝ≥0∞} {f g : ι → ℝ≥0∞}
    (hf : ∀ x, f x ≠ ⊤) (hg : ∀ x, g x ≠ ⊤) (H : ∀ i j : ι, a ≤ f i * g j) :
    a ≤ iInf f * iInf g := by
  have hg' : iInf g ≠ ⊤ := by rw [Ne.def, iInf_eq_top, not_forall]; exact ⟨hι.some, hg hι.some⟩
  rw [iInf_mul hg']
  refine' le_iInf _
  intro i
  rw [mul_iInf (hf i)]
  exact le_iInf (H i)

/-- If `u v : ι → ℝ≥0∞` take real values and are antitone, then `infi (u * v) ≤ infi u * infi v`. -/
theorem iInf_hMul_le_hMul_iInf {u v : ℕ → ℝ≥0∞} (hu_top : ∀ x, u x ≠ ⊤) (hu : Antitone u)
    (hv_top : ∀ x, v x ≠ ⊤) (hv : Antitone v) : iInf (u * v) ≤ iInf u * iInf v := by
  rw [iInf_le_iff]
  intro b hb
  apply le_iInf_hMul_iInf hu_top hv_top
  intro m n
  exact le_trans (hb (max m n)) (mul_le_mul' (hu (le_max_left _ _)) (hv (le_max_right _ _)))

theorem iSup_tail_seq (u : ℕ → ℝ≥0∞) (n : ℕ) :
    (⨆ (k : ℕ) (_ : n ≤ k), u k) = ⨆ k : { k : ℕ // n ≤ k }, u k := by rw [iSup_subtype]

theorem le_iSup_prop (u : ℕ → ℝ≥0∞) {n k : ℕ} (hnk : n ≤ k) : u k ≤ ⨆ (k : ℕ) (_ : n ≤ k), u k := by
  refine' le_iSup_of_le k _
  rw [ciSup_pos hnk]

/-- The function sending `n : ℕ` to `⨆ (k : ℕ) (x : n ≤ k), u k` is antitone. -/
theorem Antitone.iSup {u : ℕ → ℝ≥0∞} : Antitone fun n : ℕ => ⨆ (k : ℕ) (_ : n ≤ k), u k := by
  apply antitone_nat_of_succ_le _
  intro n
  rw [iSup₂_le_iff]
  intro k hk
  exact le_iSup_prop u (le_trans (Nat.le_succ n) hk)

/-- If `u : ℕ → ℝ≥0∞` is bounded above by a real number, then its `supr` is finite. -/
theorem iSup_le_top_of_bdd_above {u : ℕ → ℝ≥0∞} {B : ℝ≥0} (hu : ∀ x, u x ≤ B) (n : ℕ) :
    (⨆ (k : ℕ) (_ : n ≤ k), u k) ≠ ⊤ :=
  haveI h_le : (⨆ (k : ℕ) (_ : n ≤ k), u k) ≤ B :=
    by
    rw [iSup_tail_seq]
    exact iSup_le fun m => hu m
  ne_top_of_le_ne_top coe_ne_top h_le

/-- If `u v : ℕ → ℝ≥0∞` are bounded above by real numbers, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top`. -/
theorem limsup_mul_le' {u v : ℕ → ℝ≥0∞} {Bu Bv : ℝ≥0} (hu : ∀ x, u x ≤ Bu) (hv : ∀ x, v x ≤ Bv) :
    Filter.limsup (u * v) atTop ≤ Filter.limsup u atTop * Filter.limsup v atTop := by
  have h_le :
    (⨅ n : ℕ, ⨆ (i : ℕ) (_ : n ≤ i), u i * v i) ≤
      ⨅ n : ℕ, (⨆ (i : ℕ) (_ : n ≤ i), u i) * ⨆ (j : ℕ) (_ : n ≤ j), v j := by
    refine' iInf_mono _
    intro n
    apply iSup_le _
    intro k
    apply iSup_le _
    intro hk
    exact mul_le_mul' (le_iSup_prop u hk) (le_iSup_prop v hk)
  simp only [Filter.limsup_eq_iInf_iSup_of_nat, ge_iff_le, Pi.mul_apply]
  exact le_trans h_le
    (iInf_hMul_le_hMul_iInf (iSup_le_top_of_bdd_above hu) Antitone.iSup
      (iSup_le_top_of_bdd_above hv) Antitone.iSup)


theorem coe_limsup {u : ℕ → ℝ≥0} (hu : BddAbove (Set.range u)) :
    ((limsup u atTop : ℝ≥0) : ℝ≥0∞) = limsup (fun n => (u n : ℝ≥0∞)) atTop := by
  simp only [limsup_eq]
  rw [coe_sInf (NNReal.eventually_le_of_bdd_above' hu), sInf_eq_iInf]
  simp only [eventually_atTop, ge_iff_le, Set.mem_setOf_eq, iInf_exists]
  · apply le_antisymm
    · apply le_iInf₂ _
      intro x n
      apply le_iInf _
      intro h
      cases' x with x x
      · simp only [none_eq_top, le_top]
      · simp only [some_eq_coe, coe_le_coe] at h
        exact iInf₂_le_of_le x n (iInf_le_of_le h (le_refl _))
    · apply le_iInf₂ _
      intro x n
      apply le_iInf _
      intro h
      refine' iInf₂_le_of_le x n _
      simp_rw [coe_le_coe]
      exact iInf_le_of_le h (le_refl _)

theorem coe_limsup' {u : ℕ → ℝ} (hu : BddAbove (Set.range u)) (hu0 : 0 ≤ u) :
    limsup (fun n => ((↑⟨u n, hu0 n⟩ : ℝ≥0) : ℝ≥0∞)) atTop =
      ((↑⟨limsup u atTop, limsup_nonneg_of_nonneg hu.isBoundedUnder hu0⟩ : ℝ≥0) : ℝ≥0∞) := by
  rw [← ENNReal.coe_limsup (NNReal.bdd_above' hu0 hu), ENNReal.coe_inj, ← NNReal.coe_eq,
    NNReal.coe_mk, NNReal.coe_limsup]

end ENNReal

namespace Real

/-- If `u v : ℕ → ℝ` are nonnegative and bounded above, then `u * v` is bounded above. -/
theorem range_bddAbove_mul {u v : ℕ → ℝ} (hu : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv : BddAbove (Set.range v)) (hv0 : 0 ≤ v) : BddAbove (Set.range (u * v)) := by
  obtain ⟨bu, hbu⟩ := hu
  obtain ⟨bv, hbv⟩ := hv
  use bu * bv
  simp only [mem_upperBounds, Set.mem_range, Pi.mul_apply, forall_exists_index,
    forall_apply_eq_imp_iff] at hbu hbv ⊢
  intro n
  exact mul_le_mul (hbu n) (hbv n) (hv0 n) (le_trans (hu0 n) (hbu n))



/-- If `u v : ℕ → ℝ` are nonnegative and bounded above, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top `.-/
theorem limsup_mul_le {u v : ℕ → ℝ} (hu_bdd : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv_bdd : BddAbove (Set.range v)) (hv0 : 0 ≤ v) :
    Filter.limsup (u * v) atTop ≤ Filter.limsup u atTop * Filter.limsup v atTop := by
  have h_bdd : BddAbove (Set.range (u * v)) := range_bddAbove_mul hu_bdd hu0 hv_bdd hv0
  have hc :
    ∀ n : ℕ, (⟨u n * v n, mul_nonneg (hu0 n) (hv0 n)⟩ : ℝ≥0) = ⟨u n, hu0 n⟩ * ⟨v n, hv0 n⟩ := by
    intro n; simp only [Nonneg.mk_mul_mk]
  rw [NNReal.coe_limsup (mul_nonneg hu0 hv0), NNReal.coe_limsup hu0, NNReal.coe_limsup hv0, ←
    NNReal.coe_mul, NNReal.coe_le_coe, ← ENNReal.coe_le_coe, ENNReal.coe_mul,
    ENNReal.coe_limsup (NNReal.bdd_above' _ h_bdd),
    ENNReal.coe_limsup (NNReal.bdd_above' hu0 hu_bdd),
    ENNReal.coe_limsup (NNReal.bdd_above' hv0 hv_bdd)]
  simp only [Pi.mul_apply, hc, ENNReal.coe_mul]
  obtain ⟨Bu, hBu⟩ := hu_bdd
  obtain ⟨Bv, hBv⟩ := hv_bdd
  simp only [Nonneg.mk_mul_mk]
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    at hBu hBv
  have hBu_0 : 0 ≤ Bu := le_trans (hu0 0) (hBu 0)
  -- TODO: ask about this (Real.toNNReal might not be needed)
  have hBu' : ∀ n : ℕ, Real.toNNReal (u n) ≤ Real.toNNReal Bu := by
    intro n
    rw [Real.toNNReal_of_nonneg (hu0 n), Real.toNNReal_of_nonneg hBu_0]
    exact hBu n
  have hBv_0 : 0 ≤ Bv := le_trans (hv0 0) (hBv 0)
  have hBv' : ∀ n : ℕ, Real.toNNReal (v n) ≤ Real.toNNReal Bv := by
    intro n
    rw [Real.toNNReal_of_nonneg (hv0 n), Real.toNNReal_of_nonneg hBv_0]
    exact hBv n
  simp_rw [← ENNReal.coe_le_coe] at hBu' hBv'
  convert ENNReal.limsup_mul_le' hBu' hBv'
  · rw [Pi.mul_apply, ← Real.toNNReal_of_nonneg, Real.toNNReal_mul (hu0 _), ENNReal.coe_mul]
  · rw [Real.toNNReal_of_nonneg (hu0 _)]
  · rw [Real.toNNReal_of_nonneg (hv0 _)]

  /-
-- Alternative proof of limsup_mul_le
theorem limsup_mul_le {u v : ℕ → ℝ} (hu_bdd : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv_bdd : BddAbove (Set.range v)) (hv0 : 0 ≤ v) :
    Filter.limsup (u * v) atTop ≤ Filter.limsup u atTop * Filter.limsup v atTop := by
  have h_bdd : BddAbove (Set.range (u * v)) := range_bddAbove_mul hu_bdd hu0 hv_bdd hv0
  have hc :
    ∀ n : ℕ, (⟨u n * v n, mul_nonneg (hu0 n) (hv0 n)⟩ : ℝ≥0) = ⟨u n, hu0 n⟩ * ⟨v n, hv0 n⟩ := by
    intro n; simp only [Nonneg.mk_mul_mk]
  rw [← NNReal.coe_mk _ (limsup_nonneg_of_nonneg h_bdd.isBoundedUnder (mul_nonneg hu0 hv0)), ←
    NNReal.coe_mk _ (limsup_nonneg_of_nonneg hu_bdd.isBoundedUnder hu0), ←
    NNReal.coe_mk _ (limsup_nonneg_of_nonneg hv_bdd.isBoundedUnder hv0), ← NNReal.coe_mul,
    NNReal.coe_le_coe, ← ENNReal.coe_le_coe, ENNReal.coe_mul]
  rw [← ENNReal.coe_limsup', ← ENNReal.coe_limsup', ← ENNReal.coe_limsup']
  simp only [Pi.mul_apply, hc, ENNReal.coe_mul]
  obtain ⟨Bu, hBu⟩ := hu_bdd
  obtain ⟨Bv, hBv⟩ := hv_bdd
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    at hBu hBv
  have hBu_0 : 0 ≤ Bu := le_trans (hu0 0) (hBu 0)
  have hBu' : ∀ n : ℕ, (↑⟨u n, hu0 n⟩ : ℝ≥0) ≤ (↑⟨Bu, hBu_0⟩ : ℝ≥0) := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_mk]; exact hBu
  have hBv_0 : 0 ≤ Bv := le_trans (hv0 0) (hBv 0)
  have hBv' : ∀ n : ℕ, (↑⟨v n, hv0 n⟩ : ℝ≥0) ≤ (↑⟨Bv, hBv_0⟩ : ℝ≥0) := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_mk]; exact hBv
  --simp only [← ENNReal.coe_le_coe] at hBu' hBv'
  simp_rw [← NNReal.coe_le_coe/- , ← ENNReal.coe_le_coe -/] at hBu' hBv'
  --apply ENNReal.limsup_mul_le'

  --apply @ENNReal.limsup_mul_le' (fun n => ((↑⟨u n, hu0 n⟩ : ℝ≥0) : ℝ≥0∞))
  --  (fun n => ((↑⟨v n, hv0 n⟩ : ℝ≥0) : ℝ≥0∞)) (⟨Bu, hBu_0⟩ : ℝ≥0) (⟨Bv, hBv_0⟩ : ℝ≥0) hBu' hBv'
  sorry
  sorry
  sorry
  sorry

  --simp_rw [← ENNReal.coe_le_coe] at hBu' hBv'
  --exact ENNReal.limsup_mul_le hBu' hBv'
  /- simp only [← ENNReal.coe_limsup', Pi.mul_apply, hc, ENNReal.coe_mul]
  obtain ⟨Bu, hBu⟩ := hu_bdd
  obtain ⟨Bv, hBv⟩ := hv_bdd
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] at hBu
    hBv
  have hBu_0 : 0 ≤ Bu := le_trans (hu0 0) (hBu 0)
  have hBu' : ∀ n : ℕ, (⟨u n, hu0 n⟩ : ℝ≥0) ≤ (⟨Bu, hBu_0⟩ : ℝ≥0) := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_mk]; exact hBu
  have hBv_0 : 0 ≤ Bv := le_trans (hv0 0) (hBv 0)
  have hBv' : ∀ n : ℕ, (⟨v n, hv0 n⟩ : ℝ≥0) ≤ (⟨Bv, hBv_0⟩ : ℝ≥0) := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_mk]; exact hBv
  simp_rw [← ENNReal.coe_le_coe] at hBu' hBv'
  exact ENNReal.limsup_mul_le hBu' hBv' -/

-/

end Real
