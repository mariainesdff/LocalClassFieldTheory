/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Data.Set.Lattice

#align_import for_mathlib.data.set.lattice

-- *FAE* In PR 12961

/-!
# Lattice
This file contains a technical lemma concerning intersections of Iio and Ico in linearly order
sets
-/

open Set

theorem sInterIio_eq_sInterIio_inter_Ico {α β : Type _} [LinearOrder β] {X : β → Set α} {D N : β}
    (hND : N ≤ D) : (⋂ d ∈ Iio D, X d) = (⋂ d ∈ Iio N, X d) ∩ ⋂ d ∈ Ico N D, X d := by
  by_cases hND₀ : N = D
  · simp only [mem_Iio, hND₀, gt_iff_lt, lt_self_iff_false, not_false_eq_true, Ico_eq_empty,
      mem_empty_iff_false, iInter_of_empty, iInter_univ, inter_univ]
  · replace hND := lt_of_le_of_ne hND hND₀
    rw [← iInter_inter_distrib, ← max_eq_right (le_refl D), ← Iio_union_Ioo (min_lt_of_left_lt hND),
      max_eq_right (le_refl D)]
    congr with d
    simp only [mem_union, mem_Iio, mem_Ico, mem_Ioo, mem_iInter, mem_inter_iff, and_imp]
    refine ⟨fun h b => ⟨fun H => h b <| Or.inl <| H.trans hND, fun _ h_ND => h b <| Or.inl h_ND⟩,
      fun h b H => ?_⟩
    rcases H with (Ha | Hb)
    by_cases H_bN : b < N
    exacts [(h b).1 H_bN, (h b).2 (le_of_not_lt H_bN) Ha, (h b).2 (le_of_lt Hb.1) Hb.2]
