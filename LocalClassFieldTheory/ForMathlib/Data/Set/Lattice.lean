import Mathlib.Data.Set.Lattice

#align_import for_mathlib.data.set.lattice

/-!
# Lattice
This file contains a technical lemma concerning intersections of Iio and Ico in linearly order
sets
-/


theorem set_inter_Iio {α β : Type _} [LinearOrder β] {X : β → Set α} {D N : β} (hND : N ≤ D) :
    (⋂ d ∈ Set.Iio D, X d) = (⋂ d ∈ Set.Iio N, X d) ∩ ⋂ d ∈ Set.Ico N D, X d :=
  by
  by_cases hND₀ : N = D
  · have : IsEmpty {d | D ≤ d ∧ d < D} := by
      simp only [Set.coe_setOf, isEmpty_subtype, not_and, not_lt, imp_self, imp_true_iff]
    have aux : (⋂ (d : β) (_ : D ≤ d ∧ d < D), X d) = Set.univ :=
      by
      erw [Set.biInter_eq_iInter {d | D ≤ d ∧ d < D} fun x _ => X x]
      apply Set.iInter_of_empty
    simp only [hND₀, Set.mem_Iio, Set.mem_Ico, aux, Set.inter_univ]
  · replace hND := lt_of_le_of_ne hND hND₀
    rw [← Set.iInter_inter_distrib, ← max_eq_right (le_refl D), ←
      Set.Iio_union_Ioo (min_lt_of_left_lt hND), max_eq_right (le_refl D)]
    congr with d
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ico, Set.mem_Ioo, Set.mem_iInter,
      Set.mem_inter_iff, and_imp]
    refine ⟨fun h b => ⟨fun H => h b <| Or.inl <| H.trans hND, fun _ h_ND => h b <| Or.inl h_ND⟩,
      fun h b H => ?_⟩
    rcases H with (Ha | Hb)
    by_cases H_bN : b < N
    exacts [(h b).1 H_bN, (h b).2 (le_of_not_lt H_bN) Ha, (h b).2 (le_of_lt Hb.1) Hb.2]
