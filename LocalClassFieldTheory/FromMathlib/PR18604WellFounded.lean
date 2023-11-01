/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.LocallyFinite
import Mathlib.Order.WellFoundedSet

#align_import from_mathlib.PR18604_well_founded

/-
# Main Result
The main result of this file is the lemma `bdd_below.well_founded_on_lt` showing that a subset of a
preorder is bounded from below if and only if the `<`-relation on it is well-founded.#check

### Note
This file is a PR to mathlib3, suggested by Yaël Dillies, that has not yet been merged. We
acknowledge their help and are thankful for their permission to use their on-going work in our
project.
-/
/-
# Main Result
The main result of this file is the lemma `bdd_below.well_founded_on_lt` showing that a subset of a
preorder is bounded from below if and only if the `<`-relation on it is well-founded.#check

### Note
This file is a PR to mathlib3, suggested by Yaël Dillies, that has not yet been merged. We
acknowledge their help and are thankful for their permission to use their on-going work in our
project.
-/
variable {α : Type _} {s : Set α} [Preorder α] [LocallyFiniteOrder α]

open Set

theorem BddBelow.wellFoundedOn_lt : BddBelow s → s.WellFoundedOn (· < ·) :=
  by
  rw [wellFoundedOn_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf

  apply infinite_range_of_injective f.injective <| Finite.subset _ _
  use Icc a (f 0)
  apply finite_Icc
  apply range_subset_iff.2
  intro n
  apply mem_Icc.2
  constructor
  · apply le_trans <| ha <| hf n
    apply antitone_iff_forall_lt.2
    exacts [fun a b hab => le_of_lt <| (@RelEmbedding.map_rel_iff (f := f) b a).2 hab, le_refl _]
  · apply le_trans (b := f 0)
    · apply antitone_iff_forall_lt (f := f).2
      · intro a b hab
        apply le_of_lt <| (@RelEmbedding.map_rel_iff (f := f) b a).2 hab
      · simp only [zero_le]
    simp only [le_refl]

theorem BddAbove.wellFoundedOn_gt (hs : BddAbove s) : s.WellFoundedOn (· > ·) :=
  hs.dual.wellFoundedOn_lt
