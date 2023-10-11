/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.LocallyFinite
import Order.WellFoundedSet

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
  rw [well_founded_on_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf
  exact
    infinite_range_of_injective f.injective
      ((finite_Icc a <| f 0).Subset <|
        range_subset_iff.2 fun n =>
          ⟨ha <| hf _,
            (antitone_iff_forall_lt.2 fun a b hab => (f.map_rel_iff.2 hab).le) <| zero_le _⟩)

theorem BddAbove.wellFoundedOn_gt (hs : BddAbove s) : s.WellFoundedOn (· > ·) :=
  hs.dual.wellFoundedOn_lt

