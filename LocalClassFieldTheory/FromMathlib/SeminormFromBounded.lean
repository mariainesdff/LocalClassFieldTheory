/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import LocalClassFieldTheory.FromMathlib.RingSeminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

#align_import from_mathlib.seminorm_from_bounded

/-!
# seminorm_from_bounded
In this file, we prove [BGR, Proposition 1.2.1/2] : given a nonzero additive group seminorm on a
commutative ring `R` such that for some positive `c : ℝ`,and every `x y : R`, the inequality
`f (x * y) ≤ c * f x * f y)` is satisfied, we create a ring seminorm on `R`.

In the file comments, we will use the expression `f is multiplicatively bounded` to indicate that
`∃ (c : ℝ) (_ : 0 < c), ∀ (x y : R), f (x * y) ≤ c * f x * f y`.


## Main Definitions

* `seminorm_from_bounded'` : the real-valued function sending `x ∈ R` to the supremum of
  `f(x*y)/f(y)`, where `y` runs over the elements of `R`.
* `seminorm_from_bounded` : the function `seminorm_from_bounded'` is a `ring_seminorm` on `R`.
* `norm_from_bounded` :`seminorm_from_bounded' f` is a ring_norm on `R`, provided that `f` is
  nonnegative, multiplicatively bounded and subadditive, that it preserves `0` and negation, and
  that `f` has trivial kernel.


## Main Results

* `seminorm_from_bounded_is_nonarchimedean` : if `f : R → ℝ` is a nonnegative, multiplicatively
  bounded, nonarchimedean function, then `seminorm_from_bounded' f` is nonarchimedean.
* `seminorm_from_bounded_of_mul_is_mul` : if `f : R → ℝ` is a nonnegative, multiplicatively bounded
  function and `x : R` is multiplicative for `f`, then `x` is multiplicative for
  `seminorm_from_bounded' f`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

seminorm_from_const, seminorm, nonarchimedean
-/


noncomputable section

open Function

open scoped Topology NNReal

namespace NormedGroupHom

/-- The inverse of `f : normed_add_group_hom V W` as a `normed_add_group_hom W V`. The map `f` must
  be bijective and bounded in the sense that `∃ (C : ℝ), ∀ v, ‖v‖ ≤ C * ‖f v‖`. -/
def normedGroupHomInvOfBijectiveBounded {V : Type _} {W : Type _} [SeminormedAddCommGroup V]
    [SeminormedAddCommGroup W] (f : NormedAddGroupHom V W) (h_bij : Bijective f)
    (h_bdd : ∃ C : ℝ, ∀ v, ‖v‖ ≤ C * ‖f v‖) : NormedAddGroupHom W V
    where
  toFun := invFun f
  map_add' :=
    (AddMonoidHom.inverse f.toAddMonoidHom (invFun f) (leftInverse_invFun h_bij.injective)
        (rightInverse_invFun h_bij.surjective)).map_add
  bound' := by
    obtain ⟨C, hC⟩ := h_bdd
    use C
    intro w
    set v := invFun f w
    rw [← rightInverse_invFun h_bij.surjective w]
    exact hC v

/-- The inverse of `f : normed_add_group_hom V W` is bijective and there exists a real `C` such that
 `∀ v : W, ‖v‖ ≤ C * ‖f v‖`, then the inverse of `f` is continuous. -/
theorem continuous_inv_of_bijective_bounded {V : Type _} {W : Type _} [SeminormedAddCommGroup V]
    [SeminormedAddCommGroup W] {f : NormedAddGroupHom V W} (h_bij : Bijective f)
    (h_bdd : ∃ C : ℝ, ∀ v, ‖v‖ ≤ C * ‖f v‖) : Continuous (invFun f) := by
  set g : NormedAddGroupHom W V :=
    { toFun := invFun f
      map_add' := fun x y => by
        rw [← (Classical.choose_spec (((bijective_iff_existsUnique _).mp h_bij) x)).1, ←
          (Classical.choose_spec (((bijective_iff_existsUnique _).mp h_bij) y)).1, ← map_add]
        simp only [← (invFun f).comp_apply, invFun_comp h_bij.injective, id_eq]
      bound' := by
        use Classical.choose h_bdd
        intro w
        rw [← (Classical.choose_spec (((bijective_iff_existsUnique _).mp h_bij) w)).1]
        simp only [← (invFun f).comp_apply, invFun_comp h_bij.injective, id_eq]
        exact Classical.choose_spec h_bdd _ }
  change Continuous g
  apply NormedAddGroupHom.continuous

/-- We regard a bijective `f : normed_add_group_hom V W` such that
  `∃ (C : ℝ), ∀ v, ‖v‖ ≤ C * ‖f v‖` as a homeomorphism. -/
def homeoOfBijectiveBounded {V : Type _} {W : Type _} [SeminormedAddCommGroup V]
    [SeminormedAddCommGroup W] {f : NormedAddGroupHom V W} (h_bij : Bijective f)
    (h_bdd : ∃ C : ℝ, ∀ v, ‖v‖ ≤ C * ‖f v‖) : Homeomorph V W where
  toFun             := f.toFun
  invFun            := invFun f.toFun
  left_inv          := leftInverse_invFun h_bij.injective
  right_inv         := rightInverse_invFun h_bij.surjective
  continuous_toFun  := f.continuous
  continuous_invFun := NormedGroupHom.continuous_inv_of_bijective_bounded h_bij h_bdd

end NormedGroupHom

variable {R : Type _} [CommRing R] (f : R → ℝ)

section seminormFromBounded

/-- The real-valued function sending `x ∈ R` to the supremum of  `f(x*y)/f(y)`, where `y` runs over
  the elements of `R`.-/
def seminormFromBounded' : R → ℝ := fun x => iSup fun y : R => f (x * y) / f y

variable {f}

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then `f 1 ≠ 0`. -/
theorem f_one_ne_zero (f_ne_zero : ∃ x : R, f x ≠ 0) (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_hc : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) : f 1 ≠ 0 :=
  by
  intro h1
  obtain ⟨c, _hc, hxy⟩ := f_mul
  specialize hxy 1
  simp_rw [h1, one_mul, MulZeroClass.mul_zero, MulZeroClass.zero_mul] at hxy
  obtain ⟨z, hz⟩ := f_ne_zero
  exact hz (le_antisymm (hxy z) (f_nonneg z))

/-- If `f : R → ℝ` is a nonnegative multiplicatively bounded function and `x : R` is a unit with
  `f x ≠ 0`, then for every `n : ℕ`, we have `f (x ^ n) ≠ 0`. -/
theorem f_pow_ne_zero (f_nonneg : ∀ x : R, 0 ≤ f x) {x : R} (hx : IsUnit x) (hfx : f x ≠ 0) (n : ℕ)
    (f_mul : ∃ (c : ℝ) (_hc : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) : f (x ^ n) ≠ 0 :=
  by
  have h1 : f 1 ≠ 0 := f_one_ne_zero (Exists.intro x hfx) f_nonneg f_mul
  intro hxn
  obtain ⟨c, _hc, hxy⟩ := f_mul
  obtain ⟨u, hu⟩ := hx
  specialize hxy (x ^ n) (u.inv ^ n)
  rw [hxn, MulZeroClass.mul_zero, MulZeroClass.zero_mul, ← mul_pow, ← hu, Units.inv_eq_val_inv,
    Units.mul_inv, one_pow] at hxy
  exact h1 (le_antisymm hxy (f_nonneg 1))

/-- `seminorm_from_bounded' f` preserves `0`. -/
theorem seminorm_from_bounded_zero (f_zero : f 0 = 0) : seminormFromBounded' f (0 : R) = 0 := by
  simp_rw [seminormFromBounded', MulZeroClass.zero_mul, f_zero, zero_div, ciSup_const]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  the image of `y ↦ f (x * y) / f y` is bounded above. -/
theorem seminorm_from_bounded_bdd_range (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    BddAbove (Set.range fun y => f (x * y) / f y) :=
  by
  obtain ⟨c, hc_pos, hxy⟩ := f_mul
  use c * f x
  rintro r ⟨y, hy⟩
  simp only [← hy]
  by_cases hy0 : f y = 0
  · rw [← hy0.symm, div_zero]
    apply mul_nonneg (le_of_lt hc_pos) (f_nonneg x)
  · simpa [div_le_iff (lt_of_le_of_ne (f_nonneg y) (Ne.symm hy0))] using hxy x y

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `seminorm_from_bounded' f x` is bounded above by some multiple of `f x`. -/
theorem seminorm_from_bounded_le (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x ≤ Classical.choose f_mul * f x := by
  apply ciSup_le
  intro y
  by_cases hy : 0 = f y
  · rw [← hy, div_zero]
    exact mul_nonneg (le_of_lt (Classical.choose (Classical.choose_spec f_mul))) (f_nonneg _)
  · rw [div_le_iff (lt_of_le_of_ne (f_nonneg _) hy)]
    exact (Classical.choose_spec (Classical.choose_spec f_mul)) x y

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `f x ≤ f 1 * seminorm_from_bounded' f x`. -/
theorem seminorm_from_bounded_ge (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    f x ≤ f 1 * seminormFromBounded' f x := by
  by_cases h1 : f 1 = 0
  · obtain ⟨c, _, hxy⟩ := f_mul
    specialize hxy x 1
    rw [mul_one, h1, MulZeroClass.mul_zero] at hxy
    have hx0 : f x = 0 := le_antisymm hxy (f_nonneg _)
    rw [hx0, h1, MulZeroClass.zero_mul]
  · rw [mul_comm, ← div_le_iff (lt_of_le_of_ne' (f_nonneg _) h1)]
    have h_bdd : BddAbove (Set.range fun y => f (x * y) / f y) :=
      seminorm_from_bounded_bdd_range f_nonneg f_mul x
    convert le_ciSup h_bdd (1 : R)
    rw [mul_one]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminorm_from_bounded' f` is nonnegative. -/
theorem seminorm_from_bounded_nonneg (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    0 ≤ seminormFromBounded' f x :=
  le_csSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) ⟨1, rfl⟩
    (div_nonneg (f_nonneg _) (f_nonneg _))

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then given `x y : R` with
  `f x = 0`, we have `f (x * y) = 0`. -/
theorem f_mul_zero_of_f_zero (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R} (hx : f x = 0)
    (y : R) : f (x * y) = 0 := by
  obtain ⟨c, _, hxy⟩ := f_mul
  specialize hxy x y
  rw [hx, MulZeroClass.mul_zero, MulZeroClass.zero_mul] at hxy
  exact le_antisymm hxy (f_nonneg _)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminorm_from_bounded' f x = 0` if and only if `f x = 0`. -/
theorem seminorm_from_bounded_eq_zero_iff (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x = 0 ↔ f x = 0 := by
  refine' ⟨fun h => _, fun h => _⟩
  · have hf := seminorm_from_bounded_ge f_nonneg f_mul x
    rw [h, MulZeroClass.mul_zero] at hf
    exact le_antisymm hf (f_nonneg _)
  · have hf : seminormFromBounded' f x ≤ Classical.choose f_mul * f x :=
      seminorm_from_bounded_le f_nonneg f_mul x
    rw [h, MulZeroClass.mul_zero] at hf
    exact le_antisymm hf (seminorm_from_bounded_nonneg f_nonneg f_mul x)

/-- If `f` is invariant under negation of `x`, then so is `seminorm_from_bounded'`.-/
theorem seminorm_from_bounded_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) :
    seminormFromBounded' f (-x) = seminormFromBounded' f x := by
  simp only [seminormFromBounded']
  congr; ext y
  rw [neg_mul, f_neg]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminorm_from_bounded' f` is submultiplicative. -/
theorem seminorm_from_bounded_mul (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) (x y : R) :
    seminormFromBounded' f (x * y) ≤ seminormFromBounded' f x * seminormFromBounded' f y := by
  apply ciSup_le
  by_cases hy : seminormFromBounded' f y = 0
  · rw [seminorm_from_bounded_eq_zero_iff f_nonneg f_mul] at hy
    intro z
    have hz : f (y * (x * z)) = 0 := f_mul_zero_of_f_zero f_nonneg f_mul hy (x * z)
    rw [mul_comm x y, mul_assoc, hz, zero_div]
    exact
      mul_nonneg (seminorm_from_bounded_nonneg f_nonneg f_mul x)
        (seminorm_from_bounded_nonneg f_nonneg f_mul y)
  · intro z
    rw [← div_le_iff (lt_of_le_of_ne' (seminorm_from_bounded_nonneg f_nonneg f_mul _) hy)]
    apply le_ciSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) z
    rw [div_le_iff (lt_of_le_of_ne' (seminorm_from_bounded_nonneg f_nonneg f_mul _) hy),
      div_mul_eq_mul_div]
    by_cases hz : f z = 0
    · have hxyz : f (z * (x * y)) = 0 := f_mul_zero_of_f_zero f_nonneg f_mul hz _
      simp_rw [mul_comm, hxyz, zero_div]
      exact
        div_nonneg (mul_nonneg (seminorm_from_bounded_nonneg f_nonneg f_mul y) (f_nonneg _))
          (f_nonneg _)
    · rw [div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))]
      by_cases hxz : f (x * z) = 0
      · have hxyz : f (x * z * y) = 0 := f_mul_zero_of_f_zero f_nonneg f_mul hxz y
        rw [mul_comm x y, mul_assoc, mul_comm y, hxyz]
        exact mul_nonneg (seminorm_from_bounded_nonneg f_nonneg f_mul y) (f_nonneg _)
      · rw [← div_le_iff (lt_of_le_of_ne' (f_nonneg _) hxz)]
        apply le_ciSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul y) (x * z)
        rw [div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hxz), mul_comm x y, mul_assoc]

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminorm_from_bounded' f 1 = 1`. -/
theorem seminorm_from_bounded_one_eq (f_ne_zero : ∃ x : R, f x ≠ 0) (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 = 1 := by
  simp_rw [seminormFromBounded', one_mul]
  have h_le : (⨆ y : R, f y / f y) ≤ 1 := by
    apply ciSup_le
    intro x; by_cases hx : f x = 0
    · rw [hx]; rw [div_zero]; exact zero_le_one
    · rw [div_self hx]
  have h_ge : 1 ≤ ⨆ y : R, f y / f y := by
    rw [← div_self (f_one_ne_zero f_ne_zero f_nonneg f_mul)]
    have h_bdd : BddAbove (Set.range fun y => f y / f y) :=
      by
      use(1 : ℝ)
      rw [mem_upperBounds]
      rintro r ⟨y, hy⟩
      simp_rw [← hy]
      by_cases hy : f y = 0
      · rw [hy, div_zero]; exact zero_le_one
      · rw [div_self hy]
    exact le_ciSup h_bdd (1 : R)
  exact le_antisymm h_le h_ge

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminorm_from_bounded' f 1 ≤ 1`. -/
theorem seminorm_from_bounded_is_norm_le_one_class (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 ≤ 1 := by
  by_cases f_ne_zero : ∃ x : R, f x ≠ 0
  · exact le_of_eq (seminorm_from_bounded_one_eq f_ne_zero f_nonneg f_mul)
  · simp_rw [seminormFromBounded', one_mul]
    apply ciSup_le
    intro x
    push_neg at f_ne_zero
    · rw [f_ne_zero x]; rw [div_zero]; exact zero_le_one

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function, then
  `seminorm_from_bounded' f` is subadditive. -/
theorem seminorm_from_bounded_add (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (x y : R) :
    seminormFromBounded' f (x + y) ≤ seminormFromBounded' f x + seminormFromBounded' f y := by
  apply ciSup_le
  intro z
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z + f (y * z) / f z by
    exact le_trans hf (add_le_add
      (le_ciSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) z (le_refl _))
      (le_ciSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul y) z (le_refl _)))
  by_cases hz : f z = 0
  · simp only [hz, div_zero, zero_add, le_refl, or_self_iff]
  · rw [div_add_div_same, div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul]
    exact f_add _ _

/-- `seminorm_from_bounded'` is a ring seminorm on `R`. -/
def seminormFromBounded (f_zero : f 0 = 0) (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) : RingSeminorm R
    where
  toFun := seminormFromBounded' f
  map_zero' := seminorm_from_bounded_zero f_zero
  add_le' := seminorm_from_bounded_add f_nonneg f_mul f_add
  mul_le' := seminorm_from_bounded_mul f_nonneg f_mul
  neg' := seminorm_from_bounded_neg f_neg

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, nonarchimedean function, then
  `seminorm_from_bounded' f` is nonarchimedean. -/
theorem seminorm_from_bounded_isNonarchimedean (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (hna : IsNonarchimedean f) : IsNonarchimedean (seminormFromBounded' f) := by
  intro x y
  apply ciSup_le
  intro z
  rw [le_max_iff]
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z ∨ f ((x + y) * z) / f z ≤ f (y * z) / f z by
    cases' hf with hfx hfy <;> [left; right]
    · exact le_ciSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) z hfx
    · exact le_ciSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul y) z hfy
  by_cases hz : f z = 0
  · simp only [hz, div_zero, le_refl, or_self_iff]
  · rw [div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz),
      div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff]
    exact hna _ _

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `seminorm_from_bounded' f x = f x`. -/
theorem seminorm_from_bounded_of_mul_apply (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded', hx, ← mul_div_assoc']
  have h_le : (⨆ y : R, f x * (f y / f y)) ≤ f x := by
    apply ciSup_le
    intro x; by_cases hx : f x = 0
    · rw [hx, div_zero, MulZeroClass.mul_zero]; exact f_nonneg _
    · rw [div_self hx, mul_one]
  have h_ge : f x ≤ ⨆ y : R, f x * (f y / f y) := by
    by_cases f_ne_zero : ∃ x : R, f x ≠ 0
    · conv_lhs => rw [← mul_one (f x)]
      rw [← div_self (f_one_ne_zero f_ne_zero f_nonneg f_mul)]
      have h_bdd : BddAbove (Set.range fun y => f x * (f y / f y)) :=
        by
        use f x
        rw [mem_upperBounds]
        rintro r ⟨y, hy⟩
        simp_rw [← hy]
        by_cases hy0 : f y = 0
        · rw [hy0, div_zero, MulZeroClass.mul_zero]; exact f_nonneg _
        · rw [div_self hy0, mul_one]
      exact le_ciSup h_bdd (1 : R)
    · push_neg at f_ne_zero
      simp_rw [f_ne_zero, zero_div, MulZeroClass.zero_mul, ciSup_const]; rfl
  exact le_antisymm h_le h_ge

/-- If `f : R → ℝ` is a nonnegative function and `x : R` is submultiplicative for `f`, then
  `seminorm_from_bounded' f x = f x`. -/
theorem seminorm_from_bounded_of_mul_le (f_nonneg : ∀ x : R, 0 ≤ f x) {x : R}
    (hx : ∀ y : R, f (x * y) ≤ f x * f y) (h_one : f 1 ≤ 1) : seminormFromBounded' f x = f x :=
  by
  simp_rw [seminormFromBounded']
  have h_le : (⨆ y : R, f (x * y) / f y) ≤ f x :=
    by
    apply ciSup_le
    intro y; by_cases hy : f y = 0
    · rw [hy, div_zero]; exact f_nonneg _
    · rw [div_le_iff (lt_of_le_of_ne' (f_nonneg _) hy)]; exact hx _
  have h_ge : f x ≤ ⨆ y : R, f (x * y) / f y :=
    by
    have h_bdd : BddAbove (Set.range fun y => f (x * y) / f y) :=
      by
      use f x
      rw [mem_upperBounds]
      rintro r ⟨y, hy⟩
      simp only [← hy]
      by_cases hy0 : f y = 0
      · rw [hy0, div_zero]
        exact f_nonneg _
      · rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc,
          div_le_iff (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one]
        exact hx y
    convert le_ciSup h_bdd (1 : R)
    by_cases h0 : f x = 0
    · rw [mul_one, h0, zero_div]
    · have heq : f 1 = 1 := by
        apply le_antisymm h_one
        specialize hx 1
        rw [mul_one, le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (Ne.symm h0))] at hx
        exact hx
      rw [heq, mul_one, div_one]
  exact le_antisymm h_le h_ge

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminorm_from_bounded' f` is nonzero. -/
theorem seminorm_from_bounded_ne_zero (f_ne_zero : ∃ x : R, f x ≠ 0) (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    ∃ x : R, seminormFromBounded' f x ≠ 0 :=
  by
  obtain ⟨x, hx⟩ := f_ne_zero
  use x
  rw [ne_eq, seminorm_from_bounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then the kernel of
  `seminorm_from_bounded' f` equals the kernel of `f`. -/
theorem seminorm_from_bounded_ker (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ⁻¹' {0} = f ⁻¹' {0} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact seminorm_from_bounded_eq_zero_iff f_nonneg f_mul x

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function that preserves
  zero and negation, then `seminorm_from_bounded' f` is a norm if and only if `f⁻¹' {0} = {0}`. -/
theorem seminormFromBounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) :
    (∀ x : R, (seminormFromBounded f_zero f_nonneg f_mul f_add f_neg).toFun x = 0 → x = 0) ↔
      f ⁻¹' {0} = {0} := by
  refine' ⟨fun h0 => _, fun h_ker => _⟩
  · rw [← seminorm_from_bounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h0 x h, fun h => by rw [h]; exact seminorm_from_bounded_zero f_zero⟩
  · intro x hx
    rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff, ←
      seminorm_from_bounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

/-- `seminorm_from_bounded' f` is a ring_norm on `R`, provided that `f` is nonnegative,
  multiplicatively bounded and subadditive, that it preserves `0` and negation, and that `f` has
  trivial kernel. -/
def normFromBounded (f_zero : f 0 = 0) (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x)
    (f_ker : f ⁻¹' {0} = {0}) : RingNorm R :=
  { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `x` is multiplicative for `seminorm_from_bounded' f`. -/
theorem seminorm_from_bounded_of_mul_is_mul (f_nonneg : ∀ x : R, 0 ≤ f x)
    (f_mul : ∃ (c : ℝ) (_ : 0 < c), ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromBounded' f (x * y) = seminormFromBounded' f x * seminormFromBounded' f y := by
  rw [seminorm_from_bounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

end seminormFromBounded
