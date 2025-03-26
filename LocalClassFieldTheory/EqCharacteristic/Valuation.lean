/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import LocalClassFieldTheory.DiscreteValuationRing.TrivialExtension
import LocalClassFieldTheory.EqCharacteristic.Basic

/-!
# The canonical valuation on an equal characteristic local field

In this file we define the canonical valuation on an equal characteristic local field, which is the
`discrete_valuation.extended_valuation` constructed from the `X`-adic valuation on `FpX_completion`.

## Main Definitions
* `eq_char_local_field.with_zero.valued` : the valued instance in an equal characteristic local
  field, induced by the extension of the `X`-adic valuation.

##  Main Theorems
* `eq_char_local_field.complete_space` : an equal characteristic local field is a complete space.

* `eq_char_local_field.valuation.is_discrete` : the canonical valuation in an equal characteristic
  local field is discrete.

* `eq_char_local_field.ring_of_integers.discrete_valuation_ring` : the ring of integers of an
  equal characteristic local field is a discrete valuation ring.

## Implementation details
Note that when `K = FpX_completion`, there are two valued instances on it : the one coming from the
fact that `FpX_completion` is defined as the `adic_completion` of `ratfunc 𝔽_[p]` with respect to
the ideal `(X)`, and the one obtained by extending this valuation on `FpX_completion` to its trivial
field extension `FpX_completion`. These instances are mathematically equivalent, but not
definitionally equal. However `discrete_valuation.extension.trivial_extension_eq_valuation` from the
file `discrete_valuation_ring.trivial_extension` allow us to easily translate between the two
instances on `FpX_completion`, whenever this diamond comes up.

-/


noncomputable section

open DiscreteValuation IsDedekindDomain Multiplicative NNReal Polynomial RatFunc
  DiscreteValuation.Extension

open scoped EqCharLocalField NNReal DiscreteValuation

namespace EqCharLocalField

variable (p : outParam ℕ) [hp : Fact p.Prime]

variable (K : Type*) [Field K] [EqCharLocalField p K]

/-- The valued instance in an equal characteristic local field, induced by the extension of the
  `X`-adic valuation.-/
instance (priority := 100) WithZero.valued : Valued K ℤₘ₀ :=
  Extension.valued (FpXCompletion p) K

/-- An equal characteristic local field is a complete space. -/
instance (priority := 100) completeSpace : CompleteSpace K :=
  Extension.completeSpace (FpXCompletion p) K

/-- The canonical valuation in an equal characteristic local field is discrete. -/
instance valuation.isDiscrete : Valuation.IsDiscrete (EqCharLocalField.WithZero.valued p K).v :=
  Extension.isDiscrete_of_finite (FpXCompletion p) K

/-- The ring of integers of an equal characteristic local field is a discrete valuation ring. -/
instance : IsDiscreteValuationRing (𝓞 p K) :=
  integralClosure.discreteValuationRing_of_finite_extension (FpXCompletion p) K

variable {p}

theorem valuation_X_ne_zero : Valued.v (algebraMap (RatFunc 𝔽_[p]) K X) ≠ (0 : ℤₘ₀) := by
  simp only [ne_eq, _root_.map_eq_zero, RatFunc.X_ne_zero, not_false_iff]

/-- The ramification index of an equal characteristic local field `K` is given by the
  additive valuation of the element `(X : K)`. -/
def ramificationIndex (K : Type*) [Field K] [EqCharLocalField p K] : ℤ :=
  - toAdd (WithZero.unzero (valuation_X_ne_zero K))
  -- Porting note: dot notation doesn't work

scoped notation "e" => EqCharLocalField.ramificationIndex

variable (p)

/-- The local field `FpX_completion` is unramified. -/
theorem is_unramified_fpXCompletion : e (FpXCompletion p) = 1 := by
  have hX :
    (EqCharLocalField.WithZero.valued p (FpXCompletion p)).v (FpXCompletion.X p) =
      ofAdd (-1 : ℤ) := by
    have heq :
      (EqCharLocalField.WithZero.valued p (FpXCompletion p)).v =
        extendedValuation (FpXCompletion p) (FpXCompletion p) :=
      by rfl
    rw [← @FpXCompletion.valuation_X p _, FpXCompletion.X, FpXIntCompletion.X,
      EqCharLocalField.WithZero.valued, heq,
      DiscreteValuation.Extension.trivial_extension_eq_valuation]
    rfl
  rw [ramificationIndex, neg_eq_iff_eq_neg, ← toAdd_ofAdd (-1 : ℤ)]
  apply congr_arg
  rw [← WithZero.coe_inj, ← hX, WithZero.coe_unzero]
  rfl

/-- A ring equivalence between `FpX_int_completion` and the valuation subring of `FpX_completion`
viewed as an equal characteristic local field. -/
noncomputable def FpXIntCompletion.equivValuationSubring :
    FpXIntCompletion p ≃+*
      ↥(EqCharLocalField.WithZero.valued p (FpXCompletion p)).v.valuationSubring
    where
  toFun x := by
    use x.1
    have heq :
      (EqCharLocalField.WithZero.valued p (FpXCompletion p)).v x.val =
        extendedValuation (FpXCompletion p) (FpXCompletion p) x.val :=
      by rfl
    rw [Valuation.mem_valuationSubring_iff, heq, trivial_extension_eq_valuation (FpXCompletion p)]
    exact x.2
  invFun x := by
    use x.1
    rw [FpXIntCompletion, HeightOneSpectrum.mem_adicCompletionIntegers,
      ← trivial_extension_eq_valuation (FpXCompletion p)]
    exact x.2
  left_inv x   := by simp only [SetLike.eta]
  right_inv x  := by simp only [SetLike.eta]
  map_mul' x y := by simp only [MulMemClass.coe_mul, MulMemClass.mk_mul_mk]
  map_add' x y := by simp only [AddMemClass.coe_add, AddMemClass.mk_add_mk]

variable {p}

theorem FpXIntCompletion.equivValuationSubring_comm :
    (algebraMap (EqCharLocalField.WithZero.valued p (FpXCompletion p)).v.valuationSubring K).comp
        (FpXIntCompletion.equivValuationSubring p).toRingHom =
      algebraMap (FpXIntCompletion p) K :=
  rfl

end EqCharLocalField
