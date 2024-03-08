import LocalClassFieldTheory.DiscreteValuationRing.TrivialExtension
import LocalClassFieldTheory.MixedCharacteristic.Basic
import LocalClassFieldTheory.PadicCompare

#align_import mixed_characteristic.valuation

/-!
# The canonical valuation on a mixed characteristic local field

In this file we define the canonical valuation on a mixed characteristic local field, which is the
`discrete_valuation.extended_valuation` constructed from the `p`-adic valuation on `Q_p p`.

## Main Definitions
* `mixed_char_local_field.with_zero.valued` : the valued instance in a mixed characteristic local
  field, induced by the extension of the `p`-adic valuation.

##  Main Theorems
* `mixed_char_local_field.complete_space` : a mixed characteristic local field is a complete space.

* `mixed_char_local_field.valuation.is_discrete` : the canonical valuation in a mixed characteristic
  local field is discrete.

* `mixed_char_local_field.ring_of_integers.discrete_valuation_ring` : the ring of integers of a
  mixed characteristic local field is a discrete valuation ring.

## Implementation details
Note that when `K = Q_p p`, there are two valued instances on it : the one coming from the fact that
`Q_p p` is defined as the `adic_completion` of `ℚ` with respect to the ideal `(p)`, and the one
obtained by extending this valuation on `Q_p p` to its trivial field extension `Q_p p`.
These instances are mathematically equivalent, but not definitionally equal. However, the lemma
`discrete_valuation.extension.trivial_extension_eq_valuation` from the file
`discrete_valuation_ring.trivial_extension` allow us to easily translate between the two instances
on `Q_p p`, whenever the diamond comes up.

-/


noncomputable section

open PadicComparison DiscreteValuation DiscreteValuation.Extension IsDedekindDomain Multiplicative NNReal
  Padic' Polynomial Multiplicative IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid

open scoped MixedCharLocalField NNReal DiscreteValuation

variable (p : outParam ℕ) [hp : Fact p.Prime]

theorem Padic'.mem_integers_iff (y : Q_p p) : y ∈ 𝓞 p (Q_p p) ↔ ‖y‖ ≤ 1 := by
  let _ : IsIntegrallyClosed (Z_p p) := instIsIntegrallyClosed
  rw [MixedCharLocalField.mem_ringOfIntegers, IsIntegrallyClosed.isIntegral_iff,
    norm_le_one_iff_val_le_one]
  refine' ⟨fun h => _, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  · obtain ⟨x, hx⟩ := h
    rw [← hx, ← mem_adicCompletionIntegers]
    exact x.2

namespace MixedCharLocalField

variable (K : Type _) [Field K] [MixedCharLocalField p K]

/-- The valued instance in a mixed characteristic local field, induced by the extension of the
  `p`-adic valuation. -/
instance (priority := 100) WithZero.valued: Valued K ℤₘ₀ :=
  Extension.valued (Q_p p) K

/-- A mixed characteristic local field is a complete space. -/
instance (priority := 100) completeSpace : CompleteSpace K :=
  Extension.completeSpace (Q_p p) K

/-- The canonical valuation in a mixed characteristic local field is discrete. -/
instance valuation.IsDiscrete : Valuation.IsDiscrete (MixedCharLocalField.WithZero.valued p K).v :=
  Extension.isDiscrete_of_finite (Q_p p) K

/-- The ring of integers of a mixed characteristic local field is a discrete valuation ring. -/
instance : DiscreteValuationRing (𝓞 p K) :=
  integralClosure.discreteValuationRing_of_finite_extension (Q_p p) K

variable {p}

theorem valuation_p_ne_zero : Valued.v (p : K) ≠ (0 : ℤₘ₀) := by
  simp only [Ne.def, Valuation.zero_iff, Nat.cast_eq_zero, hp.1.ne_zero, not_false_iff]

/-- The ramification index of a mixed characteristic local field `K` is given by the
  additive valuation of the element `(p : K)`. -/
def ramificationIndex (K : Type _) [Field K] [MixedCharLocalField p K] : ℤ :=
  - (Multiplicative.toAdd (WithZero.unzero (valuation_p_ne_zero K)))

scoped notation "e" => MixedCharLocalField.ramificationIndex

variable (p)

/-- The local field `Q_p p` is unramified. -/
theorem is_unramified_qP : e (Q_p p) = 1 :=
  by
  rw [ramificationIndex, neg_eq_iff_eq_neg, ← toAdd_ofAdd (-1 : ℤ)]
  apply congr_arg
  rw [← WithZero.coe_inj, ← Padic'.valuation_p p, WithZero.coe_unzero, ←
    trivial_extension_eq_valuation (Q_p p)]
  rfl

/-- A ring equivalence between `Z_p p` and the valuation subring of `Q_p p` viewed as a mixed
  characteristic local field. -/
noncomputable def PadicInt.equivValuationSubring :
    Z_p p ≃+* ↥(MixedCharLocalField.WithZero.valued p (Q_p p)).v.valuationSubring
    where
  toFun x := by
    use x.1
    have heq :
      (MixedCharLocalField.WithZero.valued p (Q_p p)).v x.val =
        extendedValuation (Q_p p) (Q_p p) x.val :=
      by rfl
    rw [Valuation.mem_valuationSubring_iff, heq, trivial_extension_eq_valuation (Q_p p)]
    exact x.2
  invFun x := by
    use x.1
    rw [Valuation.mem_valuationSubring_iff, ← trivial_extension_eq_valuation (Q_p p)]
    exact x.2
  left_inv x := by simp only [SetLike.eta]
  right_inv x := by simp only [SetLike.eta]
  map_mul' x y := by simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Submonoid.mk_mul_mk]
  map_add' x y := by simp only [Subsemiring.coe_add, AddMemClass.mk_add_mk]

variable {p}

theorem PadicInt.equivValuationSubring_comm :
    (algebraMap (MixedCharLocalField.WithZero.valued p (Q_p p)).v.valuationSubring K).comp
        (PadicInt.equivValuationSubring p).toRingHom =
      algebraMap (Z_p p) K :=
  rfl

end MixedCharLocalField
