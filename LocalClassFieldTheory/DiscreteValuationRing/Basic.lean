import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.ValuedField
import Mathlib.Topology.Algebra.WithZeroTopology
import LocalClassFieldTheory.ForMathlib.RankOneValuation
import LocalClassFieldTheory.ForMathlib.WithZero
import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.Integers

#align_import discrete_valuation_ring.basic

/-!
# Discrete Valuation Rings

In this file we prove basic results about Discrete Valuation Rings, building on the main definitions
provided in `ring_theory.discrete_valuation_ring.basic`. We focus in particular on discrete
valuations and on `valued` structures on the field of fractions of a DVR, as well as on a DVR
structure on the unit ball of a `valued` field whose valuation is discrete.

## Main Definitions
* `is_discrete`: We define a valuation to be discrete if it is ℤₘ₀-valued and surjective.
* `is_uniformizer`: Given a ℤₘ₀-valued valuation `v` on a ring `R`, an element `π : R` is a
  uniformizer if `v π = multiplicative.of_add (- 1 : ℤ) : ℤₘ₀`.
* `uniformizer`: A strucure bundling an element of a ring and a proof that it is a uniformizer.
* `base`: Given a valued field `K`, if the residue field of its unit ball (that is a local field)
  is finite, then `valuation_base` is the cardinal of the residue field, and otherwise it takes the
  value `6` which  is not a prime power.
* The `instance dvr_of_is_discrete` is the formalization of Chapter I, Section 1, Proposition 1 in
  Serre's **Local Fields** showing that the unit ball of a discretely-valued field is a DVR.


## Main Results
* `associated_of_uniformizer` An element associated to a uniformizer is itself a uniformizer
* `uniformizer_of_associated` If two elements are uniformizers, they are associated.
* `is_uniformizer_is_generator` A generator of the maximal ideal is a uniformizer if the valuation
  is discrete.
* `is_discrete_of_exists_uniformizer` If there exists a uniformizer, the valuation is discrete.
* `exists_uniformizer_of_discrete` Conversely, if the valuation is discrete there exists a
  uniformizer.
* `is_uniformizer_of_generator` A uniformizer generates the maximal ideal.
* `discrete_valuation.is_discrete` Given a DVR, the valuation induced on its ring of fractions is
  discrete.
* `discrete_valuation.dvr_equiv_unit_ball` The ring isomorphism between a DVR and the unit ball in
  its field of fractions endowed with the adic valuation of the maximal ideal.

## Implementation details
In the section `discrete_valuation` we put a `valued` instance only on `fraction_field A`, where
`A` is the DVR, and not on any field `L` such that `[is_fraction_field A L]` because this creates
loops in the type-class inference mechanism.
-/


open scoped DiscreteValuation NNReal

open Multiplicative

namespace Valuation

variable {A : Type _} [CommRing A]

theorem add_eq_max_of_ne {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation A Γ₀}
    {a b : A} (hne : v a ≠ v b) : v (a + b) = max (v a) (v b) :=
  by
  wlog hle : v b ≤ v a generalizing b a with H
  · rw [add_comm, max_comm]
    exact H hne.symm (le_of_lt (not_le.mp hle))
  · have hlt : v b < v a := lt_of_le_of_ne hle hne.symm
    have : v a ≤ max (v (a + b)) (v b) :=
      calc
        v a = v (a + b + -b) := by rw [add_neg_cancel_right]
        _ ≤ max (v (a + b)) (v (-b)) := (Valuation.map_add _ _ _)
        _ = max (v (a + b)) (v b) := by rw [Valuation.map_neg _ _]
    have hnge : v b ≤ v (a + b) := by
      apply le_of_not_gt
      intro hgt
      rw [max_eq_right_of_lt hgt] at this
      apply not_lt_of_ge this
      assumption
    have : v a ≤ v (a + b) := by rwa [max_eq_left hnge] at this
    apply le_antisymm
    · exact Valuation.map_add _ _ _
    · rw [max_eq_left_of_lt hlt]
      assumption

theorem add_eq_max_of_lt {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation A Γ₀}
    {a b : A} (hlt : v a < v b) : v (a + b) = max (v a) (v b) :=
  add_eq_max_of_ne (ne_of_lt hlt)

theorem mem_integer {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀) (a : A) :
    a ∈ v.integer ↔ v a ≤ 1 :=
  Iff.rfl

namespace Integer

theorem isUnit_iff_valuation_eq_one {K : Type _} [Field K] {Γ₀ : Type _}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (x : v.integer) : IsUnit x ↔ v x = 1 :=
  by
  refine'
    ⟨@integers.one_of_is_unit K Γ₀ _ _ v v.integer _ _ (Valuation.integer.integers v) _, fun hx =>
      _⟩
  have hx0 : (x : K) ≠ 0 := by
    by_contra h0
    rw [h0, map_zero] at hx
    exact zero_ne_one hx
  have hx' : v (x : K)⁻¹ = (1 : Γ₀) := by rw [map_inv₀, inv_eq_one]; exact hx
  rw [isUnit_iff_exists_inv]
  use(x : K)⁻¹
  · rw [mem_integer]
    exact le_of_eq hx'
  · ext; rw [Subring.coe_mul, SetLike.coe_mk, algebraMap.coe_one, mul_inv_cancel hx0]

theorem not_isUnit_iff_valuation_lt_one {K : Type _} [Field K] {Γ₀ : Type _}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (x : v.integer) :
    ¬IsUnit x ↔ v x < 1 :=
  by
  rw [← not_le, not_iff_not, is_unit_iff_valuation_eq_one, le_antisymm_iff]
  exact and_iff_right x.2

end Integer

/-- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `with_zero.multiplicative (- 1) : ℤₘ₀`-/
class IsDiscrete (v : Valuation A ℤₘ₀) : Prop where
  surj : Function.Surjective v

open Valuation Ideal Multiplicative WithZero

variable {R : Type _} [CommRing R] (vR : Valuation R ℤₘ₀)

/-- An element `π : R` is a uniformizer if `v π = multiplicative.of_add (- 1 : ℤ) : ℤₘ₀`.-/
def IsUniformizer (π : R) : Prop :=
  vR π = (Multiplicative.ofAdd (-1 : ℤ) : ℤₘ₀)

variable {vR}

theorem isUniformizer_iff {π : R} :
    IsUniformizer vR π ↔ vR π = (Multiplicative.ofAdd (-1 : ℤ) : ℤₘ₀) :=
  refl _

variable (vR)

/-- The structure `uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer.-/
@[ext]
structure Uniformizer where
  val : vR.integer
  valuationEqNegOne : IsUniformizer vR val

/-- A constructor for uniformizers.-/
def Uniformizer.mk' (x : R) (hx : IsUniformizer vR x) : Uniformizer vR
    where
  val :=
    ⟨x, by
      rw [mem_integer, is_uniformizer_iff.mp hx]
      exact le_of_lt WithZero.ofAdd_neg_one_lt_one⟩
  valuationEqNegOne := hx

@[simp]
instance : Coe (Uniformizer vR) vR.integer :=
  ⟨fun π => π.val⟩

@[simp]
theorem Uniformizer.val_eq_coe {π : Uniformizer vR} : (π : R) = π.val :=
  rfl

theorem isDiscreteOfExistsUniformizer {K : Type _} [Field K] (v : Valuation K ℤₘ₀) {π : K}
    (hπ : IsUniformizer v π) : IsDiscrete v :=
  by
  fconstructor
  intro x
  apply WithZero.cases_on x
  · exact ⟨0, Valuation.map_zero v⟩
  · rw [is_uniformizer] at hπ
    intro m
    use π ^ (-Multiplicative.toAdd m)
    rw [map_zpow₀, hπ, ← coe_zpow, coe_inj, ← ofAdd_zsmul, ← zsmul_neg', neg_neg, zsmul_one,
      Int.cast_id, ofAdd_toAdd]

theorem uniformizer_ne_zero {π : R} (hπ : IsUniformizer vR π) : π ≠ 0 :=
  by
  intro h0
  rw [h0, is_uniformizer, Valuation.map_zero] at hπ
  exact WithZero.zero_ne_coe hπ

theorem uniformizer_ne_zero' (π : Uniformizer vR) : π.1.1 ≠ 0 :=
  uniformizer_ne_zero vR π.2

theorem uniformizer_valuation_pos {π : R} (hπ : IsUniformizer vR π) : 0 < vR π := by
  rw [is_uniformizer_iff] at hπ ; simp only [zero_lt_iff, Ne.def, hπ, coe_ne_zero, not_false_iff]

theorem uniformizer_not_isUnit {π : vR.integer} (hπ : IsUniformizer vR π) : ¬IsUnit π :=
  by
  intro h
  have h1 :=
    @Valuation.Integers.one_of_isUnit R ℤₘ₀ _ _ vR vR.integer _ _ (Valuation.integer.integers vR) π
      h
  erw [is_uniformizer, h1] at hπ
  exact ne_of_gt of_add_neg_one_lt_one hπ

theorem uniformizer_valuation_lt_one {π : R} (hπ : IsUniformizer vR π) : vR π < 1 := by
  rw [is_uniformizer_iff.mp hπ]; exact of_add_neg_one_lt_one

open scoped NNReal

/-- If the residue field is finite, then `valuation_base` is the cardinal of the residue field, and
otherwise it takes the value `6` which is not a prime power.-/
noncomputable def base (K : Type _) [Field K] (v : Valuation K ℤₘ₀) : ℝ≥0 :=
  if 1 < Nat.card (LocalRing.ResidueField v.ValuationSubring) then
    Nat.card (LocalRing.ResidueField v.ValuationSubring)
  else 6

theorem one_lt_base (K : Type _) [Field K] (v : Valuation K ℤₘ₀) : 1 < base K v :=
  by
  rw [base]
  split_ifs with hlt hge
  · rw [Nat.one_lt_cast]; exact hlt
  · norm_num

theorem base_ne_zero (K : Type _) [Field K] (v : Valuation K ℤₘ₀) : base K v ≠ 0 :=
  ne_zero_of_lt (one_lt_base K v)

end Valuation

namespace DiscreteValuation

open Valuation Ideal Multiplicative WithZero LocalRing

-- is_dedekind_domain
variable {K : Type _} [Field K] (v : Valuation K ℤₘ₀)

/- When the valuation is defined on a field instead that simply on a (commutative) ring, we use the
notion of `valuation_subring` instead of the weaker one of `integer`s to access the corresponding
API. -/
local notation "K₀" => v.ValuationSubring

theorem uniformizerOfAssociated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁) (H : Associated π₁ π₂) :
    IsUniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  rwa [is_uniformizer_iff, ← hu, Subring.coe_mul, ← Units.val_eq_coe, Valuation.map_mul,
    (integer.is_unit_iff_valuation_eq_one u.1).mp u.is_unit, mul_one]

theorem associated_of_uniformizer {π₁ π₂ : Uniformizer v} : Associated π₁.1 π₂.1 :=
  by
  have hval : v ((↑π₁)⁻¹ * ↑π₂) = 1
  simp only [uniformizer.val_eq_coe, Valuation.map_mul, map_inv₀, is_uniformizer_iff.mp π₁.2,
    is_uniformizer_iff.mp π₂.2, ofAdd_neg, coe_inv, inv_inv, mul_inv_cancel, Ne.def, coe_ne_zero,
    not_false_iff]
  let p : v.integer := ⟨(↑π₁)⁻¹ * ↑π₂, (Valuation.mem_integer v _).mpr (le_of_eq hval)⟩
  use((integer.is_unit_iff_valuation_eq_one p).mpr hval).Unit
  apply_fun (coe : K₀ → K) using Subtype.val_injective
  simp only [Subring.coe_mul, IsUnit.unit_spec, SetLike.coe_mk, uniformizer.val_eq_coe, ← mul_assoc,
    mul_inv_cancel (uniformizer_ne_zero v π₁.2), one_mul]

theorem pow_uniformizer {r : K₀} (hr : r ≠ 0) (π : Uniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = π.1 ^ n * u :=
  by
  have hr₀ : v r ≠ 0 := by rw [Ne.def, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set m := -(unzero hr₀).toAdd with hm
  have hm₀ : 0 ≤ m :=
    by
    rw [hm, Right.nonneg_neg_iff, ← toAdd_one, to_add_le, ← coe_le_coe, coe_unzero]
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1 ^ (-m) * r) = 1 := by
    rw [Valuation.map_mul, map_zpow₀, is_uniformizer_iff.mp π.2, ofAdd_neg, coe_inv, inv_zpow',
      neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd, coe_inv,
      coe_unzero, inv_mul_cancel hr₀]
  set a : K₀ := ⟨π.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) ≠ 0 :=
    by
    simp only [ha, neg_neg, SetLike.coe_mk, Ne.def]
    by_cases h0 : to_add (unzero hr₀) = 0
    · rw [h0, zpow_zero, one_mul, Subring.coe_eq_zero_iff]; exact hr
    · apply mul_ne_zero
      · rw [Ne.def, zpow_eq_zero_iff h0]
        exact uniformizer_ne_zero' v π
      · rw [Ne.def, Subring.coe_eq_zero_iff]; exact hr
  have h_unit_a : IsUnit a :=
    integers.is_unit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  ext
  rw [IsUnit.unit_spec, Subring.coe_mul, Subring.coe_pow, Subtype.coe_mk, hn, ← mul_assoc, zpow_neg,
    zpow_ofNat, mul_inv_cancel, one_mul]
  apply pow_ne_zero
  exact uniformizer_ne_zero' _ π

/-- This proof of the lemma does not need the valuation to be discrete, although the fact that a
uniformizer exists forces the condition.-/
theorem uniformizer_is_generator (π : Uniformizer v) :
    maximalIdeal v.ValuationSubring = Ideal.span {π.1} :=
  by
  apply (maximal_ideal.is_maximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply uniformizer_not_is_unit v π.2 h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp only [hx₀, Ideal.zero_mem]
    · obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v hx₀ π
      have hn : Not (IsUnit x) := fun h =>
        (maximal_ideal.is_maximal _).ne_top (eq_top_of_is_unit_mem _ hx h)
      replace hn : n ≠ 0 := fun h => by rw [hu, h, pow_zero, one_mul] at hn ; exact hn u.is_unit
      simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using
        dvd_pow_self _ hn

theorem isUniformizer_is_generator {π : v.ValuationSubring} (hπ : IsUniformizer v π) :
    maximalIdeal v.ValuationSubring = Ideal.span {π} :=
  uniformizer_is_generator _ ⟨π, hπ⟩

theorem pow_uniformizer_is_pow_generator {π : Uniformizer v} (n : ℕ) :
    maximalIdeal v.ValuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow, uniformizer_is_generator]

variable [IsDiscrete v]

theorem exists_uniformizer_of_discrete : ∃ π : K₀, IsUniformizer v (π : K) :=
  by
  let surj_v : is_discrete v; infer_instance
  refine'
    ⟨⟨(surj_v.surj (Multiplicative.ofAdd (-1 : ℤ) : ℤₘ₀)).some, _⟩,
      (surj_v.surj (Multiplicative.ofAdd (-1 : ℤ) : ℤₘ₀)).choose_spec⟩
  rw [mem_valuation_subring_iff, (surj_v.surj (Multiplicative.ofAdd (-1 : ℤ) : ℤₘ₀)).choose_spec]
  exact le_of_lt of_add_neg_one_lt_one

instance : Nonempty (Uniformizer v) :=
  ⟨⟨(exists_uniformizer_of_discrete v).some, (exists_uniformizer_of_discrete v).choose_spec⟩⟩

theorem not_isField : ¬IsField K₀ :=
  by
  obtain ⟨π, hπ⟩ := exists_uniformizer_of_discrete v
  rintro ⟨-, -, h⟩
  have := uniformizer_ne_zero v hπ
  simp only [uniformizer_ne_zero v hπ, Ne.def, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact uniformizer_not_is_unit v hπ h

theorem isUniformizerOfGenerator {r : K₀} (hr : maximalIdeal v.ValuationSubring = Ideal.span {r}) :
    IsUniformizer v r :=
  by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact
      Ring.ne_bot_of_isMaximal_of_not_isField (maximal_ideal.is_maximal v.valuation_subring)
        (not_is_field v) hr
  obtain ⟨π, hπ⟩ := exists_uniformizer_of_discrete v
  obtain ⟨n, u, hu⟩ := pow_uniformizer v hr₀ ⟨π, hπ⟩
  rw [uniformizer_is_generator v ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact uniformizer_of_associated v hπ hr

theorem val_le_iff_dvd (L : Type _) [Field L] {w : Valuation L ℤₘ₀} [IsDiscrete w]
    [DiscreteValuationRing w.ValuationSubring] (x : w.ValuationSubring) (n : ℕ) :
    w x ≤ ofAdd (-(n : ℤ)) ↔ LocalRing.maximalIdeal w.ValuationSubring ^ n ∣ Ideal.span {x} :=
  by
  by_cases hx : x = 0
  ·
    simp_rw [ideal.span_singleton_eq_bot.mpr hx, hx, algebraMap.coe_zero, Valuation.map_zero,
      WithZero.zero_le, true_iff_iff, ← Ideal.zero_eq_bot, dvd_zero]
  · set r := Submodule.IsPrincipal.generator (LocalRing.maximalIdeal w.valuation_subring) with hr
    have hrn : w (r ^ n) = of_add (-(n : ℤ)) :=
      by
      simp only [Valuation.map_pow, ofAdd_neg, WithZero.coe_inv, inv_pow, inv_inj, ←
        WithZero.coe_pow, ← ofAdd_nsmul, Nat.smul_one_eq_coe]
      rw [WithZero.ofAdd_zpow, ← zpow_neg, ← Nat.cast_one, ← WithZero.ofAdd_neg_one_pow_comm (-n) 1,
        neg_neg, ← zpow_ofNat, ← zpow_ofNat, WithZero.ofAdd_pow_pow_comm, Nat.cast_one, zpow_one]
      congr
      rw [← is_uniformizer_iff]
      apply DiscreteValuation.isUniformizerOfGenerator
      rw [← Submodule.IsPrincipal.span_singleton_generator (maximal_ideal w.valuation_subring), ←
        hr]
      rfl
    have :=
      @Valuation.Integers.le_iff_dvd L ℤₘ₀ _ _ w w.valuation_subring _ _
        (Valuation.integer.integers w) x (r ^ n)
    erw [← hrn, this]
    rw [← Ideal.span_singleton_generator (LocalRing.maximalIdeal w.valuation_subring), ← hr,
      Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton', dvd_iff_exists_eq_mul_left]
    tauto

section RankOne

variable {K}

noncomputable instance isRankOne : IsRankOne v
    where
  hom := withZeroMultIntToNnreal (base_ne_zero K v)
  StrictMono := withZeroMultIntToNnreal_strictMono (one_lt_base K v)
  Nontrivial := by
    obtain ⟨π, hπ⟩ := exists_uniformizer_of_discrete v
    exact
      ⟨π, ne_of_gt (uniformizer_valuation_pos v hπ), ne_of_lt (uniformizer_valuation_lt_one v hπ)⟩

theorem isRankOne_hom_def : IsRankOne.hom v = withZeroMultIntToNnreal (base_ne_zero K v) :=
  rfl

end RankOne

theorem ideal_isPrincipal (I : Ideal K₀) : I.IsPrincipal :=
  by
  suffices : ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P
  exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π := (uniformizer.nonempty v).some
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v hx₀ π
    by_cases hn : n = 0
    · rw [hu, hn, pow_zero, one_mul] at hx_mem
      exact (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem u.is_unit)).elim
    · rw [hu, Ideal.mul_unit_mem_iff_mem P u.is_unit,
        is_prime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn), ← Ideal.span_singleton_le_iff_mem, ←
        uniformizer_is_generator v π] at hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (LocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      use⟨π.1, uniformizer_is_generator v π⟩

theorem integer_isPrincipalIdealRing : IsPrincipalIdealRing K₀ :=
  ⟨fun I => ideal_isPrincipal v I⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
instance dvr_of_isDiscrete : DiscreteValuationRing K₀
    where
  to_isPrincipalIdealRing := integer_isPrincipalIdealRing v
  to_localRing := inferInstance
  not_a_field' := by rw [Ne.def, ← is_field_iff_maximal_ideal_eq] <;> exact not_is_field v

variable (A : Type _) [CommRing A] [IsDomain A] [DiscreteValuationRing A]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Subring DiscreteValuationRing

/-- The maximal ideal of a DVR-/
def maximalIdeal : HeightOneSpectrum A
    where
  asIdeal := maximalIdeal A
  IsPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by
    simpa [Ne.def, ← is_field_iff_maximal_ideal_eq] using DiscreteValuationRing.not_isField A

variable {A}

noncomputable instance : Valued (FractionRing A) ℤₘ₀ :=
  (maximalIdeal A).adicValued

instance : IsDiscrete Valued.v :=
  isDiscreteOfExistsUniformizer Valued.v
    (valuation_exists_uniformizer (FractionRing A) (maximalIdeal A)).choose_spec

theorem exists_of_le_one {x : FractionRing A} (H : Valued.v x ≤ (1 : ℤₘ₀)) :
    ∃ a : A, algebraMap A (FractionRing A) a = x :=
  by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, ⟨b, ⟨hb, h_frac⟩⟩⟩ := @IsFractionRing.div_surjective A _ _ _ _ _ _ x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha, _root_.map_zero, zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    replace hb := (mul_mem_non_zero_divisors.mp hb).2
    erw [mul_comm ↑v _, _root_.map_mul _ ↑u _, _root_.map_mul _ _ ↑v, div_eq_mul_inv, mul_assoc,
      Valuation.map_mul, valuation_one_of_is_unit u.is_unit, one_mul, mul_inv, ← mul_assoc,
      Valuation.map_mul, map_inv₀, valuation_one_of_is_unit v.is_unit, inv_one, mul_one, ←
      div_eq_mul_inv, ← @IsFractionRing.mk'_mk_eq_div _ _ _ (FractionRing A) _ _ _ (π ^ n) _ hb,
      @valuation_of_mk' A _ _ _ (FractionRing A) _ _ _ (maximal_ideal A) (π ^ n) ⟨π ^ m, hb⟩,
      SetLike.coe_mk, Valuation.map_pow, Valuation.map_pow] at H
    have h_mn : m ≤ n :=
      by
      have π_lt_one :=
        (int_valuation_lt_one_iff_dvd (maximal_ideal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      rw [← int_valuation_apply] at π_lt_one
      have : (maximal_ideal A).intValuation π ≠ 0 := int_valuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← sub_nonneg]
      rw [← coe_unzero this, ← WithZero.coe_one] at H π_lt_one
      rw [div_eq_mul_inv, ← WithZero.coe_pow, ← WithZero.coe_pow, ← WithZero.coe_inv, ← zpow_ofNat,
        ← zpow_ofNat, ← WithZero.coe_mul, WithZero.coe_le_coe, ← zpow_sub, ← ofAdd_zero, ←
        ofAdd_toAdd (unzero _ ^ (↑n - ↑m)), of_add_le, Int.toAdd_zpow] at H
      apply nonneg_of_mul_nonpos_right H
      rwa [← toAdd_one, to_add_lt, ← WithZero.coe_lt_coe]
    use u * π ^ (n - m) * v.2
    simp only [← h_frac, Units.inv_eq_val_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebraMap A _) ↑u) _ _]
    congr 1
    rw [div_eq_mul_inv, mul_inv, mul_comm ((algebraMap A _) ↑v)⁻¹ _, ←
      mul_assoc _ _ ((algebraMap A _) ↑v)⁻¹]
    congr
    rw [pow_sub₀ _ _ h_mn]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exacts [hπ.ne_zero, valuation_le_one (maximal_ideal A), valuation_le_one (maximal_ideal A)]

theorem alg_map_eq_integers :
    Subring.map (algebraMap A (FractionRing A)) ⊤ = Valued.v.ValuationSubring.toSubring :=
  by
  ext
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨_, _, rfl⟩ := subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR and the unit ball in
  its field of fractions endowed with the adic valuation of the maximal ideal.-/
noncomputable def dvrEquivUnitBall :
    A ≃+* (@Valued.v (FractionRing A) _ ℤₘ₀ _ _).ValuationSubring :=
  topEquiv.symm.trans
    ((equivMapOfInjective _ (algebraMap A (FractionRing A)) (IsFractionRing.injective A _)).trans
      (RingEquiv.subringCongr alg_map_eq_integers))

end DiscreteValuation

namespace DiscretelyValued

open Valuation DiscreteValuation

variable (K : Type _) [Field K] [hv : Valued K ℤₘ₀]

/-- The definition of being a uniformizer for an element of a valued field-/
def IsUniformizer :=
  Valuation.IsUniformizer hv.V

/-- The structure `uniformizer` for a valued field-/
def Uniformizer :=
  Valuation.Uniformizer hv.V

instance [hv : Valued K ℤₘ₀] [IsDiscrete hv.V] : Nonempty (Uniformizer K) :=
  ⟨⟨(exists_uniformizer_of_discrete hv.V).some, (exists_uniformizer_of_discrete hv.V).choose_spec⟩⟩

end DiscretelyValued
