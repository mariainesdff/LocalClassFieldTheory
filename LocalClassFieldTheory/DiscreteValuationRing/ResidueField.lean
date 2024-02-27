import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

#align_import discrete_valuation_ring.residue_field

/-! # The residue field of a DVR
In this file we consider a finite extension `L/K` of a discretely valued field `K`. By the results
in `discrete_valuation_ring.basic`, the unit ball `K₀` is a DVR and the main result we prove is that
(under the assumption that `L/K` is separable, currently needed to ensure that the integral closure
of `K₀` in `L` is finite over `K₀`, but that should potentially be removed), the residue field of
the integral closure of `K₀` in `L` is finite dimensional over the residue field of `K₀`. As a
consequence, when the residue field of `K₀` is finite, so is the residue field of `L₀`

## Main definitions
* `extendedMaxIdeal` The ideal in `L` extending the maximal ideal of `K₀.
* `quotient_linear_iso` The equivalence as vector spaces over the residue field of the base of
  * the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below;
    and
  * the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
  induced by the equality of the two ideals proved in `extended_eq_pow_ramification_index`
* `finite_residue_field_of_integral_closure` and `finite_residue_field_of_unit_ball` are the proofs
  that whenever `L/K` is separable, and the residue field of `K₀` is finite, so is also the residue
  field both of the integral closure of `K₀` in `L` and of the unit ball `L₀`.

## Main results
* `ramification_idx_maximal_ne_zero` The ramification index of the maximal ideal in the integral
  closure of `K₀` in `L` over the maximal ideal of `K₀` is non zero.
* `ramification_idx_extended_ne_zero` The ramification index of the extension of the maximal ideal
  of `K₀` to the ring of integers of `L`, over the maximal ideal of `K₀` is non zero.
* `extended_eq_pow_ramification_index` The equality between the the extension of the maximal ideal
  of `K₀` to the ring of integers of `L` and the `e`-th power of the maximal ideal in this integral
  closure, where `e ≠ 0` is the ramification index.
* `finite_dimensional_residue_field_of_integral_closure` When `L/K` is (finite and) separable, the
  residue field of the integral closure of `K₀` in `L` (or, equivalently, of `L₀` in view of the
  declaration `integral_closure_eq_integer`  proven in `discrete_valuation_ring.extensions`) is
  finite dimensional over the residue field of `K₀`.


## Implementation details
* `algebra_mod_power_e` is an `instance` while `algebra_mod_extended` is only a `definition`, turned
  into a `local instance`. This is because the type-class inference mechanism seems unable to find
  the second instance automatically even if it is marked as such, so it has sometimes to be called
  explicitely.
* To prove that the residue field of `L₀` is finite (under suitable assumptions) we first prove that
  the residue field of the integral closure of `K₀` in `L` is finite, and then we use
  `integral_closure_eq_integer` proven in `discrete_valuation_ring.extensions` to transfer this
  finiteness to `L₀`.
-/


open LocalRing Valuation Ideal

open scoped DiscreteValuation Classical

noncomputable section

universe u w

namespace DiscreteValuation

variable (K : Type u) [Field K] [hv : Valued K ℤₘ₀] (L : Type w) [Field L] [Algebra K L]

local notation "K₀" => hv.v.valuationSubring

-- Porting note: needed to add this to avoid timeouts
instance : Algebra ↥(integralClosure K₀ L) ↥(integralClosure K₀ L) := Algebra.id _

-- Porting note: needed to add this to avoid timeouts
instance : Module K₀ ↥(integralClosure K₀ L) := Algebra.toModule

-- Porting note: needed to add this to avoid timeouts
instance : CommSemiring ↥(integralClosure K₀ L) := inferInstance

-- Porting note: needed to add this to avoid timeouts
instance : AddCommGroup ↥(integralClosure K₀ L) := Ring.toAddCommGroup

-- Porting note: needed to add this to avoid timeouts
instance : IsDedekindDomain ↥(integralClosure K₀ L) := sorry

/-- The ideal in the ìntegers of `L` obtained by extending the maximal ideal of `K₀`-/
@[reducible]
def extendedMaxIdeal : Ideal (integralClosure K₀ L) :=
  map (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)

theorem extendedMaxIdeal_not_isUnit : ¬IsUnit (extendedMaxIdeal K L) := by
  have h₁ : Algebra.IsIntegral K₀ (integralClosure K₀ L) :=
    le_integralClosure_iff_isIntegral.mp (le_refl _)
  have h₂ : RingHom.ker (algebraMap K₀ (integralClosure K₀ L)) ≤ LocalRing.maximalIdeal K₀ :=
    LocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ_max, hQ⟩ :=
    exists_ideal_over_maximal_of_isIntegral h₁ (LocalRing.maximalIdeal K₀) h₂
  rw [extendedMaxIdeal, ← hQ, isUnit_iff]
  exact ne_top_of_le_ne_top hQ_max.ne_top map_comap_le

variable [IsDiscrete hv.v]

theorem extendedMaxIdeal_ne_zero : extendedMaxIdeal K L ≠ 0 := by
  obtain ⟨π, hπ⟩ := DiscreteValuation.exists_Uniformizer_ofDiscrete hv.v
  rw [extendedMaxIdeal, Ideal.map, Ne.def, zero_eq_bot, span_eq_bot]
  simp only [Set.mem_image, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, exists_prop]
  use π, Uniformizer_not_isUnit hv.v hπ
  rw [map_eq_zero_iff _, ← Subring.coe_eq_zero_iff]
  exact Uniformizer_ne_zero hv.v hπ
  · exact NoZeroSMulDivisors.algebraMap_injective _ _

variable [FiniteDimensional K L]

instance [IsSeparable K L] : IsNoetherian K₀ (integralClosure K₀ L) :=
  IsIntegralClosure.isNoetherian K₀ K L (integralClosure K₀ L)

variable [CompleteSpace K]

theorem ramificationIdx_maximal_neZero :
    NeZero
      (ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
        (LocalRing.maximalIdeal (integralClosure K₀ L))) := by

  apply NeZero.mk
  apply IsDedekindDomain.ramificationIdx_ne_zero (extendedMaxIdeal_ne_zero K L)
  · apply IsMaximal.isPrime'
  · apply LocalRing.le_maximalIdeal
    intro h
    apply extendedMaxIdeal_not_isUnit K L (isUnit_iff.mpr h)

-- Porting note: I made this an instance
instance ramificationIdx_extended_neZero :
    NeZero
      (ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
        (extendedMaxIdeal K L)) := by
  apply NeZero.mk
  apply ramificationIdx_ne_zero Nat.one_ne_zero
  · rw [pow_one, extendedMaxIdeal]
  · rw [← extendedMaxIdeal, one_add_one_eq_two, not_le]
    apply pow_lt_self
    apply extendedMaxIdeal_ne_zero
    · intro h
      rw [← isUnit_iff] at h
      exact extendedMaxIdeal_not_isUnit K L h
    exact le_refl _

/-- The residue field of `L` is an algebra over the residue field of `K`-/
noncomputable def algebraResidueFields :
    Algebra (ResidueField K₀) (ResidueField (integralClosure K₀ L)) := by
  letI : NeZero (ramificationIdx (algebraMap K₀ ↥(integralClosure (K₀) L))
      (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal ↥(integralClosure (K₀) L))) :=
    ramificationIdx_maximal_neZero K L
  apply Quotient.algebraQuotientOfRamificationIdxNeZero (algebraMap K₀ (integralClosure K₀ L))
    (LocalRing.maximalIdeal K₀) _

theorem extended_eq_pow_ramification_index :
    extendedMaxIdeal K L =
      LocalRing.maximalIdeal (integralClosure K₀ L) ^
        ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
          (LocalRing.maximalIdeal (integralClosure K₀ L)) :=  by
  have h : DiscreteValuationRing (integralClosure K₀ L) := inferInstance
  have := ((DiscreteValuationRing.TFAE (integralClosure K₀ L)
    (DiscreteValuationRing.not_isField _)).out 0 6).mp h
  obtain ⟨n, hn⟩ := this (extendedMaxIdeal K L) (extendedMaxIdeal_ne_zero K L)
  rw [hn]
  · apply congr_arg
    rw [ramificationIdx_spec]
    · exact le_of_eq hn
    · rw [not_le, ← extendedMaxIdeal, hn]
      apply pow_succ_lt_pow
      exact DiscreteValuationRing.not_a_field _

instance algebraModPowerE :
    Algebra (ResidueField K₀)
      (integralClosure K₀ L ⧸
        LocalRing.maximalIdeal (integralClosure K₀ L) ^
          ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
            (LocalRing.maximalIdeal (integralClosure K₀ L))) := by
  letI : NeZero
    (ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
      (LocalRing.maximalIdeal K₀)
      (LocalRing.maximalIdeal ↥(integralClosure K₀ L) ^
        ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
          (LocalRing.maximalIdeal  K₀)
          (LocalRing.maximalIdeal ↥(integralClosure K₀ L)))) := by
    rw [← extended_eq_pow_ramification_index]
    apply ramificationIdx_extended_neZero
  apply
    Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero (algebraMap K₀ (integralClosure K₀ L)) _ _


/-- The quotient of the ring of integers in `L` by the extension of the maximal ideal in `K₀` as an
algebra over the residue field of `K₀`-/
@[reducible]
def algebraModExtended : Algebra (ResidueField K₀) (integralClosure K₀ L ⧸ extendedMaxIdeal K L) :=
  by
  rw [extended_eq_pow_ramification_index]
  infer_instance

theorem algebraMap_comp_extended :
    @algebraMap (ResidueField K₀)
          (integralClosure K₀ L ⧸
            LocalRing.maximalIdeal (integralClosure K₀ L) ^
              ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
                (LocalRing.maximalIdeal (integralClosure K₀ L)))
          _ _ _ ∘
        Ideal.Quotient.mk (LocalRing.maximalIdeal K₀) =
      Ideal.Quotient.mk
          (LocalRing.maximalIdeal (integralClosure K₀ L) ^
            ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
              (LocalRing.maximalIdeal (integralClosure K₀ L))) ∘
        algebraMap K₀ (integralClosure K₀ L) :=
  rfl

theorem algebraMap_comp_power_e :
    @algebraMap (ResidueField K₀) (integralClosure K₀ L ⧸ extendedMaxIdeal K L) _ _
          (algebraModExtended K L) ∘
        Ideal.Quotient.mk (LocalRing.maximalIdeal K₀) =
      Ideal.Quotient.mk (extendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L) := by
  convert algebraMap_comp_extended K L using 4
  sorry
  /- any_goals rw [extended_eq_pow_ramification_index]
  · simp only [algebra_mod_extended]
    simp only [eq_mpr_eq_cast, ← cast_cast, cast_hEq] -/

attribute [local instance] algebraModExtended

theorem algebraMap_comp_power_e_apply (a : K₀) :
    (algebraMap (ResidueField K₀) (integralClosure K₀ L ⧸ extendedMaxIdeal K L))
        (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀) a) =
      Ideal.Quotient.mk (extendedMaxIdeal K L) (algebraMap K₀ (integralClosure K₀ L) a) := by
  sorry/- have :
    (algebraMap (residue_field K₀) (integralClosure K₀ L ⧸ extendedMaxIdeal K L) ∘
          Ideal.Quotient.mk (LocalRing.maximalIdeal K₀))
        a =
      (Ideal.Quotient.mk (extendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L)) a
  rwa [algebraMap_comp_power_e]
 -/

instance : SMul (ResidueField K₀)
    (↥(integralClosure K₀ L) ⧸ extendedMaxIdeal K L) := sorry

instance : SMul K₀ (↥(integralClosure K₀ L) ⧸ extendedMaxIdeal K L) := sorry

theorem scalar_tower_extended :
    IsScalarTower K₀ (ResidueField K₀) (integralClosure K₀ L ⧸ extendedMaxIdeal K L) := by
  sorry
  /- refine' IsScalarTower.of_algebraMap_eq fun a => _
  have algebra_map_comp :
    algebraMap K₀ (integralClosure K₀ L ⧸ extendedMaxIdeal K L) a =
      (Ideal.Quotient.mk (extendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L)) a :=
    by rfl
  have algebra_map_eq_quot_mk :
    algebraMap K₀ (residue_field K₀) a = (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) a := by rfl
  rw [algebra_map_comp, ← algebra_map_comp_power_e, algebra_map_eq_quot_mk] -/

instance : SMul (ResidueField K₀) (↥(integralClosure K₀ L) ⧸
    LocalRing.maximalIdeal ↥(integralClosure K₀ L) ^
      ramificationIdx (algebraMap K₀ ↥(integralClosure K₀ L))
    (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal ↥(integralClosure K₀ L))) := sorry

instance : SMul K₀ (↥(integralClosure K₀ L) ⧸
    LocalRing.maximalIdeal ↥(integralClosure K₀ L) ^
      ramificationIdx (algebraMap K₀ ↥(integralClosure K₀ L))
    (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal ↥(integralClosure K₀ L))) := sorry

theorem scalar_tower_power_e :
    IsScalarTower K₀ (ResidueField K₀)
      (integralClosure K₀ L ⧸
        LocalRing.maximalIdeal (integralClosure K₀ L) ^
          ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
            (LocalRing.maximalIdeal (integralClosure K₀ L))) := by
  sorry/- refine' IsScalarTower.of_algebraMap_eq fun a => _
  have algebra_map_comp :
    algebraMap K₀
        (integralClosure K₀ L ⧸
          LocalRing.maximalIdeal (integralClosure K₀ L) ^
            ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
              (LocalRing.maximalIdeal (integralClosure K₀ L)))
        a =
      (Ideal.Quotient.mk
            (LocalRing.maximalIdeal (integralClosure K₀ L) ^
              ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
                (LocalRing.maximalIdeal (integralClosure K₀ L))) ∘
          algebraMap K₀ (integralClosure K₀ L))
        a :=
    by rfl
  have algebra_map_eq_quot_mk :
      algebraMap K₀ (residue_field K₀) a = (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) a := by
    rfl
  rw [algebra_map_comp, ← algebra_map_comp_extended, algebra_map_eq_quot_mk] -/

instance : Module (ResidueField K₀) (↥(integralClosure K₀ L) ⧸ extendedMaxIdeal K L) := sorry

/-- The equivalence as vector spaces over the residue field of the base of
* the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below; and
* the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
induced by the equality of the two ideals proved in `extended_eq_pow_ramification_index` -/
noncomputable def quotientLinearIso :
    (integralClosure K₀ L ⧸ extendedMaxIdeal K L) ≃ₗ[ResidueField K₀]
      integralClosure K₀ L ⧸
        LocalRing.maximalIdeal (integralClosure K₀ L) ^
          ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
            (LocalRing.maximalIdeal (integralClosure K₀ L)) := by
  let f := (Submodule.quotEquivOfEq _ _ (extended_eq_pow_ramification_index K L)).restrictScalars K₀
  let g :
    integralClosure K₀ L ⧸ extendedMaxIdeal K L →ₗ[residue_field K₀]
      integralClosure K₀ L ⧸
        LocalRing.maximalIdeal (integralClosure K₀ L) ^
          ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
            (LocalRing.maximalIdeal (integralClosure K₀ L)) := by
    use fun x => f x
    · apply f.map_add
    · rintro ⟨a⟩ v
      simp only [Submodule.Quotient.quot_mk_eq_mk, quotient.mk_eq_mk, EmbeddingLike.apply_eq_iff_eq]
      have algebra_map_eq_quot_mk :
        algebraMap K₀ (residue_field K₀) a = (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) a := by
        rfl
      let scalar_tower_v := (scalar_tower_extended K L).1 a 1 v
      let scalar_tower_fv := (scalar_tower_power_e K L).1 a 1 (f v)
      rw [← Algebra.algebraMap_eq_smul_one a, one_smul, algebra_map_eq_quot_mk] at scalar_tower_v
        scalar_tower_fv
      rw [scalar_tower_v, RingHom.id_apply, scalar_tower_fv]
      apply f.map_smul
  have h : Function.Bijective g := by apply f.bijective
  use LinearEquiv.ofBijective g f.bijective

attribute [local instance] algebra_residue_fields

theorem finiteDimensional_pow [IsSeparable K L] :
    FiniteDimensional (ResidueField K₀)
      (map
          (Ideal.Quotient.mk
            (LocalRing.maximalIdeal (integralClosure K₀ L) ^
              ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
                (LocalRing.maximalIdeal (integralClosure K₀ L))))
          (LocalRing.maximalIdeal (integralClosure K₀ L) ^ 0) ⧸
        LinearMap.range
          (powQuotSuccInclusion (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
            (LocalRing.maximalIdeal (integralClosure K₀ L)) 0)) :=
  by
  have aux :
    FiniteDimensional.finrank (K₀ ⧸ LocalRing.maximalIdeal K₀)
        (integralClosure K₀ L ⧸ extendedMaxIdeal K L) =
      FiniteDimensional.finrank K L :=
    by
    apply
      @finrank_quotient_map K₀ _ (integralClosure K₀ L) _ (LocalRing.maximalIdeal K₀) _ K _ _ _ L _
        _ (integralClosure.isFractionRing_of_finite_extension K L) _ _ _ _ _ _ _ _ _ _
  have : FiniteDimensional (residue_field K₀) (integralClosure K₀ L ⧸ extendedMaxIdeal K L) :=
    by
    suffices 0 < FiniteDimensional.finrank K L
      by
      apply FiniteDimensional.finiteDimensional_of_finrank
      convert this using 1
      rw [← aux]
      congr 2
      apply Algebra.algebra_ext
      rintro ⟨a⟩
      simp only [Submodule.Quotient.quot_mk_eq_mk, quotient.mk_eq_mk,
        algebra_map_comp_power_e_apply K L a, ← quotient.algebra_map_quotient_map_quotient]
      rfl
    · rw [FiniteDimensional.finrank_pos_iff_exists_ne_zero]
      use 1
      apply one_ne_zero
  replace aux :
    FiniteDimensional (residue_field K₀)
      (map
        (Ideal.Quotient.mk
          (LocalRing.maximalIdeal (integralClosure K₀ L) ^
            ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
              (LocalRing.maximalIdeal (integralClosure K₀ L))))
        (LocalRing.maximalIdeal (integralClosure K₀ L) ^ 0))
  · rw [pow_zero, one_eq_top, Ideal.map_top]
    haveI := (quotient_linear_iso K L).FiniteDimensional
    apply
      (@Submodule.topEquiv (residue_field K₀)
            (integralClosure K₀ L ⧸
              LocalRing.maximalIdeal (integralClosure K₀ L) ^
                ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
                  (LocalRing.maximalIdeal (integralClosure K₀ L)))
            _ _ _).symm.FiniteDimensional
  exact @FiniteDimensional.finiteDimensional_quotient (residue_field K₀) _ _ _ _ aux _

theorem finiteDimensional_residueField_of_integralClosure [IsSeparable K L] :
    FiniteDimensional (ResidueField K₀) (ResidueField (integralClosure K₀ L)) :=
  by
  let alg := algebra_residue_fields K L
  dsimp only [residue_field] at alg
  letI := alg
  letI h0 := ramification_idx_maximal_ne_zero K L
  have zero_lt :
    0 <
      ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
        (LocalRing.maximalIdeal (integralClosure K₀ L)) :=
    by apply Nat.pos_of_ne_zero h0.1
  let surj :=
    quotient_range_pow_quot_succ_inclusion_equiv (algebraMap K₀ (integralClosure K₀ L))
      (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal (integralClosure K₀ L))
      (DiscreteValuationRing.not_a_field _) zero_lt
  apply
    @LinearEquiv.finiteDimensional (residue_field K₀) _ _ _ _ (residue_field (integralClosure K₀ L))
      _ _ surj (finite_dimensional_pow K L)

/-- The residue field of the integral closure of a DVR in a  finite, separable extension of a
fraction field of the DVR is finite if the residue field of the base is finite-/
noncomputable def finiteResidueFieldOfIntegralClosure [IsSeparable K L]
    (hres : Fintype (ResidueField K₀)) : Fintype (ResidueField (integralClosure K₀ L)) :=
  letI := finite_dimensional_residue_field_of_integral_closure K L
  Module.fintypeOfFintype
    (FiniteDimensional.finBasis (residue_field K₀) (residue_field (integralClosure K₀ L)))

/-- The residue field of the unit ball of a  finite, separable extension of a fraction field of a
DVR is finite if the residue field of the base is finite-/
noncomputable def finiteResidueFieldOfUnitBall [IsSeparable K L]
    (hres : Fintype (LocalRing.ResidueField K₀)) :
    Fintype (ResidueField (extendedValuation K L).ValuationSubring) :=
  @Fintype.ofEquiv _ _ (finiteResidueFieldOfIntegralClosure K L hres)
    (LocalRing.ResidueField.mapEquiv
        (RingEquiv.subringCongr
          (DiscreteValuation.Extension.integralClosure_eq_integer K L))).toEquiv

end DiscreteValuation
