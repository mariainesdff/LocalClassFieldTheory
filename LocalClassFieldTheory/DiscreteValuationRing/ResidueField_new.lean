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
* `ExtendedMaxIdeal` The ideal in `L` extending the maximal ideal of `K₀.
* `quotient_linear_iso` The equivalence as vector spaces over the residue field of the base of
  * the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below;
    and
  * the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
  induced by the equality of the two ideals proved in `Extended_eq_powE`
* `finite_residue_field_of_integral_closure` and `finite_residue_field_of_unit_ball` are the proofs
  that whenever `L/K` is separable, and the residue field of `K₀` is finite, so is also the residue
  field both of the integral closure of `K₀` in `L` and of the unit ball `L₀`.

## Main results
* `ramification_idx_maximal_ne_zero` The ramification index of the maximal ideal in the integral
  closure of `K₀` in `L` over the maximal ideal of `K₀` is non zero.
* `ramification_idx_Extended_ne_zero` The ramification index of the extension of the maximal ideal
  of `K₀` to the ring of integers of `L`, over the maximal ideal of `K₀` is non zero.
* `Extended_eq_powE` The equality between the the extension of the maximal ideal
  of `K₀` to the ring of integers of `L` and the `e`-th power of the maximal ideal in this integral
  closure, where `e ≠ 0` is the ramification index.
* `finite_dimensional_residue_field_of_integral_closure` When `L/K` is (finite and) separable, the
  residue field of the integral closure of `K₀` in `L` (or, equivalently, of `L₀` in view of the
  declaration `integral_closure_eq_integer`  proven in `discrete_valuation_ring.extensions`) is
  finite dimensional over the residue field of `K₀`.


## Implementation details
* `algebra_mod_power_e` is an `instance` while `algebra_mod_Extended` is only a `definition`, turned
  into a `local instance`. This is because the type-class inference mechanism seems unable to find
  the second instance automatically even if it is marked as such, so it has sometimes to be called
  explicitely.
* To prove that the residue field of `L₀` is finite (under suitable assumptions) we first prove that
  the residue field of the integral closure of `K₀` in `L` is finite, and then we use
  `integral_closure_eq_integer` proven in `discrete_valuation_ring.extensions` to transfer this
  finiteness to `L₀`.
-/
set_option autoImplicit false


open LocalRing Valuation Ideal

open scoped DiscreteValuation Classical

noncomputable section

universe u w

namespace DiscreteValuation

variable (K : Type u) [Field K] [hv : Valued K ℤₘ₀] (L : Type w) [Field L] [Algebra K L]

local notation3 "K₀" => hv.v.valuationSubring
local notation3 "R" => integralClosure K₀ L
local notation3 "ℳ" => (LocalRing.maximalIdeal K₀)

-- Porting note: needed to add this to avoid timeouts
instance : Algebra ↥(integralClosure K₀ L) ↥(integralClosure K₀ L) := Algebra.id _

-- Porting note: needed to add this to avoid timeouts
instance : Module K₀ ↥(integralClosure K₀ L) := Algebra.toModule

-- Porting note: needed to add this to avoid timeouts
instance : CommSemiring ↥(integralClosure K₀ L) := inferInstance

-- Porting note: needed to add this to avoid timeouts
instance : AddCommGroup ↥(integralClosure K₀ L) := Ring.toAddCommGroup

variable [IsDiscrete hv.v]

variable [FiniteDimensional K L]

instance [IsSeparable K L] : IsNoetherian K₀ (integralClosure K₀ L) :=
  IsIntegralClosure.isNoetherian K₀ K L (integralClosure K₀ L)


variable [CompleteSpace K]

instance : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain _

/-- The ideal in the ìntegers of `L` obtained by extending the maximal ideal of `K₀`-/
@[reducible]
def ExtendedMaxIdeal : Ideal (integralClosure K₀ L) :=
  map (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)

theorem ExtendedMaxIdeal_not_isUnit : ¬IsUnit (ExtendedMaxIdeal K L) := by
  have h₁ : Algebra.IsIntegral K₀ (integralClosure K₀ L) :=
    le_integralClosure_iff_isIntegral.mp (le_refl _)
  have h₂ : RingHom.ker (algebraMap K₀ (integralClosure K₀ L)) ≤ LocalRing.maximalIdeal K₀ :=
    LocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ_max, hQ⟩ :=
    exists_ideal_over_maximal_of_isIntegral h₁ (LocalRing.maximalIdeal K₀) h₂
  rw [ExtendedMaxIdeal, ← hQ, isUnit_iff]
  exact ne_top_of_le_ne_top hQ_max.ne_top map_comap_le



theorem ExtendedMaxIdeal_ne_zero : ExtendedMaxIdeal K L ≠ 0 := by
  obtain ⟨π, hπ⟩ := DiscreteValuation.exists_Uniformizer_ofDiscrete hv.v
  rw [ExtendedMaxIdeal, Ideal.map, Ne.def, zero_eq_bot, span_eq_bot]
  simp only [Set.mem_image, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, exists_prop]
  use π, Uniformizer_not_isUnit hv.v hπ
  rw [map_eq_zero_iff _, ← Subring.coe_eq_zero_iff]
  exact Uniformizer_ne_zero hv.v hπ
  · exact NoZeroSMulDivisors.algebraMap_injective _ _

local notation3 "e'" => (ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
  (LocalRing.maximalIdeal K₀) (ExtendedMaxIdeal K L))

local notation3 "e" => (ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
  (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal (integralClosure K₀ L)))

theorem ramificationIdx_maximal_neZero :
    NeZero e := by
  apply NeZero.mk
  apply IsDedekindDomain.ramificationIdx_ne_zero (ExtendedMaxIdeal_ne_zero K L)
  · apply IsMaximal.isPrime'
  · apply LocalRing.le_maximalIdeal
    intro h
    apply ExtendedMaxIdeal_not_isUnit K L (isUnit_iff.mpr h)

-- Porting note: I made this an instance
-- *FAE* Probably useless
instance ramificationIdx_Extended_neZero :
    NeZero e' := by
  apply NeZero.mk
  apply ramificationIdx_ne_zero Nat.one_ne_zero
  · rw [pow_one, ExtendedMaxIdeal]
  · rw [← ExtendedMaxIdeal, one_add_one_eq_two, not_le]
    apply pow_lt_self
    apply ExtendedMaxIdeal_ne_zero
    · intro h
      rw [← isUnit_iff] at h
      exact ExtendedMaxIdeal_not_isUnit K L h
    exact le_refl _
/-

/- -- Porting note: needed to add this to avoid timeouts
instance : DiscreteValuationRing ↥(integralClosure K₀ L) :=
  DiscreteValuation.integralClosure.discreteValuationRing_of_finite_extension K L -/

-- Porting note: needed to add this to avoid timeouts
instance : IsDedekindDomain ↥(integralClosure K₀ L) := IsPrincipalIdealRing.isDedekindDomain _



-- Porting note: I made this an instance
instance ramificationIdx_Extended_neZero :
    NeZero e' := by
  apply NeZero.mk
  apply ramificationIdx_ne_zero Nat.one_ne_zero
  · rw [pow_one, ExtendedMaxIdeal]
  · rw [← ExtendedMaxIdeal, one_add_one_eq_two, not_le]
    apply pow_lt_self
    apply ExtendedMaxIdeal_ne_zero
    · intro h
      rw [← isUnit_iff] at h
      exact ExtendedMaxIdeal_not_isUnit K L h
    exact le_refl _

/-- The residue field of `L` is an algebra over the residue field of `K`-/
noncomputable def algebraResidueFields :
    Algebra (ResidueField K₀) (ResidueField (integralClosure K₀ L)) := by
  letI : NeZero e := ramificationIdx_maximal_neZero K L
  apply Quotient.algebraQuotientOfRamificationIdxNeZero (algebraMap K₀ (integralClosure K₀ L))
    (LocalRing.maximalIdeal K₀) _

@[simp]
theorem powE_eq_Extended :
    LocalRing.maximalIdeal (integralClosure K₀ L) ^ e = ExtendedMaxIdeal K L :=  by
  have := ((DiscreteValuationRing.TFAE (integralClosure K₀ L)
    (DiscreteValuationRing.not_isField _)).out 0 6).mp (by infer_instance)
  obtain ⟨n, hn⟩ := this (ExtendedMaxIdeal K L) (ExtendedMaxIdeal_ne_zero K L)
  rw [hn]
  · rw [ramificationIdx_spec]
    · exact le_of_eq hn
    · rw [not_le, ← ExtendedMaxIdeal, hn]
      apply pow_succ_lt_pow
      exact DiscreteValuationRing.not_a_field _


-- instance
def algebraMod_PowerE :
    Algebra (ResidueField K₀)
      (integralClosure K₀ L ⧸
        LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) := by
  let _ : NeZero
    (ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
      (LocalRing.maximalIdeal K₀)
      (LocalRing.maximalIdeal ↥(integralClosure K₀ L) ^
        ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
          (LocalRing.maximalIdeal  K₀)
          (LocalRing.maximalIdeal ↥(integralClosure K₀ L)))) := by
    rw [powE_eq_Extended]
    apply ramificationIdx_Extended_neZero
  apply
    Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero (algebraMap K₀ (integralClosure K₀ L)) _ _

--useless?
@[reducible]
def algebraInt_PowerE :
    Algebra K₀ (integralClosure K₀ L ⧸ LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) :=
  let _ : NeZero
    (ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
      (LocalRing.maximalIdeal K₀)
      (LocalRing.maximalIdeal ↥(integralClosure K₀ L) ^
        ramificationIdx (algebraMap K₀ (integralClosure K₀ L))
          (LocalRing.maximalIdeal  K₀)
          (LocalRing.maximalIdeal ↥(integralClosure K₀ L)))) := by
    rw [powE_eq_Extended]
    apply ramificationIdx_Extended_neZero
  letI algStructure := algebraMod_PowerE K L
  ((@algebraMap _ _ _ _ algStructure).comp (algebraMap K₀ _)).toAlgebra

  -- exact ((algebraMap _ _ _ _ algStructure).comp (algebraMap K₀ _)).toAlgebra
-- theorem algebraMap_comp_Extended :
--     @algebraMap (ResidueField K₀)
--           (integralClosure K₀ L ⧸
--             LocalRing.maximalIdeal (integralClosure K₀ L) ^
--               ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
--                 (LocalRing.maximalIdeal (integralClosure K₀ L)))
--           _ _ _ ∘
--         Ideal.Quotient.mk (LocalRing.maximalIdeal K₀) =
--       Ideal.Quotient.mk
--           (LocalRing.maximalIdeal (integralClosure K₀ L) ^
--             ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
--               (LocalRing.maximalIdeal (integralClosure K₀ L))) ∘
--         algebraMap K₀ (integralClosure K₀ L) :=
--   rfl

/-The following equality should rather be looked at as an equivalence of rings, since equality of
  type behaves poorly with respect to functions leaving from two equal types.-/
def ringEquiv_powE_Extended :
    ( (integralClosure K₀ L) ⧸ (LocalRing.maximalIdeal (integralClosure K₀ L) ^
      ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
      (LocalRing.maximalIdeal (integralClosure K₀ L)))) ≃+*
    ((integralClosure K₀ L) ⧸ (ExtendedMaxIdeal K L)) :=
  Ideal.quotEquivOfEq (powE_eq_Extended K L)

def ringEquiv_Extended_powE :
    ((integralClosure K₀ L) ⧸ (ExtendedMaxIdeal K L)) ≃+*
    (integralClosure K₀ L) ⧸ (LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) :=
  (ringEquiv_powE_Extended K L).symm

theorem ringEquiv_powE_Extended_symm :
  (ringEquiv_powE_Extended K L).symm = ringEquiv_Extended_powE K L := rfl

/-- The quotient of the ring of integers in `L` by the extension of the maximal ideal in `K₀` as an
algebra over the residue field of `K₀`-/
@[reducible]
def algebraMod_Extended :
    Algebra (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) :=
--*FAE* This was the old version, using the *equality* I now propose another one, using the
  -- above ring equivalence (induced by the identity...)
  -- rw [← powE_eq_Extended]
  -- infer_instance
  letI algStructure := algebraMod_PowerE K L
  ((ringEquiv_powE_Extended K L).toRingHom.comp (@algebraMap _ _ _ _ algStructure)).toAlgebra

@[reducible]
def algebraInt_Extended :
    Algebra K₀ (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) :=
  letI algStructure := algebraMod_PowerE K L
  (((ringEquiv_powE_Extended K L).toRingHom.comp (@algebraMap _ _ _ _ algStructure)).comp
    (algebraMap K₀ _)).toAlgebra

-- theorem algebraEquiv_powE_Extended :
--     letI := algebraModExtended K L
--     algebraMap (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) ∘
--       Ideal.Quotient.mk (LocalRing.maximalIdeal K₀) =
--     algebraMap (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) ∘
--       Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)
--     ∧
--      (Ideal.Quotient.mk (ExtendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L))
--      = (Ideal.Quotient.mk (ExtendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L)):= by
--   sorry
  -- let _ := algebraModExtended K L
  -- rw [Quot_powE_eq_Extended]
  -- have := algebraMap_comp_Extended K L
  -- have := @Quotient.algebraMap_quotient_of_ramificationIdx_neZero K₀ _ (integralClosure K₀ L) _
  --   (algebraMap K₀ (integralClosure K₀ L))
  --   (LocalRing.maximalIdeal K₀) (ExtendedMaxIdeal K L) ?_
  -- ext x
  -- replace this := this x
  -- simp only [Quotient.algebraMap_quotient_of_ramificationIdx_neZero, Quotient.mk_algebraMap,
    -- /- Subtype.forall, mem_valuationSubring_iff, implies_true, forall_const -/] at this
  -- simp only [Function.comp_apply, Quotient.mk_algebraMap]
  -- erw [← this]
  -- simp only [Quotient.algebraMap_quotient_of_ramificationIdx_neZero, Quotient.mk_algebraMap]
  -- exact?
  -- rw [Quot.eq]
  -- have aa := @Extended_eq_powE K _ _ L _ _ _ _ _
  -- erw [aa]
  -- rfl
  -- have : HEq (⇑(algebraMap (ResidueField K₀)
  --         (↥(integralClosure (K₀) L) ⧸ ExtendedMaxIdeal K L)) ∘
  --     ⇑(Ideal.Quotient.mk (LocalRing.maximalIdeal K₀))) ((algebraMap (ResidueField K₀)
  --         (↥(integralClosure (K₀) L) ⧸
  --           LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^
  --             ramificationIdx
  --               (algebraMap K₀ ↥(integralClosure (K₀) L))
  --               (LocalRing.maximalIdeal K₀)
  --               (LocalRing.maximalIdeal ↥(integralClosure (K₀) L)))) ∘
  --     ⇑(Ideal.Quotient.mk (LocalRing.maximalIdeal K₀))) := by
    -- congr
    -- simp_rw [Extended_eq_powE]
    -- sorry
  -- convert algebraMap_comp_Extended K L
  -- congr
  -- simp
  -- simp only [Extended_eq_powE]
  /- ⇑(algebraMap (ResidueField K₀)
          (↥(integralClosure (K₀) L) ⧸ ExtendedMaxIdeal K L)) ∘
      ⇑(Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) =
    ⇑(Ideal.Quotient.mk (ExtendedMaxIdeal K L)) ∘
      ⇑(algebraMap K₀ ↥(integralClosure (K₀) L)) ↔


  ⇑(algebraMap (ResidueField K₀)
          (↥(integralClosure (K₀) L) ⧸
            LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^
              ramificationIdx
                (algebraMap K₀ ↥(integralClosure (K₀) L))
                (LocalRing.maximalIdeal K₀)
                (LocalRing.maximalIdeal ↥(integralClosure (K₀) L)))) ∘
      ⇑(Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) =
    ⇑(Ideal.Quotient.mk
          (LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^
            ramificationIdx
              (algebraMap K₀ ↥(integralClosure (K₀) L))
              (LocalRing.maximalIdeal K₀)
              (LocalRing.maximalIdeal ↥(integralClosure (K₀) L)))) ∘
      ⇑(algebraMap K₀ ↥(integralClosure (K₀) L))-/

  -- sorry
  -- any_goals rw [Extended_eq_powE]
  -- · simp only [algebra_mod_Extended]
    -- simp only [eq_mpr_eq_cast, ← cast_cast, cast_hEq]

attribute [local instance] algebraMod_Extended algebraMod_PowerE

def algEquiv_powE_Extended :
    ((integralClosure K₀ L) ⧸ (LocalRing.maximalIdeal (integralClosure K₀ L) ^ e))
      ≃ₐ[ResidueField K₀] ((integralClosure K₀ L) ⧸ (ExtendedMaxIdeal K L)) :=
  AlgEquiv.ofRingEquiv (f := ringEquiv_powE_Extended K L) (fun _ => rfl)
  -- Ideal.quotEquivOfEq (powE_eq_Extended K L)

-- theorem algebraMap_comp_power_e_apply (a : K₀) :
--     (algebraMap (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L))
--         (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀) a) =
--       Ideal.Quotient.mk (ExtendedMaxIdeal K L) (algebraMap K₀ (integralClosure K₀ L) a) := by
--   simp only [Quotient.mk_algebraMap]
--   rfl

  -- apply Algebra.algebra_ext
  -- sorry/- have :
--     (algebraMap (residue_field K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) ∘
--           Ideal.Quotient.mk (LocalRing.maximalIdeal K₀))
--         a =
--       (Ideal.Quotient.mk (ExtendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L)) a
--   rwa [algebraMap_comp_power_e]
--  -/

-- *FAE* Needed?
instance : SMul (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) := Algebra.toSMul

-- *FAE* Needed?
instance : SMul K₀ (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) :=
  SMul.comp _ (algebraMap K₀ (ResidueField K₀))

@[simp]
theorem Mod_algebraIntExtend_eq_algebraModExtended (a : K₀)
  (x : (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L)) : (residue K₀ a) • x = a • x := by rfl


theorem ScalarTower_Extended :
    IsScalarTower K₀ (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) := by
  -- sorry
  let _ := algebraInt_Extended K L
  -- When calling `IsScalarTower.of_algebraMap_eq` without activating implicit variables we get the
  -- strange error, CI cannot synthesize `Semiring (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L)`
  exact @IsScalarTower.of_algebraMap_eq K₀ (ResidueField K₀)
    (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) _ _ _ _ _ _ (fun _ => rfl)
  -- refine' IsScalarTower.of_algebraMap_eq fun a => _
  -- have algebra_map_comp :
  --   algebraMap K₀ (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) a =
  --     (Ideal.Quotient.mk (ExtendedMaxIdeal K L) ∘ algebraMap K₀ (integralClosure K₀ L)) a :=
  --   by rfl
  -- have algebra_map_eq_quot_mk :
  --   algebraMap K₀ (residue_field K₀) a = (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) a := by rfl
  -- rw [algebra_map_comp, ← algebra_map_comp_power_e, algebra_map_eq_quot_mk]

-- *FAE* Needed?
instance : SMul (ResidueField K₀) ((integralClosure K₀ L) ⧸
    LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) := Algebra.toSMul

-- *FAE* Needed?
instance : SMul K₀ ((integralClosure K₀ L) ⧸ LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) :=
  SMul.comp _ (algebraMap K₀ (ResidueField K₀))

@[simp]
theorem Mod_algebraIntpowerE_eq_algebraModpowerE (a : K₀)
  (x : (↥(integralClosure K₀ L) ⧸ LocalRing.maximalIdeal ↥(integralClosure K₀ L) ^ e)) :
  (residue K₀ a) • x = a • x := by rfl


theorem ScalarTower_PowerE : IsScalarTower K₀ (ResidueField K₀)
    (integralClosure K₀ L ⧸ LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) := by
  let _ := algebraInt_PowerE K L
  -- When calling `IsScalarTower.of_algebraMap_eq` without activating implicit variables we get the
  -- strange error, CI cannot synthesize `Semiring (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L)`
  exact @IsScalarTower.of_algebraMap_eq K₀ (ResidueField K₀)
    (integralClosure K₀ L ⧸ (LocalRing.maximalIdeal (integralClosure K₀ L) ^ e))
      _ _ _ _ _ _ (fun _ => rfl)
  -- have algebra_map_comp :
  --   algebraMap K₀
  --       (integralClosure K₀ L ⧸
  --         LocalRing.maximalIdeal (integralClosure K₀ L) ^
  --           ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
  --             (LocalRing.maximalIdeal (integralClosure K₀ L)))
  --       a =
  --     (Ideal.Quotient.mk
  --           (LocalRing.maximalIdeal (integralClosure K₀ L) ^
  --             ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
  --               (LocalRing.maximalIdeal (integralClosure K₀ L))) ∘
  --         algebraMap K₀ (integralClosure K₀ L))
  --       a :=
  --   by rfl
  -- have algebra_map_eq_quot_mk :
  --     algebraMap K₀ (residue_field K₀) a = (Ideal.Quotient.mk (LocalRing.maximalIdeal K₀)) a := by
  --   rfl
  -- rw [algebra_map_comp, ← algebra_map_comp_Extended, algebra_map_eq_quot_mk]

instance : Module (ResidueField K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) :=
  Algebra.toModule

instance : Module (ResidueField K₀) (↥(integralClosure (K₀) L) ⧸
    LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^ e) := Algebra.toModule

instance : Module (integralClosure K₀ L) (integralClosure K₀ L) := Algebra.toModule


/- The equivalence as vector spaces over the residue field of the base of
* the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below; and
* the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
induced by the equality of the two ideals proved in `Extended_eq_powE` -/
-- noncomputable def quotientLinearIso :
--     (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) ≃ₗ[ResidueField K₀]
--       integralClosure K₀ L ⧸
--         LocalRing.maximalIdeal (integralClosure K₀ L) ^
--           ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
--             (LocalRing.maximalIdeal (integralClosure K₀ L)) := by
--   let f:= ringEquiv_Extended_powE K L
--   have : ∀ c : ResidueField K₀, ∀ x : ((integralClosure K₀ L) ⧸ ExtendedMaxIdeal K L),
--     f (c • x) = c • f x := by
--     · intro c x
--       -- rw [Algebra.algebraMap_eq_smul_one]
--       let ScalarTower_v := (ScalarTower_Extended K L).1 1 c x
--       -- sorry
--       let ScalarTower_fv := (ScalarTower_PowerE K L).1 1 c (f x)
--       -- rw [← Algebra.algebraMap_eq_smul_one, one_smul, algebra_map_eq_quot_mk] at ScalarTower_v
--       --   ScalarTower_fv
--       -- rw [ScalarTower_v, RingHom.id_apply, ScalarTower_fv]
--   apply (ringEquiv_Extended_powE K L).toAddEquiv.toLinearEquiv
--   intro c x
--   erw [this]
--   rfl
  -- apply map_smul
  -- use f
  /- let f := (Submodule.ringEquivOfEq _ _ (Extended_eq_powE K L)).restrictScalars K₀
  let g :
    integralClosure K₀ L ⧸ ExtendedMaxIdeal K L →ₗ[residue_field K₀]
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
      let ScalarTower_v := (ScalarTower_Extended K L).1 a 1 v
      let ScalarTower_fv := (ScalarTower_power_e K L).1 a 1 (f v)
      rw [← Algebra.algebraMap_eq_smul_one a, one_smul, algebra_map_eq_quot_mk] at ScalarTower_v
        ScalarTower_fv
      rw [ScalarTower_v, RingHom.id_apply, ScalarTower_fv]
      apply f.map_smul
  have h : Function.Bijective g := by apply f.bijective
  use LinearEquiv.ofBijective g f.bijective -/

attribute [local instance] algebraResidueFields

instance : Module (K₀⧸ LocalRing.maximalIdeal K₀)
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^
            ramificationIdx
              (algebraMap K₀ ↥(integralClosure (K₀) L))
              (LocalRing.maximalIdeal K₀)
              (LocalRing.maximalIdeal ↥(integralClosure (K₀) L))))
        (LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^ (0 + 1))) := by
  sorry

-- theorem finiteDimensional_powerE [IsSeparable K L] :
--     FiniteDimensional (ResidueField K₀)

  --     (map
  --         (Ideal.Quotient.mk
  --           (LocalRing.maximalIdeal (integralClosure K₀ L) ^
  --             ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
  --               (LocalRing.maximalIdeal (integralClosure K₀ L))))
  --         (LocalRing.maximalIdeal (integralClosure K₀ L) ^ 0) ⧸
  --       LinearMap.range
  --         (powQuotSuccInclusion (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
  --           (LocalRing.maximalIdeal (integralClosure K₀ L)) 0)) := by
  -- have aux :
  --   FiniteDimensional.finrank (K₀ ⧸ LocalRing.maximalIdeal K₀)
  --       (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) =
  --     FiniteDimensional.finrank K L := by
  --   apply
  --     @finrank_quotient_map K₀ _ (integralClosure K₀ L) _ (LocalRing.maximalIdeal K₀) _ K _ _ _ L _
  --       _ (integralClosure.isFractionRing_of_finite_extension K L) _ _ _ _ _ _ _ _ _ _
  --   sorry
  -- have : FiniteDimensional (residue_field K₀) (integralClosure K₀ L ⧸ ExtendedMaxIdeal K L) :=
  --   by
  --   suffices 0 < FiniteDimensional.finrank K L
  --     by
  --     apply FiniteDimensional.finiteDimensional_of_finrank
  --     convert this using 1
  --     rw [← aux]
  --     congr 2
  --     apply Algebra.algebra_ext
  --     rintro ⟨a⟩
  --     simp only [Submodule.Quotient.quot_mk_eq_mk, quotient.mk_eq_mk,
  --       algebra_map_comp_power_e_apply K L a, ← quotient.algebra_map_quotient_map_quotient]
  --     rfl
  --   · rw [FiniteDimensional.finrank_pos_iff_exists_ne_zero]
  --     use 1
  --     apply one_ne_zero
  -- replace aux :
  --   FiniteDimensional (residue_field K₀)
  --     (map
  --       (Ideal.Quotient.mk
  --         (LocalRing.maximalIdeal (integralClosure K₀ L) ^
  --           ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
  --             (LocalRing.maximalIdeal (integralClosure K₀ L))))
  --       (LocalRing.maximalIdeal (integralClosure K₀ L) ^ 0)) := by
  --   rw [pow_zero, one_eq_top, Ideal.map_top]
  --   haveI := (quotient_linear_iso K L).FiniteDimensional
  --   apply
  --     (@Submodule.topEquiv (residue_field K₀)
  --           (integralClosure K₀ L ⧸
  --             LocalRing.maximalIdeal (integralClosure K₀ L) ^
  --               ramification_idx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
  --                 (LocalRing.maximalIdeal (integralClosure K₀ L)))
  --           _ _ _).symm.FiniteDimensional
  -- exact @FiniteDimensional.finiteDimensional_quotient (residue_field K₀) _ _ _ _ aux _

instance : Ring
    (↥(integralClosure (K₀) L) ⧸
      LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^
        ramificationIdx (algebraMap K₀ ↥(integralClosure (K₀) L))
          (LocalRing.maximalIdeal K₀)
          (LocalRing.maximalIdeal ↥(integralClosure (K₀) L))) := by
  sorry

instance : AddCommGroup
    ↥(Ideal.map
        (Ideal.Quotient.mk
          (LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^
            ramificationIdx
              (algebraMap K₀ ↥(integralClosure (K₀) L))
              (LocalRing.maximalIdeal K₀)
              (LocalRing.maximalIdeal ↥(integralClosure (K₀) L))))
        (LocalRing.maximalIdeal ↥(integralClosure (K₀) L) ^ 0)) := by
  sorry

instance : Ring ↥(integralClosure (K₀) L) := by sorry

theorem finiteDimensional_residueField_of_integralClosure [IsSeparable K L] :
    FiniteDimensional (ResidueField K₀) (ResidueField (integralClosure K₀ L)) := by
  -- let alg := algebraResidueFields K L
  -- dsimp only [ResidueField] at alg
  -- letI := alg
  letI h0 := ramificationIdx_maximal_neZero K L
  have zero_lt :
    0 <
      ramificationIdx (algebraMap K₀ (integralClosure K₀ L)) (LocalRing.maximalIdeal K₀)
        (LocalRing.maximalIdeal (integralClosure K₀ L)) :=
    by apply Nat.pos_of_ne_zero h0.1
  let surj :=
    quotientRangePowQuotSuccInclusionEquiv (algebraMap K₀ (integralClosure K₀ L))
      (LocalRing.maximalIdeal K₀) (LocalRing.maximalIdeal (integralClosure K₀ L))
      (DiscreteValuationRing.not_a_field _) zero_lt
  have temp := finiteDimensional_powerE K L
  have := @LinearEquiv.finiteDimensional (ResidueField K₀) ?_ _ ?_ ?_
    (ResidueField (integralClosure K₀ L)) _
    -- (ResidueField (integralClosure K₀ L))
  /- apply
    @LinearEquiv.finiteDimensional (ResidueField K₀) _ _ _ _ (ResidueField (integralClosure K₀ L))
      _ _ surj _ --(finiteDimensional_pow K L) -/


#exit

-/
-- instance : LocalRing (integralClosure K₀ L) := by sorry


open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

noncomputable
def aboveℳ  :
  {x // x ∈ Multiset.toFinset (UniqueFactorizationMonoid.factors
  (Ideal.map (algebraMap K₀ R) ℳ))} where
    val := LocalRing.maximalIdeal _
    property := by
      simp_all only [UniqueFactorizationMonoid.factors_eq_normalizedFactors, Multiset.mem_toFinset]
      rw [Ideal.mem_normalizedFactors_iff]
      constructor
      · exact IsMaximal.isPrime' (LocalRing.maximalIdeal ↥R)
      · apply le_maximalIdeal
        rw [ne_eq, ← Ideal.isUnit_iff]
        apply ExtendedMaxIdeal_not_isUnit
      apply ExtendedMaxIdeal_ne_zero

@[simp]
theorem aboveℳ_val_eq_max : ((aboveℳ K L) : Ideal R) = LocalRing.maximalIdeal _ := rfl

-- set_option autoImplicit false
-- set_option relaxedAutoImplicit false
-- set_option pp.proofs.withType false
-- set_option pp.unicode.fun true
-- set_option synthInstance.checkSynthOrder false

-- *FAE* Needed?
-- instance : SMul (ResidueField K₀) ((integralClosure K₀ L) ⧸
--     LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) := Algebra.toSMul

-- -- *FAE* Needed?
-- instance : SMul K₀ ((integralClosure K₀ L) ⧸ LocalRing.maximalIdeal (integralClosure K₀ L) ^ e) :=
--   SMul.comp _ (algebraMap K₀ (ResidueField K₀))

instance bleah : Algebra (ResidueField K₀) (ResidueField R) := @Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero K₀ _ R _ (algebraMap K₀ R) ℳ
    (LocalRing.maximalIdeal _) (ramificationIdx_maximal_neZero K L)

instance foo : SMul K₀ (ResidueField K₀) := inferInstance

-- instance bar : SMul K₀ (ResidueField R) :=
--   @SMul.comp (ResidueField K₀) K₀ (ResidueField R) _ (residue _ ·)

instance bar : Algebra K₀ (ResidueField R) := by
  apply RingHom.toAlgebra
  apply RingHom.comp (bleah K L).toRingHom (residue _)

  -- @SMul.comp (ResidueField K₀) K₀ (ResidueField R) _ (residue _ ·)


  /-- The residue field of the integral closure of a DVR in a  finite, separable extension of a
fraction field of the DVR is finite if the residue field of the base is finite-/
-- *FAE* Stated with `Finite` that is arguably a better class than ` Fintype`
noncomputable def finiteResidueFieldOfIntegralClosure [IsSeparable K L]
    [Finite (ResidueField K₀)] : Finite (ResidueField (integralClosure K₀ L)) := by
  have _ : Ring R := by infer_instance --remove?
  let algStr := @Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero K₀ _ R _ (algebraMap K₀ R) ℳ
    (LocalRing.maximalIdeal _) (ramificationIdx_maximal_neZero K L)
  let modStr := @Algebra.toModule _ _ _ _ algStr --remove?
  -- let algStr' := @Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero K₀ _ R _ (algebraMap K₀ R) ℳ
  --   (Ideal.map (algebraMap K₀ R) ℳ) (ramificationIdx_Extended_neZero K L)
  -- let modStr' := @Algebra.toModule _ _ _ _ algStr --remove?
  have temp := @Factors.finiteDimensional_quotient K₀ _ R _ ℳ _ _ _ _ _ ?_--probably can remove convert
  -- swap
  -- convert (aboveℳ K L)
  -- simp_all at temp
  have := @FiniteDimensional.finite_of_finite (LocalRing.ResidueField K₀)
    (LocalRing.ResidueField R) _ _ modStr _ ?_
  apply this
  unfold ResidueField
  apply IsNoetherian.iff_fg.mp
  apply @isNoetherian_of_tower K₀ (K₀ ⧸ ℳ) (R ⧸ LocalRing.maximalIdeal R) _ _ _ (foo K) modStr
    (bar K L).toModule ?_
  have xx := @isNoetherian_of_surjective K₀ R (R ⧸ LocalRing.maximalIdeal R) _ _ _ _
    (bar K L).toModule
  apply xx
  swap
  let φ := (@Ideal.Quotient.mkₐ K₀ R _ _ _ (LocalRing.maximalIdeal R))
  let ψ := @AlgHom.toLinearMap K₀ R (ResidueField R) _ _ _ _ (bar K L) φ
  -- convert (residue R).toLinearMap

    -- IsNoetherian.iff_fg.mp <|
    -- isNoetherian_of_tower R <|
    --   isNoetherian_of_surjective S (Ideal.Quotient.mkₐ _ _).toLinearMap <|
    --     LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective


  -- have _ : Ring R := by infer_instance --remove?
  -- let algStr := @Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero K₀ _ R _ (algebraMap K₀ R) ℳ
  --   (Ideal.map (algebraMap K₀ R) ℳ) ?_ --remove?
  -- let modStr := @Algebra.toModule _ _ _ _ algStr --remove?
  -- have finH := @Ideal.finrank_quotient_map K₀ _ (integralClosure K₀ L) _ ℳ _ K
  --   _ _ _ L _ _ ?_ _ _ _ _ _ _ _ _ _ _

  -- swap
  -- · apply @FiniteDimensional.of_finrank_pos (LocalRing.ResidueField K₀)
  --     (R ⧸ Ideal.map (algebraMap K₀ R) ℳ) _ _ modStr
  --   erw [finH]
  --   exact FiniteDimensional.finrank_pos
  -- have := @Ideal.inertiaDeg_algebraMap




  -- let ι := @FiniteDimensional.finBasis (LocalRing.ResidueField K₀)
  --   (R ⧸ Ideal.map (algebraMap K₀ R) ℳ) _ _ _ modStr ?_
  -- let FF := @Module.fintypeOfFintype (LocalRing.ResidueField K₀) (LocalRing.ResidueField K₀)
  --   (R ⧸ Ideal.map (algebraMap K₀ R) ℳ) _ _ ?_ _



  -- letI := finiteDimensional_residueField_of_integralClosure K L
  -- Module.fintypeOfFintype
  --   (FiniteDimensional.finBasis (ResidueField K₀) (ResidueField (integralClosure K₀ L)))

-- instance : LocalRing ↥(Subalgebra.toSubring (integralClosure (K₀) L)) := by
--   sorry


/-- The residue field of the unit ball of a  finite, separable extension of a fraction field of a
DVR is finite if the residue field of the base is finite-/
noncomputable def finiteResidueFieldOfUnitBall [IsSeparable K L]
    [Fintype (LocalRing.ResidueField K₀)] :
    Fintype (ResidueField (extendedValuation K L).valuationSubring) := sorry
  -- @Fintype.ofEquiv _ _ (finiteResidueFieldOfIntegralClosure K L)
  --   (LocalRing.ResidueField.mapEquiv
  --       (RingEquiv.subringCongr
  --         (DiscreteValuation.Extension.integralClosure_eq_integer K L))).toEquiv

end DiscreteValuation
