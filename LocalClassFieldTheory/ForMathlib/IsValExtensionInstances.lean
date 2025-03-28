/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/


import Mathlib.RingTheory.Valuation.ValExtension
import Mathlib.Topology.Algebra.Valued.ValuationTopology

section Algebra

open IsLocalRing Valuation ValuationSubring

variable {K L Γ₀ Γ₁: outParam Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁] [hv : Valued K Γ₀]
   (vL : Valuation L Γ₁) [IsValExtension hv.v vL]

theorem Integer.not_isUnit_iff_valuation_lt_one' {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (x : v.integer) :
    ¬IsUnit x ↔ v x < 1 := by
  rw [← not_le, not_iff_not, Integers.isUnit_iff_valuation_eq_one (integer.integers v),
    le_antisymm_iff]
  exact and_iff_right x.2

local notation "K₀" => hv.v.valuationSubring
local notation "L₀" => Valuation.valuationSubring vL

lemma ValuationSubring.algebraMap_mem (x : K₀) : algebraMap K L x ∈ L₀ := by
  rw [mem_valuationSubring_iff, ← _root_.map_one vL, ← _root_.map_one (algebraMap K L),
    IsValExtension.val_map_le_iff (vR := hv.v), _root_.map_one]
  exact x.2

instance instAlgebra_valuationSubring : Algebra K₀ L₀ :=
  let f : K₀ →+* L₀ := {
    toFun := fun x ↦ ⟨algebraMap K L x, algebraMap_mem vL x⟩
    map_one'  := by simp [_root_.map_one, ← @OneMemClass.coe_eq_one]
    map_mul'  := by simp [MulMemClass.coe_mul, _root_.map_mul, MulMemClass.mk_mul_mk, implies_true]
    map_zero' := by simp [← ZeroMemClass.coe_eq_zero, _root_.map_zero]
    map_add'  := by simp only [AddMemClass.coe_add, _root_.map_add, AddMemClass.mk_add_mk,
      implies_true] }
  f.toAlgebra

@[simp]
lemma coe_algebraMap_valuationSubring_eq (x : K₀) :
  (algebraMap K₀ L₀ x : L) = algebraMap K L (x : K) := rfl

protected theorem _root_.ValuationSubring.mem_maximalIdeal {a : L₀}  :
    a ∈ maximalIdeal L₀ ↔ vL a < 1 :=
  Integer.not_isUnit_iff_valuation_lt_one' a

lemma maximalIdeal_mem_iff {x : K₀} :
    x ∈ maximalIdeal K₀ ↔ algebraMap K₀ L₀ x ∈ (maximalIdeal L₀) := by
  simp only [ValuationSubring.mem_maximalIdeal, coe_algebraMap_valuationSubring_eq,
    IsValExtension.val_map_lt_one_iff hv.v vL]

instance : Algebra (ResidueField K₀) (ResidueField L₀) :=
  (Ideal.Quotient.lift (maximalIdeal K₀)
    ((Ideal.Quotient.mk (maximalIdeal L₀)).comp (algebraMap K₀ L₀))
    (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
      ((maximalIdeal_mem_iff vL).mp hx))).toAlgebra

end Algebra
