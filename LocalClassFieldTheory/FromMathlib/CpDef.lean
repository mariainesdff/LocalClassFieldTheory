/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField
import LocalClassFieldTheory.FromMathlib.SpectralNormUnique

#align_import from_mathlib.Cp_def

/-!
# The `p`-adic complex numbers.

In this file we define the field `ℂ_[p]` of `p`-adic complex numbers and we give it both a normed
field and a valued field structure, induced by the unique extension of the `p`-adic norm to `ℂ_[p]`.

## Main Definitions

* `padic_complex` : the type of `p`-adic complex numbers.
* `padic_complex_integers` : the ring of integers of `ℂ_[p]`.


## Main Results

* `padic_complex.norm_extends` : the norm on `ℂ_[p]` extends the norm on `Q_p_alg p`, and hence
  the norm on `ℚ_[p]`.
* `padic_complex.is_nonarchimedean` : The norm on `ℂ_[p]` is nonarchimedean.


## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/


noncomputable section

open Valued Valuation

open scoped NNReal

variable (p : ℕ) [hp: Fact (Nat.Prime p)]

/-- `Q_p_alg p` is the algebraic closure of `ℚ_[p]`. -/
@[reducible]
def QPAlg : Type _ :=
  AlgebraicClosure ℚ_[p]

/-- `Q_p_alg p` is an algebraic extension of `ℚ_[p]`. -/
theorem QPAlg.isAlgebraic : Algebra.IsAlgebraic ℚ_[p] (QPAlg p) :=
  AlgebraicClosure.isAlgebraic _

instance : Coe ℚ_[p] (QPAlg p) := ⟨algebraMap ℚ_[p] (QPAlg p)⟩

theorem coe_eql : (Coe.coe : ℚ_[p] → QPAlg p) = algebraMap ℚ_[p] (QPAlg p) := by
  rfl


namespace QPAlg

/-- `Q_p_alg p` is a normed field, where the norm is the `p`-adic norm, that is, the spectral norm
induced by the `p`-adic norm on `ℚ_[p]`. -/
instance normedField : NormedField (QPAlg p) :=
  spectralNormToNormedField (K := ℚ_[p]) (L := QPAlg p) padicNormE.nonarchimedean

/-- The norm on `Q_p_alg p` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (norm : QPAlg p → ℝ) :=
  spectralNorm_isNonarchimedean (K := ℚ_[p]) (L := QPAlg p) padicNormE.nonarchimedean

/-- The norm on `Q_p_alg p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
theorem norm_def (x : QPAlg p) : ‖x‖ = spectralNorm ℚ_[p] (QPAlg p) x :=
  rfl

/-- The norm on `Q_p_alg p` extends the `p`-adic norm on `ℚ_[p]`. -/
theorem QP.norm_extends (x : ℚ_[p]) : ‖(x : QPAlg p)‖ = ‖x‖ :=
  spectralAlgNorm_extends (K := ℚ_[p]) (L := QPAlg p) _ padicNormE.nonarchimedean

/-- `Q_p_alg p` is a valued field, with the valuation corresponding to the `p`-adic norm. -/
instance valuedField : Valued (QPAlg p) ℝ≥0 :=
  NormedField.toValued (QPAlg.isNonarchimedean p)

/-- The valuation of `x : Q_p_alg p` agrees with its `ℝ≥0`-valued norm. -/
theorem v_def (x : QPAlg p) : Valued.v x = ‖x‖₊ :=
  rfl

/-- The coercion of the valuation of `x : Q_p_alg p` to `ℝ` agrees with its norm. -/
theorem v_def_coe (x : QPAlg p) : ((Valued.v x : ℝ≥0) : ℝ) = spectralNorm ℚ_[p] (QPAlg p) x :=
  rfl

/-- The valuation of `p : Q_p_alg p` is `1/p`. -/
theorem valuation_p (p : ℕ) [Fact p.Prime] : Valued.v (p : QPAlg p) = 1 / (p : ℝ≥0) :=
  by
  rw [← map_natCast (algebraMap ℚ_[p] (QPAlg p))]
  ext
  rw [v_def_coe,  spectralNorm_extends, padicNormE.norm_p, one_div, NNReal.coe_inv,
    NNReal.coe_natCast]

end QPAlg

/-- `ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `Q_p_alg p` with
respect to the `p`-adic norm. -/
def PadicComplex :=
  UniformSpace.Completion (QPAlg p)

notation "ℂ_[" p "]" => PadicComplex p

namespace PadicComplex

/-- The `p`-adic complex numbers have a field structure. -/
instance : Field ℂ_[p] :=
  UniformSpace.Completion.instField

/-- The `p`-adic complex numbers are inhabited. -/
instance : Inhabited ℂ_[p] :=
  ⟨0⟩

/-- `ℂ_[p]` is a valued field, where the valuation is the one extending that on `Q_p_alg p`. -/
instance valuedField : Valued ℂ_[p] ℝ≥0 :=
  Valued.valuedCompletion

/-- `ℂ_[p]` is a complete space. -/
instance completeSpace : CompleteSpace ℂ_[p] :=
  UniformSpace.Completion.completeSpace _

instance : Coe (QPAlg p) ℂ_[p] := ⟨UniformSpace.Completion.coe' _⟩

/-- The valuation on `ℂ_[p]` extends the valuation on `Q_p_alg p`. -/
theorem valuation_extends (x : QPAlg p) : Valued.v (x : ℂ_[p]) = Valued.v x :=
  Valued.extension_extends _

/-- `ℂ_[p]` is an algebra over `Q_p_alg p`. -/
instance : Algebra (QPAlg p) ℂ_[p] :=
  UniformSpace.Completion.algebra' _

theorem coe_eq : (Coe.coe : QPAlg p → ℂ_[p]) = algebraMap (QPAlg p) ℂ_[p] :=
  rfl

theorem coe_zero : ((0 : QPAlg p) : ℂ_[p]) = 0 :=
  rfl

/-- The valuation of `p : ℂ_[p]` is `1/p`. -/
theorem valuation_p (p : ℕ) [Fact p.Prime] : Valued.v (p : ℂ_[p]) = 1 / (p : ℝ≥0) := by
  erw [← map_natCast (algebraMap (QPAlg p) ℂ_[p]), ← coe_eq, valuation_extends, QPAlg.valuation_p]

/-- The valuation on `ℂ_[p]` has rank one. -/
instance : RankOne (PadicComplex.valuedField p).v where
  hom         := MonoidWithZeroHom.id ℝ≥0
  strictMono' := strictMono_id
  nontrivial' := by
    use p
    haveI hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

/-- `ℂ_[p]` is a normed field, where the norm corresponds to the extension of the `p`-adic
  valuation.-/
instance C_p.NormedField : NormedField ℂ_[p] :=
  Valued.toNormedField _ _

instance : NormedField (UniformSpace.Completion (QPAlg p)) := C_p.NormedField p

/-- The norm on `ℂ_[p]` agrees with the valuation. -/
theorem normDef : (Norm.norm : ℂ_[p] → ℝ) = Valued.norm := rfl

/-- The norm on `ℂ_[p]` extends the norm on `Q_p_alg p`. -/
theorem norm_extends (x : QPAlg p) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, coe_zero, norm_zero, norm_zero]
  · erw [normDef, Valued.norm, valuation_extends, MonoidWithZeroHom.coe_mk]
    rfl

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `Q_p_alg p`. -/
theorem nnnorm_extends (x : QPAlg p) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by ext; exact norm_extends p x

/-- The norm on `ℂ_[p]` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (Norm.norm : ℂ_[p] → ℝ) := by
  intro x y
  refine' UniformSpace.Completion.induction_on₂ x y _ _
  · exact
      isClosed_le (Continuous.comp continuous_norm continuous_add)
        (Continuous.max (Continuous.comp (@continuous_norm ℂ_[p] _) (Continuous.fst continuous_id))
          (Continuous.comp (@continuous_norm ℂ_[p] _) (Continuous.snd continuous_id)))
  · intro a b
    rw [← UniformSpace.Completion.coe_add, norm_extends, norm_extends, norm_extends]
    exact QPAlg.isNonarchimedean p a b

  /- apply UniformSpace.Completion.induction_on₂ x y
  ·
    exact
      isClosed_le (Continuous.comp continuous_norm continuous_add)
        (Continuous.max (Continuous.comp (@continuous_norm ℂ_[p] _) (Continuous.fst continuous_id))
          (Continuous.comp (@continuous_norm ℂ_[p] _) (Continuous.snd continuous_id)))
  · intro a b
    simp only [← UniformSpace.Completion.coe_add, norm_extends]
    exact QPAlg.isNonarchimedean p a b -/

end PadicComplex

/-- We define `𝓞_ℂ_[p]` as the subring elements of `ℂ_[p]` with valuation `≤ 1`. -/
def padicComplexIntegers : Subring ℂ_[p] :=
  (PadicComplex.valuedField p).v.integer

notation "𝓞_ℂ_[" p "]" => padicComplexIntegers p

/-- `𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`. -/
theorem PadicComplex.integers : Valuation.Integers (PadicComplex.valuedField p).v 𝓞_ℂ_[p] :=
  Valuation.integer.integers _
