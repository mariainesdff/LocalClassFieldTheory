import Mathlib.MeasureTheory.Group.ModularCharacter

open MeasureTheory.Measure

variable (K : Type*) [Field K]

class LocalField extends UniformSpace K, IsUniformAddGroup K,
  IsTopologicalDivisionRing K, CompleteSpace K, LocallyCompactSpace K

class NonarchimedeanLocalField extends LocalField K where
  isNonarchimedean : IsNonarchimedean (addModularCharacterFun · : K → ℝ)

class ArchimedeanLocalField extends LocalField K where
  Archimedean : 1 < (addModularCharacterFun (2 : K))

variable [LocalField K]

def IsNonarchimedeanLocalField : Prop :=
  IsNonarchimedean (addModularCharacterFun · : K → ℝ)

def IsArchimedeanLocalField : Prop :=
  1 < (addModularCharacterFun (2 : K))

lemma isArchimedeanLocalField_iff_not_isNonarchimedean :
  IsArchimedeanLocalField K ↔ ¬ IsNonarchimedeanLocalField K := sorry

lemma RCLike.isArchimedeanLocalField [RCLike K] :
  IsArchimedeanLocalField K := sorry
