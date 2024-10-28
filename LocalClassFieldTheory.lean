-- Basic folder *complete*
import LocalClassFieldTheory.LaurentSeriesEquivAdicCompletion  -- In PR #11720, #13063, #13064, #14418, #16865, #18346
import LocalClassFieldTheory.PadicCompare
import LocalClassFieldTheory.SpectralNorm
-- DiscreteValuationRing folder *complete*
import LocalClassFieldTheory.DiscreteValuationRing.AdjoinRoot -- It has sorrys
import LocalClassFieldTheory.DiscreteValuationRing.Basic
import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.DiscreteNorm
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import LocalClassFieldTheory.DiscreteValuationRing.Localization
import LocalClassFieldTheory.DiscreteValuationRing.Ramification -- It has sorrys
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField
import LocalClassFieldTheory.DiscreteValuationRing.TrivialExtension
-- EqCharacteristic folder *complete*
import LocalClassFieldTheory.EqCharacteristic.Basic
import LocalClassFieldTheory.EqCharacteristic.Valuation
-- ForMathlib folder *complete*
-- import LocalClassFieldTheory.ForMathlib.Data.Set.Lattice -- In PR #12961 I got convinced it was useless
-- import LocalClassFieldTheory.ForMathlib.FieldTheory.Minpoly.IsIntegrallyClosed -- In PR #15723
import LocalClassFieldTheory.ForMathlib.NumberTheory.Padics.PadicIntegers
-- import LocalClassFieldTheory.ForMathlib.RingTheory.DedekindDomain.Ideal --In PR #13065
-- import LocalClassFieldTheory.ForMathlib.RingTheory.Ideal.LocalRing -- In PR #15725
-- import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.AlgebraInstances -- In PR #15734
-- import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.Integers -- In PR #12247
-- import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.IntPolynomial -- In PR #15733
-- import LocalClassFieldTheory.ForMathlib.RingTheory.Valuation.Minpoly -- In PR #15736
-- import LocalClassFieldTheory.ForMathlib.RingTheory.IntegralClosure -- In PR #15738
-- import LocalClassFieldTheory.ForMathlib.Topology.UniformSpace.AbstractCompletion -- In PR #12979
-- import LocalClassFieldTheory.ForMathlib.DiscreteUniformity -- In PR #16865 (was in #12179)
import LocalClassFieldTheory.ForMathlib.DiscreteValuationRing
-- import LocalClassFieldTheory.ForMathlib.Polynomial -- In PR #13064
-- import LocalClassFieldTheory.ForMathlib.PowerSeries -- In PR #12160 and PR #12245
import LocalClassFieldTheory.ForMathlib.RankOneValuation -- Final lemma in PR #13064
import LocalClassFieldTheory.ForMathlib.WithZero -- Partly in PR #15741
-- FromMathlib folder *complete*
import LocalClassFieldTheory.FromMathlib.AlgNormOfGalois
import LocalClassFieldTheory.FromMathlib.CpDef
-- import LocalClassFieldTheory.FromMathlib.Filter -- In PR #12430
-- TODO: uncomment
import LocalClassFieldTheory.FromMathlib.Limsup -- Mostly in PR #18172
--import LocalClassFieldTheory.FromMathlib.Minpoly -- In PR #12450
import LocalClassFieldTheory.FromMathlib.NormalClosure
import LocalClassFieldTheory.FromMathlib.NormedSpace
--import LocalClassFieldTheory.FromMathlib.NormedValued -- In PR #12432
--import LocalClassFieldTheory.FromMathlib.PowMultFaithful -- In PR #15445
-- import LocalClassFieldTheory.FromMathlib.RankOneValuation -- PRs #12156 and #12159
import LocalClassFieldTheory.FromMathlib.RingSeminorm -- Partly in PR #15445
--import LocalClassFieldTheory.FromMathlib.SeminormFromBounded -- Partly in #14359, except for NormedGroupHom section (unused)
--import LocalClassFieldTheory.FromMathlib.SeminormFromConst -- In PR #14361
import LocalClassFieldTheory.FromMathlib.SmoothingSeminorm -- In PR #15373
import LocalClassFieldTheory.FromMathlib.SpecificLimits
import LocalClassFieldTheory.FromMathlib.SpectralNormUnique
-- LocalFields folder
import LocalClassFieldTheory.LocalField.Basic
import LocalClassFieldTheory.LocalField.Unramified -- It has sorrys
-- MixedCharacteristic folder *complete*
import LocalClassFieldTheory.MixedCharacteristic.Basic
import LocalClassFieldTheory.MixedCharacteristic.Valuation
