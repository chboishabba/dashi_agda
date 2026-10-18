{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSH1ModeSelectedContinuumUpperExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact as R304
import DASHI.Physics.YangMills.BalabanR318CanonicalDirectShellRound398Exact as R398
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as H1

------------------------------------------------------------------------
-- PREFERRED ROUTE-S SOURCE COMPILER
--
-- R387 is a useful least-privilege generic spectral-upper ABI, but the
-- mode-selected contradiction needs even less structure.  R304 already consumes
-- exactly:
--
--   * one exact finite T5 direct shell;
--   * selected physical support distance = Euclidean time;
--   * one-sided closure of the actual R278 scalar convergence.
--
-- H1 constructs the direct shell through R398.  Therefore:
--
--   H1 + distance=time + SelectedLimitUpperClosure
--      -> exact continuum selected covariance upper
--
--        C_mode(t) <= (1/4)(1/2)^t.
--
-- No source envelope, source root/distance carrier, arbitrary clustering
-- envelope, or spectrum-envelope calibration is consumed.
------------------------------------------------------------------------

record RouteSH1ModeSelectedInputs
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    : Set₁ where
  field
    h1 : H1.RouteSH1DirectSelectedPayment base

    selectedPairDistanceIsTime :
      ∀ observable time →
      let index = R300.indexFor decomposition observable time in
      R318.physicalDistance base
        (R278.left tests index)
        (R278.right tests index)
      ≡ time

    selectedLimitUpperClosure :
      R342.SelectedLimitUpperClosure {dataSet = dataSet}

open RouteSH1ModeSelectedInputs public

asR304ModeSelectedPayment :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  RouteSH1ModeSelectedInputs
    base tests quantitative family decomposition →
  R304.ModeSelectedDirectT5UpperPayment
    dataSet extension tests quantitative family decomposition
asR304ModeSelectedPayment
    {base = base} inputs = record
  { R304.ModeSelectedDirectT5UpperPayment.directShell =
      R398.canonicalDirectShell base
        (H1.directSelectedDecay (h1 inputs))
  ; R304.ModeSelectedDirectT5UpperPayment.selectedPairDistanceIsTime =
      selectedPairDistanceIsTime inputs
  ; R304.ModeSelectedDirectT5UpperPayment.rationalUpperClosedUnderSelectedLimit =
      selectedLimitUpperClosure inputs
  }

h1ModeSelectedInputsBuildContinuumHalfRateUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  RouteSH1ModeSelectedInputs
    base tests quantitative family decomposition →
  R301.ContinuumSelectedCorrelationUpper decomposition
h1ModeSelectedInputsBuildContinuumHalfRateUpper inputs =
  R304.continuumSelectedUpper (asR304ModeSelectedPayment inputs)

------------------------------------------------------------------------
-- Pareto classification.
------------------------------------------------------------------------

arbitrarySpectrumClusteringEnvelopeRequired : Bool
arbitrarySpectrumClusteringEnvelopeRequired = false

arbitrarySpectrumClusteringEnvelopeRequiredIsFalse :
  arbitrarySpectrumClusteringEnvelopeRequired ≡ false
arbitrarySpectrumClusteringEnvelopeRequiredIsFalse = refl

fastSpectrumEnvelopeCalibrationRequired : Bool
fastSpectrumEnvelopeCalibrationRequired = false

fastSpectrumEnvelopeCalibrationRequiredIsFalse :
  fastSpectrumEnvelopeCalibrationRequired ≡ false
fastSpectrumEnvelopeCalibrationRequiredIsFalse = refl

sourceEnvelopeRequired : Bool
sourceEnvelopeRequired = false

sourceEnvelopeRequiredIsFalse :
  sourceEnvelopeRequired ≡ false
sourceEnvelopeRequiredIsFalse = refl

sourceRootDistanceCarrierRequired : Bool
sourceRootDistanceCarrierRequired = false

sourceRootDistanceCarrierRequiredIsFalse :
  sourceRootDistanceCarrierRequired ≡ false
sourceRootDistanceCarrierRequiredIsFalse = refl

selectedDistanceTimeStillPhysical : Bool
selectedDistanceTimeStillPhysical = true

selectedDistanceTimeStillPhysicalIsTrue :
  selectedDistanceTimeStillPhysical ≡ true
selectedDistanceTimeStillPhysicalIsTrue = refl

selectedLimitUpperClosureStillRequired : Bool
selectedLimitUpperClosureStillRequired = true

selectedLimitUpperClosureStillRequiredIsTrue :
  selectedLimitUpperClosureStillRequired ≡ true
selectedLimitUpperClosureStillRequiredIsTrue = refl

modeSelectedContinuumUpperCompilerLevel : ProofLevel
modeSelectedContinuumUpperCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
