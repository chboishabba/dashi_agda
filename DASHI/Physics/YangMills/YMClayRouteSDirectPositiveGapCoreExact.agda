{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSDirectPositiveGapCoreExact where

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
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanDirectT5PositiveSubgapExclusionRound305Exact as R305
import DASHI.Physics.YangMills.BalabanModeIndexedPositiveGapCoreRound306Exact as R306
import DASHI.Physics.YangMills.YMClayRouteSH1ModeSelectedContinuumUpperExact as Source

------------------------------------------------------------------------
-- PREFERRED ROUTE-S TERMINAL SPECTRAL CORE
--
-- R301's ModeIndexedSubgapRateSemantics is compatibility packaging.  R302/R303
-- already show that the actual physical rate semantics are smaller:
--
--   one order-reversing transfer-energy <-> decay-ratio coordinate
--   + proof that the selected spectral mode ratio is that SAME coordinate.
--
-- R305 then composes this with the direct finite-T5/continuum upper, and R306
-- projects the result to the true terminal gap content:
--
--   candidateEnergy is positive
--   + no positive spectral mode lies strictly below candidateEnergy.
--
-- Thus the preferred Route-S spectral proof consumes exactly:
--
--   source:
--     H1 + selected distance=time + selected one-sided limit closure
--
--   spectral:
--     SAME-H positive spectral component decomposition
--     + one transfer-energy/decay coordinate
--     + mode ratio uses that coordinate
--     + standard rational geometric domination.
--
-- No arbitrary clustering envelope, no old mode-rate record, no separate
-- overlap-positivity theorem and no separate spectral-lower inequality remain.
------------------------------------------------------------------------

record RouteSDirectPositiveGapInputs
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
    (coordinate : R302.TransferEnergyDecayRatioCoordinate Energy)
    : Set₁ where
  field
    source :
      Source.RouteSH1ModeSelectedInputs
        base tests quantitative family decomposition

    modeRatioUsesTransferCoordinate :
      R302.ModeRatioUsesTransferCoordinate decomposition coordinate

    geometricDominance :
      R293.RationalGeometricDominance

open RouteSDirectPositiveGapInputs public

asR305DirectT5PositiveSubgapPayment :
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
      dataSet extension tests quantitative family}
    {coordinate : R302.TransferEnergyDecayRatioCoordinate Energy} →
  RouteSDirectPositiveGapInputs
    base tests quantitative family decomposition coordinate →
  R305.DirectT5PositiveSubgapExclusionPayment decomposition coordinate
asR305DirectT5PositiveSubgapPayment inputs = record
  { R305.DirectT5PositiveSubgapExclusionPayment.modeRatioWeld =
      modeRatioUsesTransferCoordinate inputs
  ; R305.DirectT5PositiveSubgapExclusionPayment.directUpperPayment =
      Source.asR304ModeSelectedPayment (source inputs)
  ; R305.DirectT5PositiveSubgapExclusionPayment.geometricDominance =
      geometricDominance inputs
  }

routeSDirectPositiveGapCore :
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
      dataSet extension tests quantitative family}
    {coordinate : R302.TransferEnergyDecayRatioCoordinate Energy} →
  RouteSDirectPositiveGapInputs
    base tests quantitative family decomposition coordinate →
  R306.ModeIndexedPositiveGapCore Energy
routeSDirectPositiveGapCore inputs =
  R306.compileDirectT5PositiveGapCore
    (asR305DirectT5PositiveSubgapPayment inputs)

------------------------------------------------------------------------
-- Pareto classification.
------------------------------------------------------------------------

oldModeIndexedRateRecordMandatory : Bool
oldModeIndexedRateRecordMandatory = false

oldModeIndexedRateRecordMandatoryIsFalse :
  oldModeIndexedRateRecordMandatory ≡ false
oldModeIndexedRateRecordMandatoryIsFalse = refl

arbitraryClusteringEnvelopeMandatory : Bool
arbitraryClusteringEnvelopeMandatory = false

arbitraryClusteringEnvelopeMandatoryIsFalse :
  arbitraryClusteringEnvelopeMandatory ≡ false
arbitraryClusteringEnvelopeMandatoryIsFalse = refl

separatePositiveOverlapLeafMandatory : Bool
separatePositiveOverlapLeafMandatory = false

separatePositiveOverlapLeafMandatoryIsFalse :
  separatePositiveOverlapLeafMandatory ≡ false
separatePositiveOverlapLeafMandatoryIsFalse = refl

separateSpectralLowerLeafMandatory : Bool
separateSpectralLowerLeafMandatory = false

separateSpectralLowerLeafMandatoryIsFalse :
  separateSpectralLowerLeafMandatory ≡ false
separateSpectralLowerLeafMandatoryIsFalse = refl

sameHamiltonianPositiveSpectralDecompositionStillPhysical : Bool
sameHamiltonianPositiveSpectralDecompositionStillPhysical = true

sameHamiltonianPositiveSpectralDecompositionStillPhysicalIsTrue :
  sameHamiltonianPositiveSpectralDecompositionStillPhysical ≡ true
sameHamiltonianPositiveSpectralDecompositionStillPhysicalIsTrue = refl

transferEnergyDecayCoordinateStillPhysical : Bool
transferEnergyDecayCoordinateStillPhysical = true

transferEnergyDecayCoordinateStillPhysicalIsTrue :
  transferEnergyDecayCoordinateStillPhysical ≡ true
transferEnergyDecayCoordinateStillPhysicalIsTrue = refl

modeRatioSameCoordinateWeldStillPhysical : Bool
modeRatioSameCoordinateWeldStillPhysical = true

modeRatioSameCoordinateWeldStillPhysicalIsTrue :
  modeRatioSameCoordinateWeldStillPhysical ≡ true
modeRatioSameCoordinateWeldStillPhysicalIsTrue = refl

positiveCandidateAndNoSubgapAfterPaymentsCompilerOwned : Bool
positiveCandidateAndNoSubgapAfterPaymentsCompilerOwned = true

positiveCandidateAndNoSubgapAfterPaymentsCompilerOwnedIsTrue :
  positiveCandidateAndNoSubgapAfterPaymentsCompilerOwned ≡ true
positiveCandidateAndNoSubgapAfterPaymentsCompilerOwnedIsTrue = refl

routeSDirectPositiveGapCompilerLevel : ProofLevel
routeSDirectPositiveGapCompilerLevel = machineChecked

sameHamiltonianSpectralDecompositionLevel : ProofLevel
sameHamiltonianSpectralDecompositionLevel =
  R305.round305SameHamiltonianSpectralDecompositionLevel

transferEnergyDecayCoordinateLevel : ProofLevel
transferEnergyDecayCoordinateLevel =
  R305.round305PhysicalTransferEnergyDecayCoordinateLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
