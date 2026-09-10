{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectPositiveSubgapExclusionRound303Exact where

------------------------------------------------------------------------
-- ROUND303 / DIRECT POSITIVE-SUBGAP EXCLUSION WITHOUT OLD RATE RECORDS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Product using (proj₁; proj₂)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record DirectPositiveSubgapExclusionPayment
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    (coordinate : R302.TransferEnergyDecayRatioCoordinate Energy) : Set₁ where
  field
    modeRatioWeld : R302.ModeRatioUsesTransferCoordinate decomposition coordinate
    continuumUpper : R301.ContinuumSelectedCorrelationUpper decomposition
    geometricDominance : R293.RationalGeometricDominance

open DirectPositiveSubgapExclusionPayment public

noPositiveSubgapMode :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {coordinate : R302.TransferEnergyDecayRatioCoordinate Energy} →
  DirectPositiveSubgapExclusionPayment decomposition coordinate →
  ∀ energy (mode : R297.SubgapMode family energy) →
  R302.PositiveEnergy coordinate energy →
  R302.StrictlyBelow coordinate energy (R302.candidateEnergy coordinate) →
  Gap.Empty
noPositiveSubgapMode
    {family = family} {decomposition = decomposition} {coordinate = coordinate}
    payment energy mode positive below =
  let
    observable = R297.modeObservableFromActualNonzeroFamily family energy mode
    weight = R300.selectedOverlapWeight decomposition energy mode
    ratio = R300.subgapRatio decomposition energy mode
    ratioBounds = R302.positiveSubgapRatioBounds
      (modeRatioWeld payment) energy mode positive below
    witness = R293.eventuallySlowDominatesFast
      (geometricDominance payment)
      Shell.quarter weight ratio
      R274.quarterNonnegative
      (R300.selectedOverlapWeightPositive decomposition energy mode)
      (proj₁ ratioBounds)
      (proj₂ ratioBounds)
    time = fst witness
    upperStrictlyBelowLower = snd witness
    lowerBelowCorrelation =
      R300.spectralComponentBelowCorrelation decomposition energy mode time
    correlationBelowUpper = continuumUpper payment observable time
  in
  R293.strictSandwichImpossible
    lowerBelowCorrelation correlationBelowUpper upperStrictlyBelowLower

record Round303Boundary : Set where
  constructor round303-boundary
  field
    oldModeIndexedRateRecordMandatory : Bool
    oldModeIndexedRateRecordMandatoryIsFalse :
      oldModeIndexedRateRecordMandatory ≡ false

    separateSubgapRateAndCandidateRatePayments : Bool
    separateSubgapRateAndCandidateRatePaymentsIsFalse :
      separateSubgapRateAndCandidateRatePayments ≡ false

    positiveSubgapExclusionAfterPrimitivePaymentsCompilerOwned : Bool
    positiveSubgapExclusionAfterPrimitivePaymentsCompilerOwnedIsTrue :
      positiveSubgapExclusionAfterPrimitivePaymentsCompilerOwned ≡ true

canonicalRound303Boundary : Round303Boundary
canonicalRound303Boundary = round303-boundary false refl false refl true refl

round303PositiveSubgapExclusionCompilerLevel : ProofLevel
round303PositiveSubgapExclusionCompilerLevel = machineChecked

round303SpectralDecompositionLevel : ProofLevel
round303SpectralDecompositionLevel = R300.round300SameHamiltonianPositiveSpectralDecompositionLevel

round303TransferEnergyDecayCoordinateLevel : ProofLevel
round303TransferEnergyDecayCoordinateLevel = R302.round302PhysicalTransferEnergyDecayCoordinateLevel
