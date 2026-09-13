module DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr

data WaveTestFamily : Set where
  inspiralPhaseConsistency mergerRingdownConsistency dispersionPropagation
    polarizationContent remnantConsistency stochasticCorrelationShape
    cosmologicalPropagation : WaveTestFamily

data WaveTestResidual : Set where
  missingCalibratedData missingGRWaveformComparator missingAlternativeComparator
    missingDetectorResponse missingPropagationModel missingPopulationModel
    missingSystematicErrorBudget residualConsistentWithZero
    residualRequiresFurtherModelComparison : WaveTestResidual

data TestObservable : Set where
  phaseEvolution ringdownSpectrum frequencyDependentArrival
    networkPolarizationResponse inspiralVsRemnantParameters angularTimingCorrelation
    distanceRedshiftRelation : TestObservable

testObservable : WaveTestFamily → TestObservable
testObservable inspiralPhaseConsistency = phaseEvolution
testObservable mergerRingdownConsistency = ringdownSpectrum
testObservable dispersionPropagation = frequencyDependentArrival
testObservable polarizationContent = networkPolarizationResponse
testObservable remnantConsistency = inspiralVsRemnantParameters
testObservable stochasticCorrelationShape = angularTimingCorrelation
testObservable cosmologicalPropagation = distanceRedshiftRelation

record WaveTheoryTestReceipt : Set where
  constructor wave-theory-test-receipt
  field
    observation : Obs.GravitationalObservationReceipt
    testFamily : WaveTestFamily
    testedObservable : TestObservable
    testedObservableMatches : testObservable testFamily ≡ testedObservable
    testProjectionCarrier : String
    grPrediction : Attr.AttributedGravitationalPrediction
    alternativePrediction : Attr.AttributedGravitationalPrediction
    grPredictionIsGR : Pred.theoryFamily (Attr.prediction grPrediction) ≡ Pred.generalRelativityTheory
    grWeld : Pred.PredictionObservationWeld (Attr.prediction grPrediction) observation
    alternativeWeld : Pred.PredictionObservationWeld (Attr.prediction alternativePrediction) observation
    systematicBudget : String
    resultCarrier : Sources.ObservationAttributedSource
    comparisonLineage : Attr.PairedPredictionComparisonLineage grPrediction alternativePrediction observation
    deviationDetected : Bool
open WaveTheoryTestReceipt public

record WaveTheoryReverseCutset : Set where
  constructor wave-theory-reverse-cutset
  field
    testFamily : WaveTestFamily
    requiresCalibratedObservation : Bool
    requiresAttributedGRPrediction : Bool
    requiresAttributedAlternativePrediction : Bool
    requiresSameObservableGRPrediction : Bool
    requiresSameObservableAlternativePrediction : Bool
    requiresBoundComparisonLineage : Bool
    requiresDetectorResponseModel : Bool
    requiresSystematicBudget : Bool
    residualAlonePromotesAlternativeGravity : Bool

cutsetFor : WaveTestFamily → WaveTheoryReverseCutset
cutsetFor family = wave-theory-reverse-cutset family true true true true true true true true false

record WaveComparatorAttributionBoundary : Set where
  constructor wave-comparator-attribution-boundary
  field
    comparatorStringCountsAsAttributedPrediction : Bool
    sameTheoryCarrierCountsAsSupportedClaimScope : Bool
    attributedPredictionAloneCountsAsObservationMatch : Bool
    genericDerivedLineageAutomaticallyMatchesConsumedInputs : Bool
    derivedComparisonCountsAsExternalSourceStatement : Bool

canonicalWaveComparatorAttributionBoundary : WaveComparatorAttributionBoundary
canonicalWaveComparatorAttributionBoundary =
  wave-comparator-attribution-boundary false false false false false

------------------------------------------------------------------------
-- Positive current-status propositions are exact source-entitled claims.  The
-- uniqueness conclusion remains a DASHI boundary judgment and stays false.
------------------------------------------------------------------------

record CurrentGWTheoryTestStatus : Set where
  constructor current-gw-theory-test-status
  field
    currentLVKSuiteTestsGR :
      Sources.SourceEntitledObservationClaim Sources.lvkCurrentGRTestSuiteClaim
    currentLVKSuiteNoRequiredDeviation :
      Sources.SourceEntitledObservationClaim Sources.lvkNoRequiredDeviationClaim
    tighterDeviationBoundsReported :
      Sources.SourceEntitledObservationClaim Sources.lvkTighterDeviationBoundsClaim
    noDeviationMeansGRUniquelyEstablished : Bool

canonicalCurrentGWTheoryTestStatus : CurrentGWTheoryTestStatus
canonicalCurrentGWTheoryTestStatus =
  current-gw-theory-test-status
    (Sources.canonicalSourceEntitledClaim Sources.lvkCurrentGRTestSuiteClaim)
    (Sources.canonicalSourceEntitledClaim Sources.lvkNoRequiredDeviationClaim)
    (Sources.canonicalSourceEntitledClaim Sources.lvkTighterDeviationBoundsClaim)
    false

record GravitationalWaveCrossScaleBoundary : Set where
  constructor gravitational-wave-cross-scale-boundary
  field
    compactBinaryAgreementClosesLaboratoryAntigravityClaim : Bool
    laboratoryAnomalyOverturnsCompactBinaryGRTestsByItself : Bool
    nanohertzBackgroundIdentifiesUniqueMicroscopicGravityMechanism : Bool
    crossScaleAgreementMayConstrainCandidateTheory : Bool
    crossScaleTensionMayOpenTheoryResidual : Bool

canonicalGravitationalWaveCrossScaleBoundary : GravitationalWaveCrossScaleBoundary
canonicalGravitationalWaveCrossScaleBoundary =
  gravitational-wave-cross-scale-boundary false false false true true
