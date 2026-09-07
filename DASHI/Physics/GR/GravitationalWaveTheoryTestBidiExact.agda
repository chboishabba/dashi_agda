module DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr

------------------------------------------------------------------------
-- GRAVITATIONAL-WAVE THEORY TESTS
--
-- A detected strain/timing signal is separated from the inference layer used to
-- test GR or alternatives.  Theory comparators are attributed predictions welded
-- to the exact calibrated observation, not free String labels.
------------------------------------------------------------------------

data WaveTestFamily : Set where
  inspiralPhaseConsistency : WaveTestFamily
  mergerRingdownConsistency : WaveTestFamily
  dispersionPropagation : WaveTestFamily
  polarizationContent : WaveTestFamily
  remnantConsistency : WaveTestFamily
  stochasticCorrelationShape : WaveTestFamily
  cosmologicalPropagation : WaveTestFamily

data WaveTestResidual : Set where
  missingCalibratedData : WaveTestResidual
  missingGRWaveformComparator : WaveTestResidual
  missingAlternativeComparator : WaveTestResidual
  missingDetectorResponse : WaveTestResidual
  missingPropagationModel : WaveTestResidual
  missingPopulationModel : WaveTestResidual
  missingSystematicErrorBudget : WaveTestResidual
  residualConsistentWithZero : WaveTestResidual
  residualRequiresFurtherModelComparison : WaveTestResidual

data TestObservable : Set where
  phaseEvolution : TestObservable
  ringdownSpectrum : TestObservable
  frequencyDependentArrival : TestObservable
  networkPolarizationResponse : TestObservable
  inspiralVsRemnantParameters : TestObservable
  angularTimingCorrelation : TestObservable
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
    grPredictionIsGR :
      Pred.theoryFamily (Attr.prediction grPrediction)
        ≡ Pred.generalRelativityTheory
    grWeld :
      Pred.PredictionObservationWeld
        (Attr.prediction grPrediction)
        observation
    alternativeWeld :
      Pred.PredictionObservationWeld
        (Attr.prediction alternativePrediction)
        observation
    systematicBudget : String
    resultCarrier : Sources.ObservationAttributedSource
    comparisonLineage :
      Attr.PairedPredictionComparisonLineage
        grPrediction alternativePrediction observation
    deviationDetected : Bool

open WaveTheoryTestReceipt public

------------------------------------------------------------------------
-- Reverse test design.
------------------------------------------------------------------------

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
cutsetFor family =
  wave-theory-reverse-cutset family
    true true true true true true true true false

------------------------------------------------------------------------
-- Introspective firewall: a comparator label alone cannot inhabit either
-- attributed prediction, its same-observation weld, or the bound lineage.
------------------------------------------------------------------------

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
-- Current source-backed GR-test status.
------------------------------------------------------------------------

record CurrentGWTheoryTestStatus : Set where
  constructor current-gw-theory-test-status
  field
    source : Sources.ObservationAttributedSource
    currentLVKSuiteTestsGR : Bool
    currentLVKSuiteDetectsRequiredDeviationFromGR : Bool
    tighterDeviationBoundsReported : Bool
    noDeviationMeansGRUniquelyEstablished : Bool

canonicalCurrentGWTheoryTestStatus : CurrentGWTheoryTestStatus
canonicalCurrentGWTheoryTestStatus =
  current-gw-theory-test-status
    Sources.lvkGRTests2026 true false true false

------------------------------------------------------------------------
-- Cross-scale observation firewall.
------------------------------------------------------------------------

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
