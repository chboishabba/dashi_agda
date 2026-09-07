module DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- GRAVITATIONAL-WAVE THEORY TESTS
--
-- A detected strain/timing signal is separated from the inference layer used to
-- test GR or alternatives.  Each test family asks for a same-observable
-- comparator rather than treating any residual as "new gravity" by default.
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
    grComparator : String
    alternativeComparator : String
    systematicBudget : String
    resultCarrier : Sources.ObservationAttributedSource
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
    requiresSameObservableGRPrediction : Bool
    requiresDetectorResponseModel : Bool
    requiresSystematicBudget : Bool
    residualAlonePromotesAlternativeGravity : Bool

cutsetFor : WaveTestFamily → WaveTheoryReverseCutset
cutsetFor family =
  wave-theory-reverse-cutset family true true true true false

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
