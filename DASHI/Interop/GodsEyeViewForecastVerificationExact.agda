module DASHI.Interop.GodsEyeViewForecastVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact as WorldLoop
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as ProofExperiment\nimport DASHI.Core.ProviderNeutralWorldQueryAlgebraExact as Query
import DASHI.Statistics.ForecastVerificationKernelExact as Kernel
import DASHI.Statistics.ForecastResolutionSelectionExact as Lifecycle
import DASHI.Statistics.ForecastCalibrationDecompositionExact as Calibration
import DASHI.Applications.WorldMonitorForecastScorecardExact as WorldMonitor

------------------------------------------------------------------------
-- GODS-EYE-VIEW x FORECAST VERIFICATION
--
-- Forecast verification is a consumer of the existing world-research loop:
--
--   score/resolution residual
--      -> consumer-relevant missing coordinate
--      -> admitted information move / proof-search refinement
--      -> bounded acquisition
--      -> semantic assessment
--      -> world-model recomputation.
--
-- Search/acquisition never becomes proof payment merely because a backend
-- returned a result.
------------------------------------------------------------------------

data ForecastResearchResidualKind : Set where
  sourceProvenanceResidual
  forecastTimeAvailabilityResidual
  mechanismResidual
  regimeResidual
  calibrationResidual
  scorabilitySelectionResidual
  resolutionObserverResidual
  comparatorResidual
  objectDecompositionResidual :
    ForecastResearchResidualKind

record ForecastResearchResidual : Set where
  constructor forecast-research-residual
  field
    kind : ForecastResearchResidualKind
    forecastReference : String
    consumerReference : String
    missingCoordinateReference : String
    currentWorldReference : String
    forecastTimeCutReference : String
    answerChangingReference : String
    ontologyOwnerReference : String
    residualReference : String

open ForecastResearchResidual public

data ForecastAcquisitionRoute : Set where
  localWorldRoute
  wikidataRoute
  wikipediaIbrahimRoute
  officialSourceRoute
  webSearchRoute
  scholarlyIndexRoute
  citationSnowballRoute
  physicalMeasurementRoute :
    ForecastAcquisitionRoute

record ForecastResidualAcquisitionPlan
    (residual : ForecastResearchResidual) : Set where
  constructor forecast-residual-acquisition-plan
  field
    route : ForecastAcquisitionRoute
    proofSearchHypothesisReference : String
    hypothesisFamily : Query.WorldSearchHypothesisFamily
    compiledQuery : Query.WorldProviderCompiledQuery
    selectedInformationMove : Choice.InformationMove
    expectedFibreRefinementReference : String
    admissibilityReference : String
    selectionReference : String

open ForecastResidualAcquisitionPlan public

record ForecastAcquisitionAssessment
    (residual : ForecastResearchResidual)
    (plan : ForecastResidualAcquisitionPlan residual) : Set where
  constructor forecast-acquisition-assessment
  field
    acquiredArtifactReference : String
    sourceInspectionReference : String
    pnfReentryReference : String
    objectIdentityWeldReference : String
    temporalAssessmentReference : String
    sourceProvenanceReference : String
    resultAssessmentReference : String
    worldLoopDisposition : WorldLoop.ObservationReturnDisposition
    updatedWorldReference : String
    updatedResidualReference : String
    provenanceAppendOnlyReference : String

open ForecastAcquisitionAssessment public

record ForecastResearchIteration : Set₁ where
  constructor forecast-research-iteration
  field
    residual : ForecastResearchResidual
    plan : ForecastResidualAcquisitionPlan residual
    assessment : ForecastAcquisitionAssessment residual plan
    priorCompatibleFibreReference : String
    posteriorCompatibleFibreReference : String
    consumerClosureReference : String
    iterationReference : String

open ForecastResearchIteration public

------------------------------------------------------------------------
-- Existing canonical owners are reused, not copied.
------------------------------------------------------------------------

worldResearchLoopBoundary :
  WorldLoop.ExecutableWorldResearchLoopBoundary
worldResearchLoopBoundary =
  WorldLoop.canonicalExecutableWorldResearchLoopBoundary

actionabilityChoiceBoundary :
  Choice.ActionabilityChoiceBoundary
actionabilityChoiceBoundary =
  Choice.canonicalActionabilityChoiceBoundary

proofExperimentBoundary :
  ProofExperiment.ProofSearchExperimentalParetoBoundary
proofExperimentBoundary =
  ProofExperiment.canonicalProofSearchExperimentalParetoBoundary

worldQueryBoundary :
  Query.ProviderNeutralWorldQueryBoundary
worldQueryBoundary =
  Query.canonicalProviderNeutralWorldQueryBoundary

forecastKernelBoundary :
  Kernel.ForecastVerificationKernelBoundary
forecastKernelBoundary =
  Kernel.canonicalForecastVerificationKernelBoundary

forecastLifecycleBoundary :
  Lifecycle.ForecastResolutionSelectionBoundary
forecastLifecycleBoundary =
  Lifecycle.canonicalForecastResolutionSelectionBoundary

forecastCalibrationBoundary :
  Calibration.ForecastCalibrationBoundary
forecastCalibrationBoundary =
  Calibration.canonicalForecastCalibrationBoundary

worldMonitorBoundary :
  WorldMonitor.WorldMonitorForecastBoundary
worldMonitorBoundary =
  WorldMonitor.canonicalWorldMonitorForecastBoundary

------------------------------------------------------------------------
-- Return-loop fixture: a forecast explanation can split rather than close.
------------------------------------------------------------------------

forecastMechanismSplitShape : WorldLoop.ObservationAssessmentShape
forecastMechanismSplitShape =
  WorldLoop.observation-assessment-shape
    true
    true
    false
    true
    false

forecastMechanismSplitDisposition :
  WorldLoop.classifyObservationReturn forecastMechanismSplitShape
  ≡ WorldLoop.splitDiagnosis
forecastMechanismSplitDisposition = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record GodsEyeViewForecastVerificationBoundary : Set where
  constructor gods-eye-view-forecast-verification-boundary
  field
    searchResultEqualsResidualPayment : Bool
    searchResultEqualsResidualPaymentIsFalse :
      searchResultEqualsResidualPayment ≡ false

    everyUnknownCoordinateMustBeSearched : Bool
    everyUnknownCoordinateMustBeSearchedIsFalse :
      everyUnknownCoordinateMustBeSearched ≡ false

    consumerRelevantResidualGuidesAcquisition : Bool
    consumerRelevantResidualGuidesAcquisitionIsTrue :
      consumerRelevantResidualGuidesAcquisition ≡ true

    acquiredArtifactMustReenterPNF : Bool
    acquiredArtifactMustReenterPNFIsTrue :
      acquiredArtifactMustReenterPNF ≡ true

    forecastTimeCutMustSurviveHindsightResearch : Bool
    forecastTimeCutMustSurviveHindsightResearchIsTrue :
      forecastTimeCutMustSurviveHindsightResearch ≡ true

    newEvidenceMaySplitExplanationFibre : Bool
    newEvidenceMaySplitExplanationFibreIsTrue :
      newEvidenceMaySplitExplanationFibre ≡ true

canonicalGodsEyeViewForecastVerificationBoundary :
  GodsEyeViewForecastVerificationBoundary
canonicalGodsEyeViewForecastVerificationBoundary =
  gods-eye-view-forecast-verification-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
