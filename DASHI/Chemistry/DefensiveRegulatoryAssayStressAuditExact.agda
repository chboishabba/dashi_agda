module DASHI.Chemistry.DefensiveRegulatoryAssayStressAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact as Coverage

------------------------------------------------------------------------
-- GENERAL DEFENSIVE ASSAY-STRESS METHOD
--
-- This module deliberately does NOT attribute the method to the speaker in the
-- supplied screenshot.  The reusable object is a repository-native defensive
-- audit pattern: search the declared compliance observation language for a
-- collision between states that matter to a safety/quality consumer.
--
-- A credible real-world witness is conditioned on evidence about candidate
-- availability/use relevance, actual screening scope, analytical mechanism,
-- matrix/preparation effects, LOD/LOQ and decision rules.  The formal method
-- does not provide a list of chemicals for evading a screen and does not infer
-- an actual regulatory bypass from a hypothetical witness.
------------------------------------------------------------------------

record DefensiveAssayStressWitness
    {Fine Compliance SafetyCoordinate : Set}
    (observeCompliance : Fine → Compliance)
    (safetyCoordinate : Fine → SafetyCoordinate) : Set₁ where
  constructor defensiveAssayStressWitness
  field
    leftState rightState : Fine
    sameComplianceObservation :
      observeCompliance leftState ≡ observeCompliance rightState
    safetyCoordinateDiffers :
      safetyCoordinate leftState ≡ safetyCoordinate rightState → ⊥

    candidateAvailabilityReference : String
    useRelevanceReference : String
    regulatoryLimitRouteReference : String
    actualScreeningScopeReference : String
    extractionAndPreparationReference : String
    signalAndDetectorReference : String
    lodLoqReference : String
    decisionRuleReference : String
    safetyRelevanceReference : String

open DefensiveAssayStressWitness public

stressWitnessGivesNonFactorability :
  ∀ {Fine Compliance SafetyCoordinate}
    {observeCompliance : Fine → Compliance}
    {safetyCoordinate : Fine → SafetyCoordinate} →
  DefensiveAssayStressWitness observeCompliance safetyCoordinate →
  NonFactor.NonFactorabilityWitness observeCompliance safetyCoordinate
stressWitnessGivesNonFactorability witness =
  NonFactor.nonFactorabilityWitness
    (leftState witness)
    (rightState witness)
    (sameComplianceObservation witness)
    (safetyCoordinateDiffers witness)

stressWitnessRefutesCompleteRecovery :
  ∀ {Fine Compliance SafetyCoordinate}
    {observeCompliance : Fine → Compliance}
    {safetyCoordinate : Fine → SafetyCoordinate} →
  DefensiveAssayStressWitness observeCompliance safetyCoordinate →
  NonFactor.FactorsThrough observeCompliance safetyCoordinate → ⊥
stressWitnessRefutesCompleteRecovery witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (stressWitnessGivesNonFactorability witness)

------------------------------------------------------------------------
-- The existing synthetic #660 specimen is only a logical calibration of this
-- generic method.  Its strings explicitly say that no real availability,
-- method or toxicology evidence has been supplied.
------------------------------------------------------------------------

syntheticCoverageStressWitness :
  DefensiveAssayStressWitness
    Coverage.complianceSurface
    Coverage.offPanelPresence
syntheticCoverageStressWitness =
  defensiveAssayStressWitness
    Coverage.cleanPassingBatch
    Coverage.offPanelPresentPassingBatch
    refl
    (λ ())
    "synthetic calibration only; no real candidate availability claim"
    "synthetic calibration only; no real use-relevance claim"
    "synthetic calibration only; no real regulatory-limit-route claim"
    "finite declared observation surface only; not an Australian laboratory scope"
    "synthetic calibration only; no extraction/preparation receipt"
    "synthetic calibration only; no detector receipt"
    "synthetic calibration only; no LOD/LOQ receipt"
    "same compliancePass constructor in the finite witness"
    "finite consumer-relevant coordinate; not a toxicology effect-size claim"

syntheticStressWitnessRefutesRecovery :
  NonFactor.FactorsThrough
    Coverage.complianceSurface Coverage.offPanelPresence → ⊥
syntheticStressWitnessRefutesRecovery =
  stressWitnessRefutesCompleteRecovery syntheticCoverageStressWitness

------------------------------------------------------------------------
-- Evidence-completeness gate for promotion from a logical collision to a real
-- assay-robustness finding.  Strings are provenance locators; the Boolean
-- statuses are intentionally separate so merely writing a citation does not
-- inhabit the promotion gate.
------------------------------------------------------------------------

record RealAssayStressEvidence : Set where
  constructor realAssayStressEvidence
  field
    candidateAvailabilityEstablished : Bool
    useRelevanceEstablished : Bool
    regulatoryRouteEstablished : Bool
    actualScreeningScopeEstablished : Bool
    extractionMechanismEstablished : Bool
    detectorMechanismEstablished : Bool
    lodLoqEstablished : Bool
    safetyRelevanceEstablished : Bool
    evidenceReference : String

open RealAssayStressEvidence public

record RealAssayStressPromotionGate (evidence : RealAssayStressEvidence) : Set where
  constructor realAssayStressPromotionGate
  field
    availabilityReady : candidateAvailabilityEstablished evidence ≡ true
    useReady : useRelevanceEstablished evidence ≡ true
    regulatoryReady : regulatoryRouteEstablished evidence ≡ true
    scopeReady : actualScreeningScopeEstablished evidence ≡ true
    extractionReady : extractionMechanismEstablished evidence ≡ true
    detectorReady : detectorMechanismEstablished evidence ≡ true
    thresholdReady : lodLoqEstablished evidence ≡ true
    safetyReady : safetyRelevanceEstablished evidence ≡ true

open RealAssayStressPromotionGate public

------------------------------------------------------------------------
-- Defensive response is an information-design problem, not an instruction to
-- exploit the collision.  The existing actionability calculus can compare
-- declared measurement/fidelity moves such as broader validated measurement,
-- increased sensitivity, orthogonal measurement or replication.
------------------------------------------------------------------------

record DefensiveAssayRepairSearch : Set₁ where
  constructor defensiveAssayRepairSearch
  field
    problem : Choice.ActionabilityProblem
    DeclaredMove : Choice.InformationMove → Set
    selectedRepair : Choice.CheapestResolvingMove problem DeclaredMove
    assayDesignReference : String
    methodValidationReference : String
    regulatoryAuthorityReference : String

open DefensiveAssayRepairSearch public

------------------------------------------------------------------------
-- Screenshot provenance: an application claim, not ownership of the generic
-- method and not evidence that the real-world promotion gate is inhabited.
------------------------------------------------------------------------

record ScreenshotApplicationBoundary : Set where
  constructor screenshotApplicationBoundary
  field
    screenshotShowsAClaimOfSystemGaming : Bool
    screenshotOwnsGenericAssayStressMethod : Bool
    screenshotAloneInhabitsRealStressPromotionGate : Bool
    genericMethodCanBeAppliedToOtherScreeningSystems : Bool

canonicalScreenshotApplicationBoundary : ScreenshotApplicationBoundary
canonicalScreenshotApplicationBoundary =
  screenshotApplicationBoundary true false false true
