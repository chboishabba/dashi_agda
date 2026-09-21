module DASHI.Core.BackendSelectionPolicyExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- EVIDENCE-BASED PYTHON/RUST SELECTION
------------------------------------------------------------------------

data BackendRecommendation : Set where
  keepPythonReference : BackendRecommendation
  fixInvalidationFirst : BackendRecommendation
  rustCoreCandidate : BackendRecommendation

record BackendMeasurement : Set where
  constructor backendMeasurement
  field
    sampleCount : Nat
    patchP95Milliseconds : Nat
    patchSharePercent : Nat
    affectedModulesP95 : Nat

open BackendMeasurement public

record BackendSelectionThresholds : Set where
  constructor backendSelectionThresholds
  field
    minimumSamples : Nat
    patchP95LimitMilliseconds : Nat
    patchShareLimitPercent : Nat
    affectedModulesP95Limit : Nat

open BackendSelectionThresholds public

canonicalBackendSelectionThresholds :
  BackendSelectionThresholds
canonicalBackendSelectionThresholds =
  backendSelectionThresholds
    50
    50
    35
    128

-- The executable Python policy performs the numeric comparisons. This formal
-- layer fixes the admissible decision ordering: evidence first, invalidation
-- pathology before implementation-language migration.
data BackendDecisionReason : Set where
  insufficientEvidence : BackendDecisionReason
  excessiveInvalidationFanout : BackendDecisionReason
  measuredPatchHotspot : BackendDecisionReason
  measuredWithinEnvelope : BackendDecisionReason

recommendationForReason :
  BackendDecisionReason →
  BackendRecommendation
recommendationForReason insufficientEvidence =
  keepPythonReference
recommendationForReason excessiveInvalidationFanout =
  fixInvalidationFirst
recommendationForReason measuredPatchHotspot =
  rustCoreCandidate
recommendationForReason measuredWithinEnvelope =
  keepPythonReference

insufficientEvidenceDoesNotPromoteRust :
  recommendationForReason insufficientEvidence
    ≡ keepPythonReference
insufficientEvidenceDoesNotPromoteRust = refl

fanoutProblemIsNotRustEvidence :
  recommendationForReason excessiveInvalidationFanout
    ≡ fixInvalidationFirst
fanoutProblemIsNotRustEvidence = refl

measuredHotspotAdmitsRustCandidate :
  recommendationForReason measuredPatchHotspot
    ≡ rustCoreCandidate
measuredHotspotAdmitsRustCandidate = refl

record BackendSelectionBoundary : Set where
  constructor backendSelectionBoundary
  field
    rustMayBeChosenWithoutMeasurements : Bool
    rustMayBeChosenWithoutMeasurementsIsFalse :
      rustMayBeChosenWithoutMeasurements ≡ false

    highFanoutMayBeHiddenByFasterLanguage : Bool
    highFanoutMayBeHiddenByFasterLanguageIsFalse :
      highFanoutMayBeHiddenByFasterLanguage ≡ false

    rendererMustMoveToRustWithSemanticCore : Bool
    rendererMustMoveToRustWithSemanticCoreIsFalse :
      rendererMustMoveToRustWithSemanticCore ≡ false

canonicalBackendSelectionBoundary :
  BackendSelectionBoundary
canonicalBackendSelectionBoundary =
  backendSelectionBoundary
    false refl
    false refl
    false refl
