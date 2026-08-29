module DASHI.Programmes.ResearchProgrammeExact where

open import DASHI.Core.Prelude
open import DASHI.Core.PredictionEnvelopeExact

------------------------------------------------------------------------
-- Cross-repository research-programme registry.
--
-- Satellite repositories remain computational / experimental laboratories.
-- This layer records the formal problem class, formal owner family, and the
-- evidence boundary required before a satellite result can be promoted into a
-- theorem-facing claim.  It intentionally does not reimplement satellite code.
------------------------------------------------------------------------

data SatelliteRepository : Set where
  dashiCFD dashiBRAIN dashiQ dashifine DASHIg dashiCORE FRACDASH dashitest dashiRTX : SatelliteRepository

data ProblemClass : Set where
  fluidClosure
  connectomeKernelClosure
  quantumProjectionPhysics
  spectralLearningGeometry
  grokkingValidation
  coreSemanticReference
  executableCompilation
  heterogeneousExperimentHarness
  lightTransportGeometry : ProblemClass

data FormalOwnerFamily : Set where
  navierStokesClosure
  biologyNetworkGeometry
  physicsFoundations
  corePredictionInference
  coreKernelDefectAdmissibility
  foundationsClaimTransport
  fractranCrossPollination
  ultrametricMDLGeometry : FormalOwnerFamily

data CoverageDepth : Set where
  theoremDeep
  explicitBridge
  semanticAdapter
  frontierAdapter : CoverageDepth

record ResearchProgramme : Set where
  constructor researchProgramme
  field
    repository : SatelliteRepository
    problemClass : ProblemClass
    primaryOwner : FormalOwnerFamily
    secondaryOwner : FormalOwnerFamily
    coverageDepth : CoverageDepth

    -- Mechanical completeness cutset: every registered programme must have a
    -- literal formal owner and must refuse promotion without an evidence
    -- receipt.  The Bool witnesses make accidental documentation-only entries
    -- fail to inhabit this record.
    formalOwnerAssigned : Bool
    formalOwnerAssignedIsTrue : formalOwnerAssigned ≡ true

    promotionRequiresEvidenceReceipt : Bool
    promotionRequiresEvidenceReceiptIsTrue :
      promotionRequiresEvidenceReceipt ≡ true

    -- PR #636 boundary: programme adapters share the deterministic prediction
    -- envelope semantics and do not silently introduce probability weights.
    predictionBoundary : PredictionEnvelopeBoundary

ownerAssigned : ResearchProgramme → Bool
ownerAssigned p = ResearchProgramme.formalOwnerAssigned p

promotionReceiptRequired : ResearchProgramme → Bool
promotionReceiptRequired p = ResearchProgramme.promotionRequiresEvidenceReceipt p

allRegisteredProgrammesUseReceiptGate :
  (p : ResearchProgramme) → promotionReceiptRequired p ≡ true
allRegisteredProgrammesUseReceiptGate p =
  ResearchProgramme.promotionRequiresEvidenceReceiptIsTrue p

allRegisteredProgrammesHaveFormalOwner :
  (p : ResearchProgramme) → ownerAssigned p ≡ true
allRegisteredProgrammesHaveFormalOwner p =
  ResearchProgramme.formalOwnerAssignedIsTrue p

------------------------------------------------------------------------
-- Experiment/proof feedback-loop boundary.
--
-- A satellite may produce candidate evidence.  The adapter only promises that
-- promotion is receipt-gated; it does not assert that any concrete experiment
-- is adequate, calibrated, or theorem-closing.
------------------------------------------------------------------------

record ResearchFeedbackBoundary : Set where
  constructor researchFeedbackBoundary
  field
    experimentOutputIsProofByItself : Bool
    experimentOutputIsProofByItselfIsFalse : experimentOutputIsProofByItself ≡ false

    theoremMaySpecifyNextMeasurement : Bool
    theoremMaySpecifyNextMeasurementIsTrue : theoremMaySpecifyNextMeasurement ≡ true

    failedRouteMayRemainFormalKnowledge : Bool
    failedRouteMayRemainFormalKnowledgeIsTrue : failedRouteMayRemainFormalKnowledge ≡ true

canonicalResearchFeedbackBoundary : ResearchFeedbackBoundary
canonicalResearchFeedbackBoundary =
  researchFeedbackBoundary
    false refl
    true refl
    true refl
