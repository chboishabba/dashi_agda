module DASHI.Interop.ITIRSuiteNormalizedCompilerStageParityWitnessExact where

open import DASHI.Core.Prelude

import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Interop.ITIRSensiBlawStreamlineArchitecture as Architecture

------------------------------------------------------------------------
-- DEFINITIONAL PARITY WITNESS
--
-- Every normalized concept introduced from the pinned ITIR-suite README is
-- definitionally routed into the pre-existing ITIR/SensiBlaw Agda stage
-- architecture.  These `refl` witnesses make parity compiler-visible rather
-- than leaving the alignment in comments.
------------------------------------------------------------------------

record NormalizedStageParityWitness : Set where
  constructor normalizedStageParityWitness
  field
    sourceArtifactParity :
      ITIR.stageFor ITIR.sourceArtifact ≡ Architecture.captureStage
    provenanceAnchorParity :
      ITIR.stageFor ITIR.provenanceAnchor ≡ Architecture.fileAndTranscriptStage
    contextEnvelopeParity :
      ITIR.stageFor ITIR.contextEnvelope ≡ Architecture.textSubstrateStage
    canonicalIdentityParity :
      ITIR.stageFor ITIR.canonicalIdentity ≡ Architecture.actorEventStage
    observedSignalParity :
      ITIR.stageFor ITIR.observedSignal ≡ Architecture.actorEventStage
    compiledStateParity :
      ITIR.stageFor ITIR.compiledState ≡ Architecture.persistedViewStage
    reviewableClaimParity :
      ITIR.stageFor ITIR.reviewableClaim ≡ Architecture.claimHarmEvidenceStage
    promotedRecordParity :
      ITIR.stageFor ITIR.promotedRecord ≡ Architecture.correctionReceiptStage
    derivedProductParity :
      ITIR.stageFor ITIR.derivedProduct ≡ Architecture.graphProjectionStage
    followObligationParity :
      ITIR.stageFor ITIR.followObligation ≡ Architecture.claimHarmEvidenceStage
    unresolvedPressureParity :
      ITIR.stageFor ITIR.abstentionHoldUnresolvedPressure
      ≡ Architecture.claimHarmEvidenceStage
    operatorInspectionParity :
      ITIR.stageFor ITIR.operatorInspectionSurface ≡ Architecture.streamlineStage
    boundedUnionParity :
      ITIR.stageFor ITIR.boundedUnionSurface ≡ Architecture.graphProjectionStage

open NormalizedStageParityWitness public

canonicalNormalizedStageParityWitness : NormalizedStageParityWitness
canonicalNormalizedStageParityWitness =
  normalizedStageParityWitness
    refl refl refl refl refl refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Owner parity for the high-value current lane.
------------------------------------------------------------------------

record CurrentLaneOwnerParity : Set where
  constructor currentLaneOwnerParity
  field
    sourceOwnedByCapture : ITIR.ownerFor ITIR.sourceArtifact ≡ ITIR.captureOwner
    provenanceOwnedByCapture :
      ITIR.ownerFor ITIR.provenanceAnchor ≡ ITIR.captureOwner
    compiledStateOwnedByStateCompiler :
      ITIR.ownerFor ITIR.compiledState ≡ ITIR.stateCompilationOwner
    reviewOwnedByDeterministicReview :
      ITIR.ownerFor ITIR.reviewableClaim ≡ ITIR.deterministicReviewOwner
    promotionOwnedByDeterministicReview :
      ITIR.ownerFor ITIR.promotedRecord ≡ ITIR.deterministicReviewOwner

canonicalCurrentLaneOwnerParity : CurrentLaneOwnerParity
canonicalCurrentLaneOwnerParity = currentLaneOwnerParity refl refl refl refl refl
