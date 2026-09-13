module DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRSensiBlawStreamlineArchitecture as Architecture

------------------------------------------------------------------------
-- ITIR-SUITE README -> AGDA NORMALIZED COMPILER PARITY
--
-- Source-owned terminology pinned to:
--   chboishabba/ITIR-suite README.md
--   commit 24f62fecbec11909bcdb32916801b2315a796513
--
-- This is a parity/ownership compiler only.  It does not manufacture source
-- facts, identity resolutions, legal authority, or promotion receipts.
------------------------------------------------------------------------

itirSuiteRepository : String
itirSuiteRepository = "chboishabba/ITIR-suite"

itirSuiteReadmeCommit : String
itirSuiteReadmeCommit = "24f62fecbec11909bcdb32916801b2315a796513"


data NormalizedCompilerConcept : Set where
  sourceArtifact : NormalizedCompilerConcept
  provenanceAnchor : NormalizedCompilerConcept
  contextEnvelope : NormalizedCompilerConcept
  canonicalIdentity : NormalizedCompilerConcept
  observedSignal : NormalizedCompilerConcept
  compiledState : NormalizedCompilerConcept
  reviewableClaim : NormalizedCompilerConcept
  promotedRecord : NormalizedCompilerConcept
  derivedProduct : NormalizedCompilerConcept
  followObligation : NormalizedCompilerConcept
  abstentionHoldUnresolvedPressure : NormalizedCompilerConcept
  operatorInspectionSurface : NormalizedCompilerConcept
  boundedUnionSurface : NormalizedCompilerConcept


data SuiteOwner : Set where
  captureOwner : SuiteOwner
  stateCompilationOwner : SuiteOwner
  deterministicReviewOwner : SuiteOwner
  integrationOwner : SuiteOwner
  operatorSurfaceOwner : SuiteOwner
  crossDomainOwner : SuiteOwner

ownerFor : NormalizedCompilerConcept → SuiteOwner
ownerFor sourceArtifact = captureOwner
ownerFor provenanceAnchor = captureOwner
ownerFor contextEnvelope = deterministicReviewOwner
ownerFor canonicalIdentity = deterministicReviewOwner
ownerFor observedSignal = deterministicReviewOwner
ownerFor compiledState = stateCompilationOwner
ownerFor reviewableClaim = deterministicReviewOwner
ownerFor promotedRecord = deterministicReviewOwner
ownerFor derivedProduct = deterministicReviewOwner
ownerFor followObligation = deterministicReviewOwner
ownerFor abstentionHoldUnresolvedPressure = deterministicReviewOwner
ownerFor operatorInspectionSurface = operatorSurfaceOwner
ownerFor boundedUnionSurface = crossDomainOwner

------------------------------------------------------------------------
-- Existing DASHI Agda architecture parity.
--
-- The earlier ITIR/SensiBlaw architecture remains the stage owner.  The README
-- normalized concepts refine that architecture rather than replacing it.
------------------------------------------------------------------------

stageFor : NormalizedCompilerConcept → Architecture.PipelineStage
stageFor sourceArtifact = Architecture.captureStage
stageFor provenanceAnchor = Architecture.fileAndTranscriptStage
stageFor contextEnvelope = Architecture.textSubstrateStage
stageFor canonicalIdentity = Architecture.actorEventStage
stageFor observedSignal = Architecture.actorEventStage
stageFor compiledState = Architecture.persistedViewStage
stageFor reviewableClaim = Architecture.claimHarmEvidenceStage
stageFor promotedRecord = Architecture.correctionReceiptStage
stageFor derivedProduct = Architecture.graphProjectionStage
stageFor followObligation = Architecture.claimHarmEvidenceStage
stageFor abstentionHoldUnresolvedPressure = Architecture.claimHarmEvidenceStage
stageFor operatorInspectionSurface = Architecture.streamlineStage
stageFor boundedUnionSurface = Architecture.graphProjectionStage

record NormalizedArtifact : Set₁ where
  constructor normalizedArtifact
  field
    concept : NormalizedCompilerConcept
    stableReference : String
    provenanceReference : String
    contextReference : String
    artifactReceipt : Set

open NormalizedArtifact public

record PromotionReceipt (candidate promoted : NormalizedArtifact) : Set₁ where
  constructor promotionReceipt
  field
    candidateIsReviewable : concept candidate ≡ reviewableClaim
    promotedIsRecord : concept promoted ≡ promotedRecord
    sameClaimIdentityReceipt : Set
    authorityReceipt : Set
    promotionReference : String

open PromotionReceipt public

record DerivationReceipt (source derived : NormalizedArtifact) : Set₁ where
  constructor derivationReceipt
  field
    derivedIsProduct : concept derived ≡ derivedProduct
    sourceIdentityPreservedReceipt : Set
    transformationReceipt : Set
    derivationReference : String

open DerivationReceipt public

record FollowReceipt (pressure follow : NormalizedArtifact) : Set₁ where
  constructor followReceipt
  field
    pressureIsUnresolved :
      concept pressure ≡ abstentionHoldUnresolvedPressure
    followIsObligation : concept follow ≡ followObligation
    boundedTriggerReceipt : Set
    followReference : String

open FollowReceipt public

------------------------------------------------------------------------
-- README invariants compiled as fail-closed boundary bits.
------------------------------------------------------------------------

record ITIRSuiteNormalizedParityBoundary : Set where
  constructor itirSuiteNormalizedParityBoundary
  field
    sourceArtifactAutomaticallyPromoted : Bool
    sourceArtifactAutomaticallyPromotedIsFalse :
      sourceArtifactAutomaticallyPromoted ≡ false

    candidateIdentityEqualsCanonicalIdentity : Bool
    candidateIdentityEqualsCanonicalIdentityIsFalse :
      candidateIdentityEqualsCanonicalIdentity ≡ false

    derivedProductEqualsCanonicalTruth : Bool
    derivedProductEqualsCanonicalTruthIsFalse :
      derivedProductEqualsCanonicalTruth ≡ false

    unresolvedPressureMayRemainVisible : Bool
    unresolvedPressureMayRemainVisibleIsTrue :
      unresolvedPressureMayRemainVisible ≡ true

    followRequiresBoundedTrigger : Bool
    followRequiresBoundedTriggerIsTrue : followRequiresBoundedTrigger ≡ true

    authorityCrossingRequiresPromotionReceipt : Bool
    authorityCrossingRequiresPromotionReceiptIsTrue :
      authorityCrossingRequiresPromotionReceipt ≡ true

    stageArchitectureIsRefinedNotReplaced : Bool
    stageArchitectureIsRefinedNotReplacedIsTrue :
      stageArchitectureIsRefinedNotReplaced ≡ true

canonicalITIRSuiteNormalizedParityBoundary : ITIRSuiteNormalizedParityBoundary
canonicalITIRSuiteNormalizedParityBoundary =
  itirSuiteNormalizedParityBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceArtifactAutomaticallyPromoted : Set where
data CandidateIdentityAutomaticallyCanonical : Set where
data DerivedProductAutomaticallyTruth : Set where
data FollowWithoutBoundedTrigger : Set where
data SideSystemMayReplaceCanonicalReducer : Set where

sourceArtifactDoesNotAutoPromote : SourceArtifactAutomaticallyPromoted → ⊥
sourceArtifactDoesNotAutoPromote ()

candidateIdentityDoesNotAutoResolve : CandidateIdentityAutomaticallyCanonical → ⊥
candidateIdentityDoesNotAutoResolve ()

derivedProductDoesNotAutoBecomeTruth : DerivedProductAutomaticallyTruth → ⊥
derivedProductDoesNotAutoBecomeTruth ()

followRequiresTrigger : FollowWithoutBoundedTrigger → ⊥
followRequiresTrigger ()

sideSystemDoesNotReplaceCanonicalReducer : SideSystemMayReplaceCanonicalReducer → ⊥
sideSystemDoesNotReplaceCanonicalReducer ()
