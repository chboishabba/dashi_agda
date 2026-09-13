module DASHI.Interop.ITIRRecordingManifestSensibLawAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Law.SensibLawRecordingManifestLineageExact as Recording

------------------------------------------------------------------------
-- ITIR NORMALIZED SPINE -> SENSIBLAW RECORDING-LINEAGE ADAPTER
--
-- RecordingManifestLineageExact owns the domain-specific carrier distinctions.
-- ITIRSuiteNormalizedCompilerParityExact owns the suite-level source /
-- provenance / canonical identity / observation / review / promotion stages.
-- This adapter binds them without creating a second canonical reducer.
------------------------------------------------------------------------

record ITIRRecordingArtifact : Set₁ where
  constructor itirRecordingArtifact
  field
    recordingCarrier : Recording.RecordingCarrier
    normalizedArtifact : ITIR.NormalizedArtifact
    sourceCarrierIsSourceOrProvenance :
      (ITIR.concept normalizedArtifact ≡ ITIR.sourceArtifact)
      ⊎
      (ITIR.concept normalizedArtifact ≡ ITIR.provenanceAnchor)
    sameCarrierReceipt : Set
    adapterReference : String

open ITIRRecordingArtifact public

record ITIRRecordingCanonicalIdentity
    (left right : ITIRRecordingArtifact) : Set₁ where
  constructor itirRecordingCanonicalIdentity
  field
    sameRecording :
      Recording.SameRecordingWitness
        (recordingCarrier left)
        (recordingCarrier right)
    identityArtifact : ITIR.NormalizedArtifact
    identityIsCanonical :
      ITIR.concept identityArtifact ≡ ITIR.canonicalIdentity
    identityResolutionReceipt : Set
    identityReference : String

open ITIRRecordingCanonicalIdentity public

record ITIRRecordingObservedSignal
    (identity : ITIRRecordingCanonicalIdentity) : Set₁ where
  constructor itirRecordingObservedSignal
  field
    observationArtifact : ITIR.NormalizedArtifact
    observationIsSignal :
      ITIR.concept observationArtifact ≡ ITIR.observedSignal
    observationAnchoredToIdentityReceipt : Set
    observationReference : String

open ITIRRecordingObservedSignal public

record ITIRRecordingReviewableClaim
    (observation : ITIRRecordingObservedSignal) : Set₁ where
  constructor itirRecordingReviewableClaim
  field
    claimArtifact : ITIR.NormalizedArtifact
    claimIsReviewable : ITIR.concept claimArtifact ≡ ITIR.reviewableClaim
    observationSupportsCandidateClaimReceipt : Set
    claimReference : String

open ITIRRecordingReviewableClaim public

------------------------------------------------------------------------
-- Submission is a provenance fact about a derivative; promotion remains a
-- separate ITIR authority crossing.
------------------------------------------------------------------------

record ITIRSubmittedRecordingClaim
    (recording : ITIRRecordingArtifact) : Set₁ where
  constructor itirSubmittedRecordingClaim
  field
    submittedCarrier : Recording.RecordingCarrier
    submissionWitness :
      Recording.SubmittedRecordingWitness
        (recordingCarrier recording)
        submittedCarrier
    claimArtifact : ITIR.NormalizedArtifact
    claimIsReviewable : ITIR.concept claimArtifact ≡ ITIR.reviewableClaim
    submissionClaimReference : String

open ITIRSubmittedRecordingClaim public

record ITIRPromotedRecordingRecord
    (claim : ITIRSubmittedRecordingClaim) : Set₁ where
  constructor itirPromotedRecordingRecord
  field
    promotedArtifact : ITIR.NormalizedArtifact
    promotedIsRecord : ITIR.concept promotedArtifact ≡ ITIR.promotedRecord
    promotion : ITIR.PromotionReceipt (ITIRSubmittedRecordingClaim.claimArtifact claim) promotedArtifact
    promotedRecordReference : String

open ITIRPromotedRecordingRecord public

------------------------------------------------------------------------
-- Canonical parity boundary.
------------------------------------------------------------------------

record ITIRRecordingSensibLawParityBoundary : Set where
  constructor itirRecordingSensibLawParityBoundary
  field
    manifestRowMayBypassCanonicalIdentity : Bool
    manifestRowMayBypassCanonicalIdentityIsFalse :
      manifestRowMayBypassCanonicalIdentity ≡ false

    sameRecordingWitnessMayBeReplacedBySurfaceMatch : Bool
    sameRecordingWitnessMayBeReplacedBySurfaceMatchIsFalse :
      sameRecordingWitnessMayBeReplacedBySurfaceMatch ≡ false

    submissionWitnessAutomaticallyPromotesRecord : Bool
    submissionWitnessAutomaticallyPromotesRecordIsFalse :
      submissionWitnessAutomaticallyPromotesRecord ≡ false

    sensibLawMayReplaceITIRCanonicalReducer : Bool
    sensibLawMayReplaceITIRCanonicalReducerIsFalse :
      sensibLawMayReplaceITIRCanonicalReducer ≡ false

    normalizedITIRStagesRequired : Bool
    normalizedITIRStagesRequiredIsTrue : normalizedITIRStagesRequired ≡ true

canonicalITIRRecordingSensibLawParityBoundary :
  ITIRRecordingSensibLawParityBoundary
canonicalITIRRecordingSensibLawParityBoundary =
  itirRecordingSensibLawParityBoundary
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ManifestRowBypassesCanonicalIdentity : Set where
data SurfaceMatchReplacesSameRecordingWitness : Set where
data SubmissionAutomaticallyPromotes : Set where
data SensibLawReplacesITIRCanonicalReducer : Set where

manifestRowCannotBypassCanonicalIdentity :
  ManifestRowBypassesCanonicalIdentity → ⊥
manifestRowCannotBypassCanonicalIdentity ()

surfaceMatchCannotReplaceSameRecordingWitness :
  SurfaceMatchReplacesSameRecordingWitness → ⊥
surfaceMatchCannotReplaceSameRecordingWitness ()

submissionDoesNotAutoPromote : SubmissionAutomaticallyPromotes → ⊥
submissionDoesNotAutoPromote ()

sensibLawDoesNotReplaceITIRCanonicalReducer :
  SensibLawReplacesITIRCanonicalReducer → ⊥
sensibLawDoesNotReplaceITIRCanonicalReducer ()
