module DASHI.Culture.BoundaryConservativeTransfigurationBlochfieldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as SnowballOSINT
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- Thin repo-native specialisation.
--
-- protected stasis != traceable transfiguration
-- boundary absent later != boundary lawfully resolved along a witnessed path
------------------------------------------------------------------------

blochfieldXSource : Attribution.AttributedSource
blochfieldXSource =
  Attribution.mkNoDOISource
    "@msiyasmsi (display-name / legal identity unresolved in this owner)"
    "When someone thinks Blochfield is just a topologically protected obstructionist"
    "X/Twitter status 2090447851625050481; supplied meme image"
    "2026"
    "https://x.com/msiyasmsi/status/2090447851625050481"
    (Attribution.namedSourceKind "public social-media post / creator terminology")
    "Conceptual-source attribution only; no mathematical, physical, epistemic or domain authority imported."
    Attribution.publicAttribution

blochfieldSourceRoleReceipt :
  SnowballAttribution.SourceRoleSnowballReceipt blochfieldXSource
blochfieldSourceRoleReceipt =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt blochfieldXSource

------------------------------------------------------------------------
-- Existing OSINT carrier owns the acquisition semantics.
------------------------------------------------------------------------

blochfieldAccountObservation : SnowballOSINT.OSINTObservation
blochfieldAccountObservation =
  SnowballOSINT.osint-observation
    "https://x.com/msiyasmsi"
    "https://w.twstalker.com/msiyasmsi"
    "2026-09-11 third-party profile mirror snapshot"
    SnowballOSINT.tertiaryAggregation
    SnowballOSINT.identityUnresolved
    "dynamic X/Twitter account-count snapshot for @msiyasmsi"
    "source-bound discovery metadata; counts do not establish identity, authority, truth or same-object theory lineage"
    "no native-content digest acquired"
    false
    true
    true

record SocialAccountSnapshot : Set where
  constructor social-account-snapshot
  field
    observation : SnowballOSINT.OSINTObservation
    snapshotDate : String
    postsReported : String
    followersReported : String
    followingReported : String
    likesReported : String
    dynamicCounts : Bool
    dynamicCountsIsTrue : dynamicCounts ≡ true
    countsCreateAuthority : Bool
    countsCreateAuthorityIsFalse : countsCreateAuthority ≡ false
    countsCreateTruth : Bool
    countsCreateTruthIsFalse : countsCreateTruth ≡ false

blochfieldAccountSnapshot20260911 : SocialAccountSnapshot
blochfieldAccountSnapshot20260911 =
  social-account-snapshot
    blochfieldAccountObservation
    "2026-09-11"
    "15K"
    "417"
    "2K"
    "35K"
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Native fibre-over-time carrier.
------------------------------------------------------------------------

data BoundaryStanding : Set where
  unresolvedBoundary transformedBoundary resolvedBoundary absentBoundary reopenedBoundary : BoundaryStanding

record BoundaryObservationAt
    (system : Temporal.TemporalEvidenceSystem)
    (t : Temporal.Time system) : Set where
  constructor boundary-observation-at
  field
    standing : BoundaryStanding
    observationReference : String

open BoundaryObservationAt public

record BoundaryTransformationWitness
    (system : Temporal.TemporalEvidenceSystem)
    (before after : Temporal.Time system) : Set₁ where
  constructor boundary-transformation-witness
  field
    sourceBoundary : BoundaryObservationAt system before
    targetBoundary : BoundaryObservationAt system after
    evidencePath : Temporal.EvidencePath system before after
    ancestryReference : String
    transformationReference : String
    evidenceTraceReference : String
    ancestryRetained : Bool
    ancestryRetainedIsTrue : ancestryRetained ≡ true
    transformationLogged : Bool
    transformationLoggedIsTrue : transformationLogged ≡ true
    oldEvidenceRetained : Bool
    oldEvidenceRetainedIsTrue : oldEvidenceRetained ≡ true
    futureReopeningPermitted : Bool
    futureReopeningPermittedIsTrue : futureReopeningPermitted ≡ true

open BoundaryTransformationWitness public

record BoundaryConservativeTransfiguration
    (system : Temporal.TemporalEvidenceSystem)
    (before after : Temporal.Time system) : Set₁ where
  constructor boundary-conservative-transfiguration
  field
    witness : BoundaryTransformationWitness system before after
    sourceWasUnresolved : standing (sourceBoundary witness) ≡ unresolvedBoundary
    targetResolvedOrTransformed :
      (standing (targetBoundary witness) ≡ resolvedBoundary) ⊎
      (standing (targetBoundary witness) ≡ transformedBoundary)
    sameStateRequired : Bool
    sameStateRequiredIsFalse : sameStateRequired ≡ false
    sameBoundaryObjectRequired : Bool
    sameBoundaryObjectRequiredIsFalse : sameBoundaryObjectRequired ≡ false
    traceOfTransformationRequired : Bool
    traceOfTransformationRequiredIsTrue : traceOfTransformationRequired ≡ true

------------------------------------------------------------------------
-- Resolution has more evidence than an absent after-state.
------------------------------------------------------------------------

record BoundaryResolution
    (system : Temporal.TemporalEvidenceSystem)
    (before after : Temporal.Time system) : Set₁ where
  constructor boundary-resolution
  field
    transformation : BoundaryTransformationWitness system before after
    beforeUnresolved : standing (sourceBoundary transformation) ≡ unresolvedBoundary
    afterResolved : standing (targetBoundary transformation) ≡ resolvedBoundary

record BoundaryAbsenceAt
    (system : Temporal.TemporalEvidenceSystem)
    (t : Temporal.Time system) : Set where
  constructor boundary-absence-at
  field
    observation : BoundaryObservationAt system t
    isAbsent : standing observation ≡ absentBoundary

record ReopenableResolvedState
    (system : Temporal.TemporalEvidenceSystem)
    (t : Temporal.Time system) : Set where
  constructor reopenable-resolved-state
  field
    observation : BoundaryObservationAt system t
    isResolved : standing observation ≡ resolvedBoundary
    reopeningPermitted : Bool
    reopeningPermittedIsTrue : reopeningPermitted ≡ true
    historicalResolutionRetained : Bool
    historicalResolutionRetainedIsTrue : historicalResolutionRetained ≡ true

record BoundaryReopening
    (system : Temporal.TemporalEvidenceSystem)
    (before after : Temporal.Time system) : Set₁ where
  constructor boundary-reopening
  field
    priorResolvedState : ReopenableResolvedState system before
    reopeningPath : Temporal.EvidencePath system before after
    reopenedObservation : BoundaryObservationAt system after
    isReopened : standing reopenedObservation ≡ reopenedBoundary
    oldPathStillRetained : Bool
    oldPathStillRetainedIsTrue : oldPathStillRetained ≡ true

appendOnlyRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
appendOnlyRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

------------------------------------------------------------------------
-- Snowball cut. Acquisition may be out of order; payment may not skip debt.
------------------------------------------------------------------------

data BlochfieldSnowballLeaf : Set where
  publicationEventIdentity suppliedImageIdentity nativeXBodyIdentity
    creatorLongFormIdentity externalSameObjectTheoryLineage technicalClaimPayment : BlochfieldSnowballLeaf

data LeafStanding : Set where paid unpaid : LeafStanding

blochfieldSnowballStanding : BlochfieldSnowballLeaf → LeafStanding
blochfieldSnowballStanding publicationEventIdentity = paid
blochfieldSnowballStanding suppliedImageIdentity = paid
blochfieldSnowballStanding nativeXBodyIdentity = unpaid
blochfieldSnowballStanding creatorLongFormIdentity = unpaid
blochfieldSnowballStanding externalSameObjectTheoryLineage = unpaid
blochfieldSnowballStanding technicalClaimPayment = unpaid

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data BoundaryAbsenceCreatesResolution : Set where
data ProtectedStasisEqualsTraceableTransfiguration : Set where
data MissingTransitionLogStillConservesTransformation : Set where
data SocialCountCreatesAuthority : Set where
data SocialCountCreatesTruth : Set where
data MemeTerminologyCreatesEstablishedPhysics : Set where
data LaterEvidencePaysEarlierUnpaidIdentity : Set where
data MirrorEqualsNativeXCarrier : Set where

boundaryAbsenceDoesNotCreateResolution : BoundaryAbsenceCreatesResolution → ⊥
boundaryAbsenceDoesNotCreateResolution ()

protectedStasisDoesNotEqualTraceableTransfiguration :
  ProtectedStasisEqualsTraceableTransfiguration → ⊥
protectedStasisDoesNotEqualTraceableTransfiguration ()

missingTransitionLogDoesNotConserveTransformation :
  MissingTransitionLogStillConservesTransformation → ⊥
missingTransitionLogDoesNotConserveTransformation ()

socialCountDoesNotCreateAuthority : SocialCountCreatesAuthority → ⊥
socialCountDoesNotCreateAuthority ()

socialCountDoesNotCreateTruth : SocialCountCreatesTruth → ⊥
socialCountDoesNotCreateTruth ()

memeTerminologyDoesNotCreateEstablishedPhysics :
  MemeTerminologyCreatesEstablishedPhysics → ⊥
memeTerminologyDoesNotCreateEstablishedPhysics ()

laterEvidenceDoesNotSkipUnpaidIdentity :
  LaterEvidencePaysEarlierUnpaidIdentity → ⊥
laterEvidenceDoesNotSkipUnpaidIdentity ()

mirrorDoesNotEqualNativeXCarrier : MirrorEqualsNativeXCarrier → ⊥
mirrorDoesNotEqualNativeXCarrier ()

record BlochfieldBoundary : Set where
  constructor blochfield-boundary
  field
    boundaryMayChangeLawfully : Bool
    boundaryMayChangeLawfullyIsTrue : boundaryMayChangeLawfully ≡ true
    lawfulResolutionRequiresTrace : Bool
    lawfulResolutionRequiresTraceIsTrue : lawfulResolutionRequiresTrace ≡ true
    historyMayBeDiscardedAfterResolution : Bool
    historyMayBeDiscardedAfterResolutionIsFalse : historyMayBeDiscardedAfterResolution ≡ false
    resolvedStateMayBeReopened : Bool
    resolvedStateMayBeReopenedIsTrue : resolvedStateMayBeReopened ≡ true
    protectedStasisEqualsConservation : Bool
    protectedStasisEqualsConservationIsFalse : protectedStasisEqualsConservation ≡ false
    blochfieldIsPromotedToEstablishedPhysics : Bool
    blochfieldIsPromotedToEstablishedPhysicsIsFalse : blochfieldIsPromotedToEstablishedPhysics ≡ false
    accountCountsAffectClaimValidity : Bool
    accountCountsAffectClaimValidityIsFalse : accountCountsAffectClaimValidity ≡ false

canonicalBlochfieldBoundary : BlochfieldBoundary
canonicalBlochfieldBoundary =
  blochfield-boundary true refl true refl false refl true refl false refl false refl false refl
