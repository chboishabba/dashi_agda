module DASHI.Interop.ImmutableEvidenceSupersessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.DistributedEvidenceHistoryProjectionExact as History

------------------------------------------------------------------------
-- IMMUTABLE EVIDENCE SUPERSESSION
--
-- Discussion-origin architecture: Johl Brown, 2026-09-17.
-- Instead of treating evidence revision as destructive mutation, retain exact
-- immutable source identities and represent change with an explicit relation.
-- The typed relation and firewalls below are DASHI synthesis.
------------------------------------------------------------------------

data RevisionRelation : Set where
  supersedes : RevisionRelation
  corrects : RevisionRelation
  supplements : RevisionRelation
  republishes : RevisionRelation
  independentParallelSource : RevisionRelation

record SourceRevisionEdge : Set where
  constructor sourceRevisionEdge
  field
    earlierSource : History.ImmutableSourceObject
    laterSource : History.ImmutableSourceObject
    relation : RevisionRelation
    edgeProvenance : String
    sameByteIdentityRequired : Bool
    sameByteIdentityRequiredIsFalse : sameByteIdentityRequired ≡ false
    earlierSourceInvalidated : Bool
    earlierSourceInvalidatedIsFalse : earlierSourceInvalidated ≡ false
    laterSourceAutomaticallyAuthoritative : Bool
    laterSourceAutomaticallyAuthoritativeIsFalse : laterSourceAutomaticallyAuthoritative ≡ false

open SourceRevisionEdge public

record RevisionedObservation : Set where
  constructor revisionedObservation
  field
    sourceRevision : History.ImmutableSourceObject
    observation : History.SignedObservation
    observationBoundToExactRevision : Bool
    observationBoundToExactRevisionIsTrue : observationBoundToExactRevision ≡ true

open RevisionedObservation public

record RevisionedDerivedView : Set where
  constructor revisionedDerivedView
  field
    revisionEdge : SourceRevisionEdge
    earlierView : History.DeterministicProjection
    laterView : History.DeterministicProjection
    viewsRemainConsumerRelative : Bool
    viewsRemainConsumerRelativeIsTrue : viewsRemainConsumerRelative ≡ true
    supersessionCreatesGlobalTruth : Bool
    supersessionCreatesGlobalTruthIsFalse : supersessionCreatesGlobalTruth ≡ false

open RevisionedDerivedView public

------------------------------------------------------------------------
-- Synthetic fixture demonstrating S0 != S1 as distinct immutable identities.
------------------------------------------------------------------------

sourceV0 : History.ImmutableSourceObject
sourceV0 =
  History.immutableSourceObject
    "source:fixture:v0"
    "sha256:fixture-v0"
    "cid:fixture-v0"
    true

sourceV1 : History.ImmutableSourceObject
sourceV1 =
  History.immutableSourceObject
    "source:fixture:v1"
    "sha256:fixture-v1"
    "cid:fixture-v1"
    true

fixtureSupersession : SourceRevisionEdge
fixtureSupersession =
  sourceRevisionEdge
    sourceV0 sourceV1 supersedes
    "synthetic DASHI supersession fixture"
    false refl
    false refl
    false refl

sourceV0IdentityPinned : History.sourceIdentity sourceV0 ≡ "source:fixture:v0"
sourceV0IdentityPinned = refl

sourceV1IdentityPinned : History.sourceIdentity sourceV1 ≡ "source:fixture:v1"
sourceV1IdentityPinned = refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data SupersessionMutatesEarlierBytes : Set where
data SupersessionInvalidatesEarlierSource : Set where
data SupersessionCreatesLaterAuthority : Set where
data NewerSourceMakesEarlierObservationFalse : Set where
data SameSourceLabelCreatesSameByteIdentity : Set where
data LaterProjectionRewritesEarlierEvidence : Set where

data ObservationCanFloatAcrossRevision : Set where

supersessionDoesNotMutateEarlierBytes : SupersessionMutatesEarlierBytes → ⊥
supersessionDoesNotMutateEarlierBytes ()

supersessionDoesNotInvalidateEarlierSource : SupersessionInvalidatesEarlierSource → ⊥
supersessionDoesNotInvalidateEarlierSource ()

supersessionDoesNotCreateLaterAuthority : SupersessionCreatesLaterAuthority → ⊥
supersessionDoesNotCreateLaterAuthority ()

newerSourceDoesNotMakeEarlierObservationFalse : NewerSourceMakesEarlierObservationFalse → ⊥
newerSourceDoesNotMakeEarlierObservationFalse ()

sameSourceLabelDoesNotCreateSameByteIdentity : SameSourceLabelCreatesSameByteIdentity → ⊥
sameSourceLabelDoesNotCreateSameByteIdentity ()

laterProjectionDoesNotRewriteEarlierEvidence : LaterProjectionRewritesEarlierEvidence → ⊥
laterProjectionDoesNotRewriteEarlierEvidence ()

observationDoesNotFloatAcrossRevision : ObservationCanFloatAcrossRevision → ⊥
observationDoesNotFloatAcrossRevision ()

------------------------------------------------------------------------
-- Positive construction: an explicit relation preserves both source identities.
------------------------------------------------------------------------

record AuditableSupersessionReceipt : Set where
  constructor auditableSupersessionReceipt
  field
    edge : SourceRevisionEdge
    earlierIdentityRetained : Bool
    earlierIdentityRetainedIsTrue : earlierIdentityRetained ≡ true
    laterIdentityRetained : Bool
    laterIdentityRetainedIsTrue : laterIdentityRetained ≡ true
    relationExplicit : Bool
    relationExplicitIsTrue : relationExplicit ≡ true
    promotesTruth : Bool
    promotesTruthIsFalse : promotesTruth ≡ false

open AuditableSupersessionReceipt public

mkAuditableSupersessionReceipt : SourceRevisionEdge → AuditableSupersessionReceipt
mkAuditableSupersessionReceipt edge =
  auditableSupersessionReceipt edge true refl true refl true refl false refl

fixtureSupersessionReceipt : AuditableSupersessionReceipt
fixtureSupersessionReceipt = mkAuditableSupersessionReceipt fixtureSupersession
