module DASHI.Cognition.PNF.SensibLawMinimalMatterHandoffExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMatterContextProjectionExact as Context

------------------------------------------------------------------------
-- M13 minimal recipient-scoped handoff.
--
-- This is intentionally smaller than M16 rich reporting.  It previews a
-- bounded subset already visible under MatterContext for one recipient,
-- preserving explicit redactions/exclusions without mutating canonical state.
------------------------------------------------------------------------

data HandoffRecipientProfile : Set where
  lawyerRecipient clinicianRecipient advocateRecipient regulatorRecipient :
    HandoffRecipientProfile
  publicOfficialRecipient researcherRecipient otherRecipient :
    HandoffRecipientProfile

record MinimalHandoffSelection : Set where
  constructor minimal-handoff-selection
  field
    handoffRef : String
    matterRef : String
    recipientRef : String
    recipientProfile : HandoffRecipientProfile
    disclosureBoundary : Context.MatterDisclosureBoundary
    selectedRefs : List String
    redactionRefs : List String
    retentionPolicyRef : String
    redactionPolicyRef : String
    textExportPolicyRef : String
    localOnly : Bool
    doNotSync : Bool

open MinimalHandoffSelection public

record MinimalHandoffPreview : Set where
  constructor minimal-handoff-preview
  field
    handoffRef : String
    matterRef : String
    recipientRef : String
    recipientProfile : HandoffRecipientProfile
    disclosureBoundary : Context.MatterDisclosureBoundary
    exportedRefs : List String
    redactedRefs : List String
    visibleExclusionRefs : List String
    retentionPolicyRef : String
    redactionPolicyRef : String
    textExportPolicyRef : String

    localOnly : Bool
    doNotSync : Bool

    canonicalWorldMutated : Bool
    canonicalWorldMutatedIsFalse : canonicalWorldMutated ≡ false

    redactionDeletesCanonicalSource : Bool
    redactionDeletesCanonicalSourceIsFalse :
      redactionDeletesCanonicalSource ≡ false

    unsharedMeansAbsentFromWorld : Bool
    unsharedMeansAbsentFromWorldIsFalse :
      unsharedMeansAbsentFromWorld ≡ false

    exportCreatesSemanticAuthority : Bool
    exportCreatesSemanticAuthorityIsFalse :
      exportCreatesSemanticAuthority ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open MinimalHandoffPreview public

canonicalMinimalHandoffPreview : MinimalHandoffPreview
canonicalMinimalHandoffPreview =
  minimal-handoff-preview
    "handoff:example"
    "matter:example"
    "recipient:lawyer"
    lawyerRecipient
    Context.recipientScoped
    []
    []
    []
    "retention:bounded"
    "redaction:explicit"
    "text-export:reviewed-only"
    true
    true
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Ordinary role-scoped handoff and protected disclosure remain distinct.
------------------------------------------------------------------------

record ProtectedDisclosureBoundary : Set where
  constructor protected-disclosure-boundary
  field
    protectedDisclosureNeedsNoSync : Bool
    protectedDisclosureNeedsNoSyncIsTrue :
      protectedDisclosureNeedsNoSync ≡ true

    protectedDisclosureEqualsOrdinaryRoleHandoff : Bool
    protectedDisclosureEqualsOrdinaryRoleHandoffIsFalse :
      protectedDisclosureEqualsOrdinaryRoleHandoff ≡ false

    identityMinimisationMayBeStronger : Bool
    identityMinimisationMayBeStrongerIsTrue :
      identityMinimisationMayBeStronger ≡ true

canonicalProtectedDisclosureBoundary : ProtectedDisclosureBoundary
canonicalProtectedDisclosureBoundary =
  protected-disclosure-boundary
    true refl
    false refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HandoffExportCreatesNewTruthStore : Set where
data HandoffSelectionMutatesCanonicalWorld : Set where
data RedactionDeletesCanonicalSource : Set where
data NotSharedMeansAbsentFromWorld : Set where
data RecipientRoleCreatesSemanticAuthority : Set where
data HiddenByContextMayStillBeExported : Set where
data ProtectedDisclosureEqualsOrdinaryHandoff : Set where
data ExportedSubsetClaimsCompleteness : Set where

handoffExportDoesNotCreateNewTruthStore :
  HandoffExportCreatesNewTruthStore → ⊥
handoffExportDoesNotCreateNewTruthStore ()

handoffSelectionDoesNotMutateCanonicalWorld :
  HandoffSelectionMutatesCanonicalWorld → ⊥
handoffSelectionDoesNotMutateCanonicalWorld ()

redactionDoesNotDeleteCanonicalSource :
  RedactionDeletesCanonicalSource → ⊥
redactionDoesNotDeleteCanonicalSource ()

notSharedDoesNotMeanAbsentFromWorld :
  NotSharedMeansAbsentFromWorld → ⊥
notSharedDoesNotMeanAbsentFromWorld ()

recipientRoleDoesNotCreateSemanticAuthority :
  RecipientRoleCreatesSemanticAuthority → ⊥
recipientRoleDoesNotCreateSemanticAuthority ()

hiddenContextCoordinateMayNotBeExported :
  HiddenByContextMayStillBeExported → ⊥
hiddenContextCoordinateMayNotBeExported ()

protectedDisclosureIsNotOrdinaryHandoff :
  ProtectedDisclosureEqualsOrdinaryHandoff → ⊥
protectedDisclosureIsNotOrdinaryHandoff ()

exportedSubsetDoesNotClaimCompleteness :
  ExportedSubsetClaimsCompleteness → ⊥
exportedSubsetDoesNotClaimCompleteness ()
