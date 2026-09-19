module DASHI.Interop.SLRSharedEvidenceReducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSprint2CanonicalEvidenceConvergenceExact as Sprint2
import DASHI.Interop.SLRReviewedEvidencePaymentExact as Reviewed

------------------------------------------------------------------------
-- SPRINT 2 M2.3 — SHARED REVIEWED-EVIDENCE REDUCER
--
-- Runtime target:
--   chboishabba/slr :: crates/sl-reviewed-evidence-payment/shared_reducer.rs
--
-- One reviewed canonical evidence object fans out to world, matter and legal
-- projection slots. A slot may produce a delta or abstain. The reducer does
-- not manufacture authority, applicability or claim truth.
------------------------------------------------------------------------

data ProjectionFamily : Set where
  world : ProjectionFamily
  matter : ProjectionFamily
  legal : ProjectionFamily

data ProjectionDisposition : Set where
  produced : ProjectionDisposition
  abstained : ProjectionDisposition

record ReviewedCanonicalEvidenceParity : Set where
  constructor reviewedCanonicalEvidenceParity
  field
    canonicalObservationContained : Bool
    reviewReferenceExplicit : Bool
    paymentReferenceExplicit : Bool
    consumerReferenceExplicit : Bool
    requirementReferenceExplicit : Bool
    reviewEvidenceReferenceMustEqualObservationReference : Bool
    canonicalObservationValidationRequired : Bool
    reviewedEvidenceCreatesSemanticAuthority : Bool
    reviewedEvidencePromotesApplicability : Bool
    reviewedEvidencePromotesClaimTruth : Bool

open ReviewedCanonicalEvidenceParity public

canonicalReviewedEvidenceParity : ReviewedCanonicalEvidenceParity
canonicalReviewedEvidenceParity =
  reviewedCanonicalEvidenceParity
    true true true true true true true
    false false false

record SharedEvidenceReducerParity : Set where
  constructor sharedEvidenceReducerParity
  field
    worldConsumesReviewedCanonicalEvidence : Bool
    matterConsumesReviewedCanonicalEvidence : Bool
    legalConsumesReviewedCanonicalEvidence : Bool
    projectionMayAbstain : Bool
    absentProjectionSlotMayRemainAbsent : Bool
    projectionFamilyMustMatchReducerSlot : Bool
    projectionReceiptRetainsReviewedEvidenceReference : Bool
    projectionReceiptRetainsObservationReference : Bool
    projectionReceiptRetainsSourceRevisionReference : Bool
    projectionReceiptRetainsSpanReference : Bool
    projectionReceiptRetainsReviewReference : Bool
    projectionReceiptRetainsPaymentReference : Bool
    reducerCreatesSemanticAuthority : Bool
    reducerPromotesApplicability : Bool
    reducerPromotesClaimTruth : Bool

open SharedEvidenceReducerParity public

canonicalSharedEvidenceReducerParity : SharedEvidenceReducerParity
canonicalSharedEvidenceReducerParity =
  sharedEvidenceReducerParity
    true true true
    true true true
    true true true true true true
    false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProjectionSpecificEvidenceBypassesSharedReducer : Set where
data SharedReducerCreatesSemanticAuthority : Set where
data SharedReducerPromotesApplicability : Set where
data SharedReducerPromotesClaimTruth : Set where
data ProjectionMayReplaceSourceRevision : Set where
data ProjectionMayReplaceEvidenceSpan : Set where
data ReviewedEvidenceMeansClaimTruth : Set where
data AbstentionRequiresFabricatedDelta : Set where

projectionSpecificEvidenceCannotBypassSharedReducer :
  ProjectionSpecificEvidenceBypassesSharedReducer → ⊥
projectionSpecificEvidenceCannotBypassSharedReducer ()

sharedReducerCannotCreateSemanticAuthority :
  SharedReducerCreatesSemanticAuthority → ⊥
sharedReducerCannotCreateSemanticAuthority ()

sharedReducerCannotPromoteApplicability :
  SharedReducerPromotesApplicability → ⊥
sharedReducerCannotPromoteApplicability ()

sharedReducerCannotPromoteClaimTruth :
  SharedReducerPromotesClaimTruth → ⊥
sharedReducerCannotPromoteClaimTruth ()

projectionCannotReplaceSourceRevision :
  ProjectionMayReplaceSourceRevision → ⊥
projectionCannotReplaceSourceRevision ()

projectionCannotReplaceEvidenceSpan :
  ProjectionMayReplaceEvidenceSpan → ⊥
projectionCannotReplaceEvidenceSpan ()

reviewedEvidenceDoesNotMeanClaimTruth :
  ReviewedEvidenceMeansClaimTruth → ⊥
reviewedEvidenceDoesNotMeanClaimTruth ()

abstentionDoesNotRequireFabricatedDelta :
  AbstentionRequiresFabricatedDelta → ⊥
abstentionDoesNotRequireFabricatedDelta ()

reviewBoundaryAnchor : Reviewed.ReviewedEvidencePaymentParity
reviewBoundaryAnchor = Reviewed.canonicalReviewedEvidencePaymentParity

sprint2ManifestationAnchor : Sprint2.CanonicalManifestationEnvelopeParity
sprint2ManifestationAnchor = Sprint2.canonicalManifestationEnvelope
