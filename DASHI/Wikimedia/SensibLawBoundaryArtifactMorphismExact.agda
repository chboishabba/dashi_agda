module DASHI.Wikimedia.SensibLawBoundaryArtifactMorphismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as Handoff

------------------------------------------------------------------------
-- FORMAL RETURN OF THE SENSIBLAW BOUNDARY-ARTIFACT / MORPHISM CONTRACT
--
-- Source donor:
--   SensibLaw/docs/planning/boundary_artifact_morphism_contract_20260328.md
--
-- This is the reusable interface requested for SLR: raw/source-format input is
-- normalized into typed provenance-bearing artifacts, and stronger commitments
-- require governed morphisms rather than bypassing the boundary layer.
------------------------------------------------------------------------

data ArtifactKind : Set where
  externalSourceArtifact
  sourceUnitArtifact
  observationClaimArtifact
  migrationCandidateArtifact
  splitPlanArtifact
  reviewPacketArtifact
  canonicalPromotedArtifact
  : ArtifactKind

data MorphismDeterminism : Set where
  deterministicMorphism heuristicMorphism mixedMorphism : MorphismDeterminism

data MorphismTotality : Set where
  totalMorphism partialMorphism abstainingMorphism : MorphismTotality

data AuthorityLevel : Set where
  signalAuthority candidateAuthority reviewedAuthority promotedAuthority : AuthorityLevel

data Lossiness : Set where
  lossless lossy unknownLossiness : Lossiness

data ReviewRequirement : Set where
  noReview reviewRequired verificationRequired : ReviewRequirement

record GovernedMorphism : Set where
  constructor governed-morphism
  field
    morphismId : String
    inputKind : ArtifactKind
    outputKind : ArtifactKind
    determinism : MorphismDeterminism
    totality : MorphismTotality
    inputAuthority : AuthorityLevel
    outputAuthority : AuthorityLevel
    reviewRequirement : ReviewRequirement
    preservesProvenance : Bool
    preservesProvenanceIsTrue : preservesProvenance ≡ true
    lossiness : Lossiness
    semanticsReference : String
    governanceReference : String
open GovernedMorphism public

captureSourceUnit : GovernedMorphism
captureSourceUnit =
  governed-morphism
    "capture-source-unit"
    externalSourceArtifact sourceUnitArtifact
    deterministicMorphism partialMorphism
    signalAuthority candidateAuthority
    noReview
    true refl
    lossless
    "normalize revision-locked input into sl.source_unit.v1-compatible carrier"
    "raw source does not bypass the typed boundary-artifact layer"

extractObservation : GovernedMorphism
extractObservation =
  governed-morphism
    "extract-observation"
    sourceUnitArtifact observationClaimArtifact
    mixedMorphism abstainingMorphism
    candidateAuthority candidateAuthority
    reviewRequired
    true refl
    lossy
    "extract anchored candidate observations without promoting truth"
    "anchors and provenance remain attached; ambiguity may abstain"

reviewSplitPlan : GovernedMorphism
reviewSplitPlan =
  governed-morphism
    "review-split-plan"
    splitPlanArtifact reviewPacketArtifact
    mixedMorphism abstainingMorphism
    candidateAuthority reviewedAuthority
    reviewRequired
    true refl
    lossy
    "assemble reviewer-facing bounded packet around an existing split baseline"
    "review packet reduces uncertainty but does not execute or transfer authority"

promoteReviewedCandidate : GovernedMorphism
promoteReviewedCandidate =
  governed-morphism
    "promote-reviewed-candidate"
    migrationCandidateArtifact canonicalPromotedArtifact
    deterministicMorphism partialMorphism
    reviewedAuthority promotedAuthority
    verificationRequired
    true refl
    lossless
    "promotion is a separately verified morphism"
    "checked-safe/authority/admissibility receipts required downstream"

------------------------------------------------------------------------
-- ObservationClaim payload: reusable source-unit output ABI for SLR.
------------------------------------------------------------------------

data CandidatePolarity : Set where
  positiveCandidate negativeCandidate unresolvedPolarity : CandidatePolarity

record ObservationClaimPayload : Set where
  constructor observation-claim-payload
  field
    observationId : String
    sourceUnit : Handoff.SensibLawSourceUnit
    anchorReferences : List String
    subjectQidCandidate : Id.ItemId
    predicateReference : String
    objectReference : String
    qualifierReferences : List String
    sourceReferenceProperties : List Id.PropertyId
    polarity : CandidatePolarity
    confidenceReference : String
    extractionReference : String
open ObservationClaimPayload public

record ObservationExtractionReceipt : Set where
  constructor observation-extraction-receipt
  field
    payload : ObservationClaimPayload
    morphism : GovernedMorphism
    morphismIsExtract : morphism ≡ extractObservation
    sourceIdentityPreserved : Bool
    sourceIdentityPreservedIsTrue : sourceIdentityPreserved ≡ true
    anchorsPreserved : Bool
    anchorsPreservedIsTrue : anchorsPreserved ≡ true
    createsWorldTruth : Bool
    createsWorldTruthIsFalse : createsWorldTruth ≡ false
    receiptReference : String
open ObservationExtractionReceipt public

------------------------------------------------------------------------
-- Composition firewalls.
------------------------------------------------------------------------

data RawSourcePromotesDirectly : Set where
data SplitPlanExecutesWithoutVerification : Set where
data ObservationClaimIsCanonicalTruth : Set where
data LossyMorphismMayDropProvenance : Set where

rawSourceCannotPromoteDirectly : RawSourcePromotesDirectly → ⊥
rawSourceCannotPromoteDirectly ()

splitPlanCannotExecuteWithoutVerification : SplitPlanExecutesWithoutVerification → ⊥
splitPlanCannotExecuteWithoutVerification ()

observationClaimDoesNotBecomeCanonicalTruth : ObservationClaimIsCanonicalTruth → ⊥
observationClaimDoesNotBecomeCanonicalTruth ()

lossinessDoesNotPermitProvenanceDrop : LossyMorphismMayDropProvenance → ⊥
lossinessDoesNotPermitProvenanceDrop ()

record BoundaryMorphismBoundary : Set where
  constructor boundary-morphism-boundary
  field
    rawSourceMustNormalizeFirst : Bool
    extractionMayAbstain : Bool
    extractionCreatesTruth : Bool
    reviewPacketExecutesMigration : Bool
    promotionRequiresSeparateVerification : Bool
    allMorphismsPreserveProvenance : Bool

canonicalBoundaryMorphismBoundary : BoundaryMorphismBoundary
canonicalBoundaryMorphismBoundary =
  boundary-morphism-boundary true true false false true true
