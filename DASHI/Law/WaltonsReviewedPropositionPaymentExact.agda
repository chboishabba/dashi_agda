module DASHI.Law.WaltonsReviewedPropositionPaymentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRReviewedEvidencePaymentExact as ReviewedPayment
import DASHI.Law.SensibLawRuntimeWrongTypeElementFrontierExact as WrongType
import DASHI.Law.WaltonsEstoppelMaterialisationExact as Waltons
import DASHI.Law.SensibLawOALCJudgmentCitationSnowballExact as OALCJudgment

------------------------------------------------------------------------
-- WALTONS REVIEWED PROPOSITION-EVIDENCE PAYMENT
--
-- The runtime review gate binds an explicit reviewer decision to one exact
-- OALC source revision, canonical-text digest and paragraph locator.  A
-- successful review may pay the consumer's *evidence-coordinate obligation*.
--
-- This is intentionally weaker than proposition truth, applicability, typed
-- WrongType payment, violation, liability or remedy.
------------------------------------------------------------------------

data EstoppelRequirementRole : Set where
  assumptionOrExpectation : EstoppelRequirementRole
  reliance : EstoppelRequirementRole
  detriment : EstoppelRequirementRole
  unconscionability : EstoppelRequirementRole

data PropositionEvidenceDisposition : Set where
  supports : PropositionEvidenceDisposition
  contests : PropositionEvidenceDisposition
  contextOnly : PropositionEvidenceDisposition

record ReviewedWaltonsParagraphDecision : Set where
  constructor reviewedWaltonsParagraphDecision
  field
    paragraphLocatorReference : String
    sourceRevisionReference : String
    canonicalTextDigestReference : String
    role : EstoppelRequirementRole
    disposition : PropositionEvidenceDisposition
    reviewerReference : String
    reviewerEvidenceReferences : List String

open ReviewedWaltonsParagraphDecision public

record ReviewedWaltonsPropositionEvidenceReceipt : Set₁ where
  constructor reviewedWaltonsPropositionEvidenceReceipt
  field
    decision : ReviewedWaltonsParagraphDecision
    paragraphCandidate : OALCJudgment.OalcParagraphCandidate
    exactParagraphOwnershipReceipt : Set
    exactSourceRevisionReceipt : Set
    exactCanonicalTextDigestReceipt : Set
    matchedResearchRequirementReceipt : Set
    reviewedEvidencePaymentReceipt : Set

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse :
      createsLegalAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open ReviewedWaltonsPropositionEvidenceReceipt public

------------------------------------------------------------------------
-- Existing generic payment and WrongType frontiers remain the owners.
------------------------------------------------------------------------

ReviewedEvidencePaymentBoundary : Set
ReviewedEvidencePaymentBoundary =
  ReviewedPayment.ReviewedEvidencePaymentParity

reviewedEvidencePaymentBoundaryPaid : ReviewedEvidencePaymentBoundary
reviewedEvidencePaymentBoundaryPaid =
  ReviewedPayment.canonicalReviewedEvidencePaymentParity

WrongTypeElementBoundary : Set
WrongTypeElementBoundary =
  WrongType.RuntimeWrongTypeElementBoundary

wrongTypeElementBoundaryPaid : WrongTypeElementBoundary
wrongTypeElementBoundaryPaid =
  WrongType.canonicalRuntimeWrongTypeElementBoundary

WaltonsMaterialisationBoundary : Set
WaltonsMaterialisationBoundary =
  Waltons.WaltonsEstoppelBoundary

waltonsMaterialisationBoundaryPaid : WaltonsMaterialisationBoundary
waltonsMaterialisationBoundaryPaid =
  Waltons.canonicalWaltonsEstoppelBoundary

------------------------------------------------------------------------
-- Review/payment progression.
------------------------------------------------------------------------

data EstoppelEvidenceCoordinateState : Set where
  evidenceCoordinateOpen : EstoppelEvidenceCoordinateState
  evidenceCoordinateReviewedPaid : EstoppelEvidenceCoordinateState
  evidenceCoordinateContested : EstoppelEvidenceCoordinateState

reviewedDispositionState :
  PropositionEvidenceDisposition → EstoppelEvidenceCoordinateState
reviewedDispositionState supports = evidenceCoordinateReviewedPaid
reviewedDispositionState contests = evidenceCoordinateContested
reviewedDispositionState contextOnly = evidenceCoordinateOpen

supportsPaysEvidenceCoordinate :
  reviewedDispositionState supports ≡ evidenceCoordinateReviewedPaid
supportsPaysEvidenceCoordinate = refl

contestedEvidenceStaysContested :
  reviewedDispositionState contests ≡ evidenceCoordinateContested
contestedEvidenceStaysContested = refl

contextOnlyDoesNotPayEvidenceCoordinate :
  reviewedDispositionState contextOnly ≡ evidenceCoordinateOpen
contextOnlyDoesNotPayEvidenceCoordinate = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReviewedParagraphAutomaticallyPropositionTruth : Set where
data EvidenceCoordinatePaymentAutomaticallyWrongTypeElementPayment : Set where
data EvidenceCoordinatePaymentAutomaticallyApplicability : Set where
data EvidenceCoordinatePaymentAutomaticallyViolation : Set where
data EvidenceCoordinatePaymentAutomaticallyLiability : Set where
data SupportsDispositionAutomaticallyBindingAuthority : Set where
data MatchedResearchRequirementAutomaticallyReviewDecision : Set where
data ReviewerDecisionMayChangeSourceRevision : Set where
data ReviewerDecisionMayChangeCanonicalDigest : Set where

reviewedParagraphDoesNotCreatePropositionTruth :
  ReviewedParagraphAutomaticallyPropositionTruth → ⊥
reviewedParagraphDoesNotCreatePropositionTruth ()

evidencePaymentDoesNotCreateTypedElementPayment :
  EvidenceCoordinatePaymentAutomaticallyWrongTypeElementPayment → ⊥
evidencePaymentDoesNotCreateTypedElementPayment ()

evidencePaymentDoesNotCreateApplicability :
  EvidenceCoordinatePaymentAutomaticallyApplicability → ⊥
evidencePaymentDoesNotCreateApplicability ()

evidencePaymentDoesNotCreateViolation :
  EvidenceCoordinatePaymentAutomaticallyViolation → ⊥
evidencePaymentDoesNotCreateViolation ()

evidencePaymentDoesNotCreateLiability :
  EvidenceCoordinatePaymentAutomaticallyLiability → ⊥
evidencePaymentDoesNotCreateLiability ()

supportDoesNotCreateBindingAuthority :
  SupportsDispositionAutomaticallyBindingAuthority → ⊥
supportDoesNotCreateBindingAuthority ()

researchMatchDoesNotCreateReviewDecision :
  MatchedResearchRequirementAutomaticallyReviewDecision → ⊥
researchMatchDoesNotCreateReviewDecision ()

reviewCannotRewriteSourceRevision :
  ReviewerDecisionMayChangeSourceRevision → ⊥
reviewCannotRewriteSourceRevision ()

reviewCannotRewriteCanonicalDigest :
  ReviewerDecisionMayChangeCanonicalDigest → ⊥
reviewCannotRewriteCanonicalDigest ()

record WaltonsReviewedPropositionPaymentBoundary : Set where
  constructor waltonsReviewedPropositionPaymentBoundary
  field
    reviewBindsExactParagraph : Bool
    reviewBindsExactParagraphIsTrue :
      reviewBindsExactParagraph ≡ true

    reviewBindsExactSourceRevision : Bool
    reviewBindsExactSourceRevisionIsTrue :
      reviewBindsExactSourceRevision ≡ true

    reviewBindsExactCanonicalDigest : Bool
    reviewBindsExactCanonicalDigestIsTrue :
      reviewBindsExactCanonicalDigest ≡ true

    reviewedSupportMayPayEvidenceCoordinate : Bool
    reviewedSupportMayPayEvidenceCoordinateIsTrue :
      reviewedSupportMayPayEvidenceCoordinate ≡ true

    evidenceCoordinatePaymentCreatesClaimTruth : Bool
    evidenceCoordinatePaymentCreatesClaimTruthIsFalse :
      evidenceCoordinatePaymentCreatesClaimTruth ≡ false

    evidenceCoordinatePaymentCreatesTypedElementPayment : Bool
    evidenceCoordinatePaymentCreatesTypedElementPaymentIsFalse :
      evidenceCoordinatePaymentCreatesTypedElementPayment ≡ false

    evidenceCoordinatePaymentCreatesLiability : Bool
    evidenceCoordinatePaymentCreatesLiabilityIsFalse :
      evidenceCoordinatePaymentCreatesLiability ≡ false

    contextOnlyContractsEvidenceFrontier : Bool
    contextOnlyContractsEvidenceFrontierIsFalse :
      contextOnlyContractsEvidenceFrontier ≡ false

canonicalWaltonsReviewedPropositionPaymentBoundary :
  WaltonsReviewedPropositionPaymentBoundary
canonicalWaltonsReviewedPropositionPaymentBoundary =
  waltonsReviewedPropositionPaymentBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
