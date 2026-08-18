module DASHI.Governance.ArgumentLevelAuthorityRoutingExact where

------------------------------------------------------------------------
-- ARGUMENT-LEVEL AUTHORITY ROUTING
--
-- A routing obligation can fail to be adjudicable at the current inspection
-- level without becoming false and without erasing the underlying argument.
-- The same obligation/provenance can be transported to a richer authority
-- review level and become locally decidable there.
--
-- This module intentionally does not infer live authority from a support
-- square.  It demonstrates the structural difference between:
--
--   evidence polarity
--   applicability at this level
--   required-axis completion
--   route admissibility.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Core.LevelIndexedProofObligationHyperformalismExact as Levelled
import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Governance.JusticeRequiredAxisEvidenceExact as JusticeEvidence

------------------------------------------------------------------------
-- A concrete authority-verification fibre.
------------------------------------------------------------------------

data AuthorityClaim : Set where
  currentAuthorityClaim : AuthorityClaim

data AuthorityInspectionLevel : Set where
  incidentSurfaceLevel : AuthorityInspectionLevel
  mandateReviewLevel : AuthorityInspectionLevel

data AuthorityProvenance : Set where
  retainedAuthorityRecord : AuthorityProvenance

intakeCurrentAuthorityStalk :
  Levelled.ObligationStalk
    AuthorityClaim
    JusticeEvidence.RoutingEvidenceAxis
    AuthorityInspectionLevel
    AuthorityProvenance
intakeCurrentAuthorityStalk =
  Levelled.obligationStalk
    (Levelled.obligationCoordinate
      currentAuthorityClaim
      JusticeEvidence.currentAuthorityAxis
      incidentSurfaceLevel
      retainedAuthorityRecord)
    (Support.supportSquare true false)
    Transport.outsideCurrentComparisonScope

reviewCurrentAuthorityStalk :
  Levelled.ObligationStalk
    AuthorityClaim
    JusticeEvidence.RoutingEvidenceAxis
    AuthorityInspectionLevel
    AuthorityProvenance
reviewCurrentAuthorityStalk =
  Levelled.obligationStalk
    (Levelled.obligationCoordinate
      currentAuthorityClaim
      JusticeEvidence.currentAuthorityAxis
      mandateReviewLevel
      retainedAuthorityRecord)
    (Support.supportSquare true false)
    Transport.applicableHere

sameAuthorityEvidenceAcrossLevelShift :
  Levelled.evidence intakeCurrentAuthorityStalk
  ≡ Levelled.evidence reviewCurrentAuthorityStalk
sameAuthorityEvidenceAcrossLevelShift = refl

authorityReviewTransport :
  Levelled.ObligationLevelTransport
    intakeCurrentAuthorityStalk
    reviewCurrentAuthorityStalk
authorityReviewTransport =
  Levelled.obligationLevelTransport refl refl refl

authorityReviewKeepsClaim :
  Levelled.claim (Levelled.coordinate intakeCurrentAuthorityStalk)
  ≡ Levelled.claim (Levelled.coordinate reviewCurrentAuthorityStalk)
authorityReviewKeepsClaim =
  Levelled.claimPreserved authorityReviewTransport

authorityReviewKeepsProvenance :
  Levelled.provenance (Levelled.coordinate intakeCurrentAuthorityStalk)
  ≡ Levelled.provenance (Levelled.coordinate reviewCurrentAuthorityStalk)
authorityReviewKeepsProvenance =
  Levelled.provenancePreserved authorityReviewTransport

------------------------------------------------------------------------
-- Positive evidence cannot self-promote through an applicability boundary.
------------------------------------------------------------------------

intakeCannotBeResolvedPositiveHere :
  Levelled.ResolvedPositiveHere intakeCurrentAuthorityStalk → ⊥
intakeCannotBeResolvedPositiveHere resolved with proj₁ resolved
... | ()

reviewCanBeResolvedPositiveHere :
  Levelled.ResolvedPositiveHere reviewCurrentAuthorityStalk
reviewCanBeResolvedPositiveHere =
  refl , (refl , refl)

sameEvidenceDoesNotMeanSameLocalRoutingStatus :
  Levelled.applicability intakeCurrentAuthorityStalk
  ≡ Levelled.applicability reviewCurrentAuthorityStalk → ⊥
sameEvidenceDoesNotMeanSameLocalRoutingStatus ()

------------------------------------------------------------------------
-- Compare with the existing former-supporter witness: missing current-
-- authority evidence is yet another case and is not identified with the
-- out-of-scope case above.
------------------------------------------------------------------------

formerSupporterCurrentAuthorityEvidenceIsMissing :
  Support.MissingEvidence
    (JusticeEvidence.routeEvidenceAt
      JusticeEvidence.formerSupporterEvidenceProfile
      JusticeEvidence.currentAuthorityAxis)
formerSupporterCurrentAuthorityEvidenceIsMissing =
  JusticeEvidence.formerSupporterMissingCurrentAuthorityEvidence
    .Support.MissingRequiredAxis.missingAxisEvidence

-- Same high-level routing question, structurally different obstruction:
--   * former supporter: evidence missing;
--   * intake witness: positive evidence exists but this level is not licensed
--     to adjudicate the question.
-- Neither case may be collapsed into the other.

data AuthorityRoutingObstructionKind : Set where
  missingRequiredAuthorityEvidence : AuthorityRoutingObstructionKind
  authorityQuestionOutsideCurrentLevel : AuthorityRoutingObstructionKind

missingAndOutOfScopeAreDifferent :
  missingRequiredAuthorityEvidence ≡ authorityQuestionOutsideCurrentLevel → ⊥
missingAndOutOfScopeAreDifferent ()

record ArgumentLevelAuthorityRoutingBoundary : Set where
  constructor argumentLevelAuthorityRoutingBoundary
  field
    positiveEvidenceImpliesCurrentLevelApplicability : Bool
    outOfScopeMeansAuthorityClaimFalse : Bool
    missingEvidenceEqualsOutOfScope : Bool
    rechartMayRetainClaimAndProvenance : Bool
    currentLevelDecisionMayChangeAfterAdmittedRechart : Bool

canonicalArgumentLevelAuthorityRoutingBoundary :
  ArgumentLevelAuthorityRoutingBoundary
canonicalArgumentLevelAuthorityRoutingBoundary =
  argumentLevelAuthorityRoutingBoundary false false false true true
