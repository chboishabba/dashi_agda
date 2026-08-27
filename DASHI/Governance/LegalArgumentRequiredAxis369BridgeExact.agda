module DASHI.Governance.LegalArgumentRequiredAxis369BridgeExact where

------------------------------------------------------------------------
-- LEGAL ARGUMENT / REQUIRED-AXIS / 369 AUTHORITY ROUTING BRIDGE
--
-- This does not create a second argument calculus.  It explicitly connects the
-- legal verification-fibre specialization to the existing argument-level
-- hyperformalism used by the 369 convergence regression:
--
--   retained argument/provenance
--   -> level-indexed applicability
--   -> required-axis adequacy
--   -> authority review
--   -> situated decision.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.LevelIndexedProofObligationHyperformalismExact as Levelled
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Required
import DASHI.Governance.ArgumentHyperformalism369Regression as Argument369
import DASHI.Governance.ArgumentLevelAuthorityRoutingExact as AuthorityRouting
import DASHI.Governance.InstitutionalVerificationFibreRequiredAxisExact as Verification

------------------------------------------------------------------------
-- 1. Existing argument-level authority review already supplies the verification
--    pattern: same claim/evidence/provenance, richer admitted level.
------------------------------------------------------------------------

legalAuthorityReviewKeepsClaim :
  Levelled.claim (Levelled.coordinate AuthorityRouting.intakeCurrentAuthorityStalk)
  ≡ Levelled.claim (Levelled.coordinate AuthorityRouting.reviewCurrentAuthorityStalk)
legalAuthorityReviewKeepsClaim = Argument369.authorityLevelShiftKeepsClaim

legalAuthorityReviewKeepsProvenance :
  Levelled.provenance (Levelled.coordinate AuthorityRouting.intakeCurrentAuthorityStalk)
  ≡ Levelled.provenance (Levelled.coordinate AuthorityRouting.reviewCurrentAuthorityStalk)
legalAuthorityReviewKeepsProvenance = Argument369.authorityLevelShiftKeepsProvenance

samePositiveEvidenceCanRemainOutOfScopeAtIntake :
  Levelled.evidence AuthorityRouting.intakeCurrentAuthorityStalk
  ≡ Levelled.evidence AuthorityRouting.reviewCurrentAuthorityStalk
samePositiveEvidenceCanRemainOutOfScopeAtIntake =
  AuthorityRouting.sameAuthorityEvidenceAcrossLevelShift

intakePositiveEvidenceStillNotLocallyResolved :
  Levelled.ResolvedPositiveHere AuthorityRouting.intakeCurrentAuthorityStalk → ⊥
intakePositiveEvidenceStillNotLocallyResolved =
  AuthorityRouting.intakeCannotBeResolvedPositiveHere

reviewLevelCanResolveSamePositiveEvidence :
  Levelled.ResolvedPositiveHere AuthorityRouting.reviewCurrentAuthorityStalk
reviewLevelCanResolveSamePositiveEvidence =
  AuthorityRouting.reviewCanBeResolvedPositiveHere

------------------------------------------------------------------------
-- 2. Flat local evidence cannot reconstruct the level-aware decision.  This is
--    the existing 369/argument non-factorability theorem, now placed directly
--    beside the legal verification-fibre obstruction.
------------------------------------------------------------------------

flatArgumentEvidenceCannotRecoverLevelAwareDecision :
  NF.FactorsThrough Levelled.flattenEvidence Levelled.fineDecision → ⊥
flatArgumentEvidenceCannotRecoverLevelAwareDecision =
  Argument369.flatSupportCannotRecoverLevelAwareDecision

knownQuestionStillDoesNotCloseVerificationFibre :
  Verification.VerificationDecisionSafe Verification.questionObserver → ⊥
knownQuestionStillDoesNotCloseVerificationFibre =
  Verification.questionObserverNotDecisionSafe

flatSubjectLabelStillCannotRecoverVerificationAccess :
  NF.FactorsThrough Verification.flatSubjectObserver Verification.relationAccessAxis → ⊥
flatSubjectLabelStillCannotRecoverVerificationAccess =
  Verification.flatAdjustmentCannotRecoverRelationAccess

flatSubjectLabelCannotRetainRequiredAccessAndCommunication :
  Required.RetainsBothRequiredAxes
    Verification.flatSubjectObserver
    Verification.relationAccessAxis
    Verification.communicationAxis → ⊥
flatSubjectLabelCannotRetainRequiredAccessAndCommunication =
  Verification.flatCannotRetainBothRequiredRelationalAxes

------------------------------------------------------------------------
-- 3. The 369 carrier supplies address/refinement geometry, not permission to
--    collapse evidence, applicability, required axes or authority into one bit.
------------------------------------------------------------------------

record LegalArgumentRequiredAxis369Boundary : Set where
  constructor legalArgumentRequiredAxis369Boundary
  field
    positiveEvidenceCreatesCurrentLevelApplicability : Bool
    knowingQuestionCreatesVerificationClosure : Bool
    flatEvidenceRecoversLevelAwareDecision : Bool
    flatSubjectLabelRecoversRelationalAccess : Bool
    oneRetainedAxisCompensatesForMissingRequiredAxis : Bool
    argumentAndProvenanceMaySurviveRicherRechart : Bool
    richerAuthorityReviewMayResolveSameEvidence : Bool

canonicalLegalArgumentRequiredAxis369Boundary :
  LegalArgumentRequiredAxis369Boundary
canonicalLegalArgumentRequiredAxis369Boundary =
  legalArgumentRequiredAxis369Boundary
    false false false false false true true
