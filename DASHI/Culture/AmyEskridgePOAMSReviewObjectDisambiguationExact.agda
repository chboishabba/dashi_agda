module DASHI.Culture.AmyEskridgePOAMSReviewObjectDisambiguationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgePOAMSObjectLineageExact as Lineage
import DASHI.Culture.AmyEskridgeInstituteDerivativeIdentityDiscriminatorExact as D
import DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact as Candidate
import DASHI.Core.KnowledgeBoundaryCandidateIdentityBidiExact as Identity

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: REVIEW-OBJECT REFERENT DISAMBIGUATION
--
-- The current source surface contains two non-identical candidate readings of
-- Amy's September-2020 release dependency:
--
--   (A) the earlier NASA/QM study / release process itself;
--   (B) the later NASA/TM-20205010911 / M-1531 report that records it.
--
-- NASA's TM establishes that the 2015-2016 experimental programme and the 2021
-- report are distinct knowledge objects. Secondary reconstructions can point
-- toward either referent, but disagreement among secondary descriptions cannot
-- manufacture exact identity. This owner preserves both candidates until an
-- identity-specific primary carrier resolves the referent.
------------------------------------------------------------------------

data ReviewReferentCandidate : Set where
  earlierNASAStudyReferent : ReviewReferentCandidate
  laterNASATMReferent : ReviewReferentCandidate
  instituteDerivativeReferent : ReviewReferentCandidate

data ReferentEvidenceGrade : Set where
  primaryIdentityReceipt : ReferentEvidenceGrade
  directWitnessLead : ReferentEvidenceGrade
  secondaryReconstructionLead : ReferentEvidenceGrade
  compatibilityOnly : ReferentEvidenceGrade

record ReviewReferentLead : Set where
  constructor review-referent-lead
  field
    candidate : ReviewReferentCandidate
    grade : ReferentEvidenceGrade
    sourceReference : String
    boundedReading : String
    exactObjectIdentityPaid : Bool

open ReviewReferentLead public

earlierStudyReleaseLead : ReviewReferentLead
earlierStudyReleaseLead = review-referent-lead
  earlierNASAStudyReferent
  secondaryReconstructionLead
  "Courtney Marchesani reconstruction of Amy's Estes Park email; NASA/TM-20205010911 retrospective account of the 2015-2016 SAA8-1519855 programme"
  "A secondary reconstruction reads Amy's IP-release dependency as earlier NASA-origin work associated with the 2016 programme. The NASA TM independently confirms the earlier programme existed, but no primary Amy-linked identifier currently proves that this programme itself was the unnamed review object."
  false

laterTMTransitionLead : ReviewReferentLead
laterTMTransitionLead = review-referent-lead
  laterNASATMReferent
  directWitnessLead
  "Courtney Marchesani report of later Aiden Schaeffer interview; NASA NTRS 20205010911"
  "Later reporting says Schaeffer identified Eskridge-Nelson-Schoenfeld (2021) as the NASA paper Amy was transitioning. The underlying Schaeffer recording remains unrecovered, so this is retained as a witness lead rather than exact identity."
  false

instituteDerivativeLead : ReviewReferentLead
instituteDerivativeLead = review-referent-lead
  instituteDerivativeReferent
  compatibilityOnly
  "Amy September-2020 captured statement; Institute private-maturation attribution"
  "Amy distinguished later Institute-matured results from the NASA-origin foundation. The Institute derivative therefore remains a related but separately identified object, not the default referent of the NASA review object."
  false

------------------------------------------------------------------------
-- Existing object-lineage facts constrain the fork.
------------------------------------------------------------------------

studyAndTMRemainDistinctObjects :
  Lineage.earlierStudyDistinctFromLaterTM
    Lineage.canonicalCurrentPOAMSLineageAssessment ≡ true
studyAndTMRemainDistinctObjects = refl

reviewToTMStillStrongCandidateOnly :
  Identity.grade Candidate.poamsCandidate ≡ Identity.strongCandidate
reviewToTMStillStrongCandidateOnly = refl

reviewToTMExactIdentityStillUnowned :
  Lineage.reviewObjectToTMExactIdentityOwned
    Lineage.canonicalCurrentPOAMSLineageAssessment ≡ false
reviewToTMExactIdentityStillUnowned = refl

primaryNASAReviewIdentifierStillMissing :
  Lineage.primaryNASAReviewIdentifierRecovered
    Lineage.canonicalCurrentPOAMSLineageAssessment ≡ false
primaryNASAReviewIdentifierStillMissing = refl

------------------------------------------------------------------------
-- Resolver: all plausible referents route back to identity-specific evidence.
------------------------------------------------------------------------

referentResolverDiscriminator : ReviewReferentCandidate -> D.IdentityDiscriminator
referentResolverDiscriminator earlierNASAStudyReferent = D.primaryNASAReleaseIdentifier
referentResolverDiscriminator laterNASATMReferent = D.correspondenceSameObjectStatement
referentResolverDiscriminator instituteDerivativeReferent = D.instituteDerivativeObjectIdentifier

record ReviewReferentResolution : Set where
  constructor review-referent-resolution
  field
    selectedReferent : ReviewReferentCandidate
    discriminator : D.IdentityDiscriminatorReceipt
    discriminatorTargetsSelectedRoute :
      D.target discriminator ≡ referentResolverDiscriminator selectedReferent
    discriminatorPaid : D.state discriminator ≡ D.paid
    discriminatorMayPromote : D.mayPromoteExactIdentity discriminator ≡ true
    primarySameObjectReference : String

open ReviewReferentResolution public

------------------------------------------------------------------------
-- Temporal discriminator.
--
-- Amy's captured September-2020 statement expected publication soon. NTRS
-- records the eventual TM as acquired 1 Dec 2020 and published 1 Nov 2021.
-- That chronology is compatible with a delayed release path but is not an
-- identifier and therefore cannot choose between the earlier-study and later-
-- TM referents by itself.
------------------------------------------------------------------------

record ReviewPublicationChronology : Set where
  constructor review-publication-chronology
  field
    amyStatementInSeptember2020 : Bool
    nasaTMAcquiredDecember2020 : Bool
    nasaTMPublishedNovember2021 : Bool
    chronologyCompatibleWithLaterTM : Bool
    chronologyDeterminesExactReferent : Bool

open ReviewPublicationChronology public

canonicalReviewPublicationChronology : ReviewPublicationChronology
canonicalReviewPublicationChronology =
  review-publication-chronology true true true true false

record ReviewReferentBoundary : Set where
  constructor review-referent-boundary
  field
    earlierStudyEqualsLaterTM : Bool
    secondaryEarlierStudyReadingDeterminesReferent : Bool
    laterWitnessTMReadingDeterminesReferentWithoutCarrier : Bool
    compatibleChronologyDeterminesReferent : Bool
    sourceDisagreementMayBeRetainedWithoutForcedReconciliation : Bool
    primaryIdentityReceiptMayResolveReferent : Bool
    resolvingReviewReferentAutomaticallyIdentifiesInstituteDerivative : Bool
    resolvingReviewReferentCreatesDeathCausation : Bool

open ReviewReferentBoundary public

canonicalReviewReferentBoundary : ReviewReferentBoundary
canonicalReviewReferentBoundary =
  review-referent-boundary
    false false false false
    true true false false
