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
-- PRIMARY AUTHORSHIP ATTRIBUTION FIREWALL
------------------------------------------------------------------------

record PublicTMAuthorAttribution : Set where
  constructor public-tm-author-attribution
  field
    publicTMIdentifier : String
    namedAuthors : String
    amyNamedAsAuthor : Bool
    sameSurnameImpliesSamePerson : Bool
    transitionRoleImpliesAuthorship : Bool
    sameObjectReceiptWouldPayTransitionIdentityOnly : Bool

open PublicTMAuthorAttribution public

canonicalPublicTMAuthorAttribution : PublicTMAuthorAttribution
canonicalPublicTMAuthorAttribution = public-tm-author-attribution
  "NASA NTRS 20205010911 / NASA/TM-20205010911 / M-1531"
  "R.H. Eskridge; M.A. Nelson; M.P. Schoenfeld"
  false false false true

------------------------------------------------------------------------
-- POLICY-REQUIRED RELEASE-AUTHORIZATION CARRIER
------------------------------------------------------------------------

record RequiredDAACarrier : Set where
  constructor required-daa-carrier
  field
    publicObject : String
    governingPolicy : String
    externalSTIRequiresDAA : Bool
    releasedReportRequiresApprovedDAA : Bool
    poamsSpecificDAARecovered : Bool
    daaAttachedObjectIdentityRecovered : Bool
    amyReviewObjectEqualsDAAObjectPaid : Bool
    acquisitionTarget : String

open RequiredDAACarrier public

poamsTMRequiredDAACarrier : RequiredDAACarrier
poamsTMRequiredDAACarrier = required-daa-carrier
  "NASA/TM-20205010911 / M-1531 / NTRS 20205010911"
  "NASA NPR 2200.2C/2D STI publication/dissemination requirements"
  true true false false false
  "POAMS-specific NF-1676/EDAA or Center DAA record; routing/approval dates and restrictions; attached manuscript/version; same-object crosswalk to NTRS 20205010911; any primary correspondence tying Amy's September-2020 review object to that DAA object"

------------------------------------------------------------------------
-- MARSHALL EDAA IDENTIFIER-FAMILY DISCRIMINATOR
--
-- NASA's STI publication guide records Marshall as one of the Centers using the
-- Agency Electronic Document Availability Authorization (EDAA / NF-1676B)
-- workflow. Contemporaneous 2020 Marshall NTRS records expose report numbers in
-- the form MSFC-E-DAA-TN##### (for example MSFC-E-DAA-TN77428 and
-- MSFC-E-DAA-TN79181-1/-2). This pays an identifier-family search constraint,
-- not a POAMS identifier. NTRS 20205010911 currently exposes M-1531 but not an
-- MSFC-E-DAA number on its public citation page, so an exact number must not be
-- guessed from the NTRS ID, M-1531, funding suffix, or neighboring records.
------------------------------------------------------------------------

record MarshallEDAAIdentifierFamily : Set where
  constructor marshall-edaa-identifier-family
  field
    center : String
    workflow : String
    observed2020IdentifierFamily : String
    primaryExamples : String
    poamsExactEDAAIdentifierRecovered : Bool
    ntrsPageExposesPOAMSEDAAIdentifier : Bool
    identifierMayBeInferredFromM1531 : Bool
    identifierMayBeInferredFromNTRSID : Bool
    identifierMayBeInferredFromFundingSuffix : Bool
    targetedSearchSurface : String

open MarshallEDAAIdentifierFamily public

poamsMarshallEDAAIdentifierFamily : MarshallEDAAIdentifierFamily
poamsMarshallEDAAIdentifierFamily = marshall-edaa-identifier-family
  "NASA Marshall Space Flight Center"
  "Agency EDAA / NF-1676B release-authorization workflow"
  "MSFC-E-DAA-TN##### with possible manifestation suffixes such as -1/-2"
  "NASA STI publishing guide; NTRS 20200001187 = MSFC-E-DAA-TN77428; NTRS 20200003509/20200003510 = MSFC-E-DAA-TN79181-1/-2"
  false false false false false
  "Marshall EDAA/NF-1676B records around late 2020 tied to M-1531, NTRS 20205010911, R.H. Eskridge, M.A. Nelson, M.P. Schoenfeld, POAMS, SAA8-1519855, or funding MSFC-RMB-QUANTUM-SAA8-1519855-1; require attached-object/version crosswalk before identity promotion"

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
    sameSurnameCreatesAmyAuthorship : Bool
    transitionRoleCreatesAmyAuthorship : Bool
    policyRequiredDAAImpliesAmyReviewObjectEqualsPublicTM : Bool
    policyRequiredDAAImpliesInstituteDerivativeReleased : Bool
    marshallEDAAFamilyImpliesExactPOAMSIdentifier : Bool
    neighboringEDAANumbersMayBeInterpolated : Bool

open ReviewReferentBoundary public

canonicalReviewReferentBoundary : ReviewReferentBoundary
canonicalReviewReferentBoundary =
  review-referent-boundary
    false false false false
    true true false false
    false false false false
    false false
