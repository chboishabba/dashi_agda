module DASHI.Culture.MissingDeceasedTwentyScientistRound50ProfessionalEvidenceRoomExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Core.EvidenceReliabilityPolarityExact as Polarity
import DASHI.Interop.OSINTBoundedNegativeSearchAdapterExact as Negative
import DASHI.Culture.MissingDeceasedTwentyScientistRound49SourceOriginIndependenceAuditExact as R49
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as Anti

------------------------------------------------------------------------
-- ROUND 50: PROFESSIONAL EVIDENCE ROOM
--
-- One shared evidence ledger, three consumer-specific gates. Investigators,
-- lawyers and journalists should not maintain incompatible fact databases.
-- The immutable/source-bound object stays common; tasking, admissibility and
-- publication decisions are projections over it.
------------------------------------------------------------------------

data ProfessionalRole : Set where
  investigatorConsumer : ProfessionalRole
  lawyerConsumer : ProfessionalRole
  journalistConsumer : ProfessionalRole

record SharedEvidenceRoomItem : Set where
  constructor shared-evidence-room-item
  field
    itemId : String
    nativeLocator : String
    archiveOrMirrorLocator : String
    retrievalReference : String
    retrievedAtReference : String
    sourceClassReference : String
    carrierIdentityReference : String
    sourceOriginReference : String
    propositionReference : String
    propositionScope : String
    contentDigestReference : String
    metadataReference : String
    independenceReference : String
    reliabilityReference : String
    polarityReference : String
    lawfulAcquisitionReference : String
    preservationReference : String
    privacyAndHarmReference : String
    correctionsOrRevisionReference : String

open SharedEvidenceRoomItem public

nativeCarrierPreservationRequired : Bool
nativeCarrierPreservationRequired = true

sourceOriginMustSurviveConsumerProjection : Bool
sourceOriginMustSurviveConsumerProjection = true

sameEvidenceDifferentConsumerGates : Bool
sameEvidenceDifferentConsumerGates = true

leadIsNotEvidence : Bool
leadIsNotEvidence = true

analysisCopyMustNotReplacePreservedNativeCarrier : Bool
analysisCopyMustNotReplacePreservedNativeCarrier = true

------------------------------------------------------------------------
-- Investigator projection.
------------------------------------------------------------------------

record InvestigatorGate : Set where
  constructor investigator-gate
  field
    itemReference : String
    hypothesisReference : String
    acquisitionTaskReference : String
    sourceIdentityChecked : Bool
    propositionScopeChecked : Bool
    corroborationIndependenceChecked : Bool
    counterHypothesisSearchPerformed : Bool
    hypothesisDiscriminationReference : String
    boundedNegativeSearchReference : String
    nextBestObservationReference : String
    leadPromotedToEvidenceWithoutReceipt : Bool

open InvestigatorGate public

hypothesisDiscriminationRequiredForInvestigation : Bool
hypothesisDiscriminationRequiredForInvestigation = true

investigatorMustSeparateLeadEvidenceAndInference : Bool
investigatorMustSeparateLeadEvidenceAndInference = true

investigatorNegativeConclusionRequiresCoverage : Bool
investigatorNegativeConclusionRequiresCoverage = true

investigatorNarrativeCannotSelectAcquisitionTask : Bool
investigatorNarrativeCannotSelectAcquisitionTask = true

------------------------------------------------------------------------
-- Lawyer projection.
--
-- Jurisdiction-specific admissibility rules remain external. This owner only
-- models the generic professional obligations: authenticity, provenance,
-- proposition purpose, preservation, objections/residuals and re-auditability.
------------------------------------------------------------------------

record LawyerGate : Set where
  constructor lawyer-gate
  field
    itemReference : String
    offeredPropositionReference : String
    authenticationReference : String
    chainOfCustodyOrProvenanceReference : String
    metadataIntegrityReference : String
    originalOrBestAvailableCarrierReference : String
    hearsayOrSourceRoleReference : String
    relevanceReference : String
    exclusionOrPrejudiceReference : String
    privilegeOrConfidentialityReference : String
    jurisdictionReference : String
    admissibilityStatusReference : String
    unresolvedObjectionReference : String

open LawyerGate public

authenticationRequiredForLegalUse : Bool
authenticationRequiredForLegalUse = true

legalAdmissibilityDoesNotEqualHistoricalTruth : Bool
legalAdmissibilityDoesNotEqualHistoricalTruth = true

legalAdmissibilityDoesNotEqualPublicationEthics : Bool
legalAdmissibilityDoesNotEqualPublicationEthics = true

lawyerMustPreserveObjectionsAndResiduals : Bool
lawyerMustPreserveObjectionsAndResiduals = true

------------------------------------------------------------------------
-- Journalist projection.
------------------------------------------------------------------------

record JournalistGate : Set where
  constructor journalist-gate
  field
    itemReference : String
    publishablePropositionReference : String
    originalSourceChecked : Bool
    independentVerificationReference : String
    sourceMotiveReference : String
    contextReference : String
    rightOfReplyReference : String
    publicInterestReference : String
    harmAssessmentReference : String
    anonymityJustificationReference : String
    attributionReference : String
    correctionPathReference : String
    publicationStatusReference : String

open JournalistGate public

rightOfReplyRequiredForAdversePublication : Bool
rightOfReplyRequiredForAdversePublication = true

publicationReadinessDoesNotEqualLegalAdmissibility : Bool
publicationReadinessDoesNotEqualLegalAdmissibility = true

journalistMustPreferOriginalSourcesWherePossible : Bool
journalistMustPreferOriginalSourcesWherePossible = true

journalistMustRetainCorrectionPath : Bool
journalistMustRetainCorrectionPath = true

journalisticPublicInterestDoesNotErasePrivacy : Bool
journalisticPublicInterestDoesNotErasePrivacy = true

------------------------------------------------------------------------
-- Cross-consumer firewalls.
------------------------------------------------------------------------

investigativeLeadDoesNotAutomaticallyBecomePublishable : Bool
investigativeLeadDoesNotAutomaticallyBecomePublishable = true

publishableClaimDoesNotAutomaticallyBecomeAdmissibleEvidence : Bool
publishableClaimDoesNotAutomaticallyBecomeAdmissibleEvidence = true

admissibleEvidenceDoesNotAutomaticallyBecomeCausalInference : Bool
admissibleEvidenceDoesNotAutomaticallyBecomeCausalInference = true

sameNativeItemMayHaveDifferentConsumerStatuses : Bool
sameNativeItemMayHaveDifferentConsumerStatuses = true

lowReliabilityMovesTowardIgnoranceNotOpposition : Bool
lowReliabilityMovesTowardIgnoranceNotOpposition = true

antiPanopticonBoundaryAnchor : Anti.AntiPanopticonBoundary
antiPanopticonBoundaryAnchor = Anti.canonicalAntiPanopticonBoundary

osintBoundaryAnchor : OSINT.OSINTSnowballBoundary
osintBoundaryAnchor = OSINT.canonicalOSINTSnowballBoundary

negativeSearchBoundaryAnchor : Negative.OSINTNegativeSearchRefinementBoundary
negativeSearchBoundaryAnchor = Negative.canonicalOSINTNegativeSearchRefinementBoundary

------------------------------------------------------------------------
-- External methodological attributions.
------------------------------------------------------------------------

record ProfessionalMethodAttribution : Set where
  constructor professional-method-attribution
  field
    professionalSurface : String
    sourceOwner : String
    sourceReference : String
    importedIdea : String
    attributionBoundary : String

open ProfessionalMethodAttribution public

berkeleyProtocolAttribution : ProfessionalMethodAttribution
berkeleyProtocolAttribution = professional-method-attribution
  "digital open-source investigation / evidentiary preservation"
  "UC Berkeley Human Rights Center + UN OHCHR"
  "Berkeley Protocol on Digital Open Source Investigations (2020)"
  "identify, collect, preserve, verify and analyse digital open-source information using professional, legal and ethical procedures; retain safety and integrity considerations"
  "The Protocol informs workflow design; it does not establish facts about this scientist cohort or jurisdiction-specific admissibility."

berkeleyProtocolAttributed : Bool
berkeleyProtocolAttributed = true

federalRule901Attribution : ProfessionalMethodAttribution
federalRule901Attribution = professional-method-attribution
  "legal authentication"
  "United States Federal Rules of Evidence"
  "Rule 901: Authenticating or Identifying Evidence"
  "a proponent must provide sufficient evidence for a finding that an item is what the proponent claims it is"
  "Rule 901 is a U.S. evidentiary rule and does not govern every jurisdiction or prove the underlying proposition merely because authentication succeeds."

federalRule901Attributed : Bool
federalRule901Attributed = true

spjAttribution : ProfessionalMethodAttribution
spjAttribution = professional-method-attribution
  "journalistic verification and publication ethics"
  "Society of Professional Journalists"
  "SPJ Code of Ethics"
  "verify before publication, use original sources where possible, provide context, identify sources, seek subjects' responses, minimize harm and correct/update"
  "SPJ is an ethical guide rather than legal proof authority and does not determine truth of this cohort's hypotheses."

spjAttributed : Bool
spjAttributed = true

------------------------------------------------------------------------
-- Current application.
------------------------------------------------------------------------

round50H2PaidCount : Nat
round50H2PaidCount = 0

round50H3PaidCount : Nat
round50H3PaidCount = 0

round50ProfessionalWorkflow : String
round50ProfessionalWorkflow = "Use one append-only evidence room keyed by native carrier, retrieval time, digest, source origin, proposition scope, independence, reliability, polarity, lawful access, preservation and privacy/harm metadata. Investigator projection manages leads, competing hypotheses, acquisition tasking, corroboration and bounded negative search. Lawyer projection adds authentication, provenance/chain-of-custody, proposition purpose, relevance, hearsay/source-role, privilege/confidentiality, jurisdiction and unresolved objections. Journalist projection adds original-source verification, source motive, context, independent checking, right of reply, public interest, harm, anonymity justification, attribution and corrections. None of the three consumer gates transfers authority to the others."

round50Pareto : String
round50Pareto = "For the scientist investigation, stop thinking in terms of a single narrative notebook. Build a claim ledger and immutable evidence register first; then maintain role-specific views: investigation task matrix, legal proof/admissibility matrix, and publication claim sheet. Each claim should expose supporting, opposing, ignorance/conflict, source-origin dependence, current promotion status and next discriminating acquisition."
