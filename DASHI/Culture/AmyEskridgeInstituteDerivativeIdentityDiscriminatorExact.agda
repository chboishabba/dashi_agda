module DASHI.Culture.AmyEskridgeInstituteDerivativeIdentityDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeBoundaryCandidateIdentityBidiExact as Identity
import DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact as Candidate
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App
import DASHI.Culture.POAMSLayeredReleaseExact as Release

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: INSTITUTE DERIVATIVE IDENTITY DISCRIMINATOR
--
-- The repo already owns four related-but-not-identical objects:
--
--   X1 NASA / Quantum Machines POAMS experimental programme
--   X2 NASA/TM-20205010911 / M-1531 public report
--   X3 Institute-derived / privately matured application work
--   X4 Amy's unnamed September-2020 NASA-review object
--
-- Existing evidence makes X4 -> X2 a strong candidate relation, but the
-- identity core requires an identity-specific receipt before exact promotion.
-- This owner types the remaining discriminators instead of reopening a broad
-- evidence search or collapsing X1=X2=X3=X4.
------------------------------------------------------------------------

data AmyRelatedApplicationObject : Set where
  nasaQuantumMachinesProgramme : AmyRelatedApplicationObject
  nasaTM20205010911 : AmyRelatedApplicationObject
  institutePrivateDerivative : AmyRelatedApplicationObject
  amySeptember2020ReviewObject : AmyRelatedApplicationObject

data IdentityDiscriminator : Set where
  primaryNASAReleaseIdentifier : IdentityDiscriminator
  exactPaperOrAttachmentTitle : IdentityDiscriminator
  exactAttachmentOrDraftFilename : IdentityDiscriminator
  versionedDraftIdentifier : IdentityDiscriminator
  correspondenceSameObjectStatement : IdentityDiscriminator
  directWitnessCarrierWithObjectIdentifier : IdentityDiscriminator
  instituteDerivativeObjectIdentifier : IdentityDiscriminator
  apparatusOrDatasetIdentityReceipt : IdentityDiscriminator

data DiscriminatorState : Set where
  paid : DiscriminatorState
  retainedLead : DiscriminatorState
  unpaid : DiscriminatorState

record IdentityDiscriminatorReceipt : Set where
  constructor identity-discriminator-receipt
  field
    target : IdentityDiscriminator
    state : DiscriminatorState
    sourceReference : String
    mayPromoteExactIdentity : Bool

open IdentityDiscriminatorReceipt public

------------------------------------------------------------------------
-- What is already paid around the candidate.
------------------------------------------------------------------------

reviewToTMIsStrongCandidate :
  Identity.grade Candidate.poamsCandidate ≡ Identity.strongCandidate
reviewToTMIsStrongCandidate = refl

exactReviewToTMIdentityStillUnpaid :
  Candidate.poamsExactSameObjectEstablished Candidate.canonicalCurrentPOAMSCandidateAssessment ≡ false
exactReviewToTMIdentityStillUnpaid = refl

exactIdentityStillRequiresPrimaryWeld :
  Candidate.exactIdentityStillNeedsPrimaryWeld Candidate.canonicalCurrentPOAMSCandidateAssessment ≡ true
exactIdentityStillRequiresPrimaryWeld = refl

applicationRouterStillStartsAtDerivativeIdentity :
  App.firstAmyApplicationMissingLeaf ≡ App.acquireInstituteDerivedObjectIdentity
applicationRouterStillStartsAtDerivativeIdentity = refl

instituteDerivativeReleaseStateDoesNotIdentifyObject :
  Release.state Release.poamsPrivateDerivatives ≡ Release.unknown
instituteDerivativeReleaseStateDoesNotIdentifyObject = refl

------------------------------------------------------------------------
-- Current discriminator ledger.
--
-- The existing repo pays compatibility coordinates but does not contain an
-- exact primary identifier/title/version/correspondence receipt equating X3 or
-- X4 with X1/X2. Later witness linkage remains useful as a retained lead only.
------------------------------------------------------------------------

nasaReleaseIdentifierReceipt : IdentityDiscriminatorReceipt
nasaReleaseIdentifierReceipt = identity-discriminator-receipt
  primaryNASAReleaseIdentifier unpaid
  "No Amy-linked DAA/NF-1676/STI release identifier is currently owned for the unnamed September-2020 object."
  false

exactTitleReceipt : IdentityDiscriminatorReceipt
exactTitleReceipt = identity-discriminator-receipt
  exactPaperOrAttachmentTitle unpaid
  "Amy's captured September-2020 statement does not supply the exact reviewed paper or attachment title."
  false

attachmentFilenameReceipt : IdentityDiscriminatorReceipt
attachmentFilenameReceipt = identity-discriminator-receipt
  exactAttachmentOrDraftFilename unpaid
  "No exact Amy workshop attachment/draft filename is currently owned."
  false

versionedDraftReceipt : IdentityDiscriminatorReceipt
versionedDraftReceipt = identity-discriminator-receipt
  versionedDraftIdentifier unpaid
  "No versioned draft identifier currently welds the Amy review object to M-1531/NASA-TM-20205010911."
  false

correspondenceIdentityReceipt : IdentityDiscriminatorReceipt
correspondenceIdentityReceipt = identity-discriminator-receipt
  correspondenceSameObjectStatement unpaid
  "No inspected primary correspondence currently states that the unnamed Amy review object is M-1531/NASA-TM-20205010911 or identifies the Institute derivative."
  false

directWitnessIdentifierLead : IdentityDiscriminatorReceipt
directWitnessIdentifierLead = identity-discriminator-receipt
  directWitnessCarrierWithObjectIdentifier retainedLead
  "Later reporting attributes a POAMS-object identification to Aiden Schaeffer; the direct recording/carrier and exact identifier statement remain unowned."
  false

instituteDerivativeIdentifierReceipt : IdentityDiscriminatorReceipt
instituteDerivativeIdentifierReceipt = identity-discriminator-receipt
  instituteDerivativeObjectIdentifier unpaid
  "The Institute private maturation is source-attributed, but no exact derivative object identifier is currently owned."
  false

apparatusDatasetIdentityReceipt : IdentityDiscriminatorReceipt
apparatusDatasetIdentityReceipt = identity-discriminator-receipt
  apparatusOrDatasetIdentityReceipt unpaid
  "No Institute apparatus or dataset identity receipt currently closes same-object identity with the NASA/QM programme."
  false

------------------------------------------------------------------------
-- Ordered identity residual.
------------------------------------------------------------------------

firstExactIdentityDiscriminator : IdentityDiscriminator
firstExactIdentityDiscriminator = primaryNASAReleaseIdentifier

record AmyInstituteDerivativeIdentityFrontier : Set where
  constructor amy-institute-derivative-identity-frontier
  field
    compatibilityCoordinatesPaid : Bool
    laterWitnessLeadRetained : Bool
    identitySpecificPrimaryReceiptPaid : Bool
    exactReviewToTMIdentityPaid : Bool
    exactInstituteDerivativeIdentityPaid : Bool
    laterCustodyEvidenceMayBeRetained : Bool
    laterCustodyEvidenceMaySkipObjectIdentity : Bool

open AmyInstituteDerivativeIdentityFrontier public

canonicalAmyInstituteDerivativeIdentityFrontier : AmyInstituteDerivativeIdentityFrontier
canonicalAmyInstituteDerivativeIdentityFrontier =
  amy-institute-derivative-identity-frontier
    true true false false false true false

record AmyInstituteDerivativeIdentityBoundary : Set where
  constructor amy-institute-derivative-identity-boundary
  field
    strongCandidateEqualsExactIdentity : Bool
    laterWitnessReportEqualsPrimaryIdentifierReceipt : Bool
    sameTeamAndTimelineEqualsSameObject : Bool
    publicTMEqualsInstitutePrivateDerivative : Bool
    privateMaturationClaimEqualsDerivativeIdentifier : Bool
    privateQuantumMachinesCustodyEqualsInstituteCustody : Bool
    apparatusSimilarityEqualsSameCarrier : Bool
    exactIdentifierMayPayIdentityConsumer : Bool
    exactIdentityMayThenUnlockDownstreamCustodyPayment : Bool
    identityPromotionCreatesDeathCausation : Bool

open AmyInstituteDerivativeIdentityBoundary public

canonicalAmyInstituteDerivativeIdentityBoundary : AmyInstituteDerivativeIdentityBoundary
canonicalAmyInstituteDerivativeIdentityBoundary =
  amy-institute-derivative-identity-boundary
    false false false false false false false true true false
