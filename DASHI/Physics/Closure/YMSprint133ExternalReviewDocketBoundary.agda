module DASHI.Physics.Closure.YMSprint133ExternalReviewDocketBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint131ExternalGovernanceBoundary
  as S131-GOV
import DASHI.Physics.Closure.YMSprint132RedTeamObjectionResolutionLedger
  as S132-RED
import DASHI.Physics.Closure.YMSprint132ReproducibilityBoundaryLedger
  as S132-REPRO

------------------------------------------------------------------------
-- Sprint133 external review docket boundary.
--
-- This module records the concrete external-review docket rows after the
-- Sprint131 governance boundary and Sprint132 ledgers.  The repository may
-- export imported internal packet/readiness facts only.  Every external
-- gate in this docket is absent, the external acceptance token is false,
-- and Clay Yang-Mills promotion remains false.

sprintNumber : Nat
sprintNumber = 133

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint133ExternalReviewDocketBoundary.agda"

docketName : String
docketName =
  "Sprint133 external review docket boundary"

docketLane : String
docketLane =
  "Sprint133-external-review-docket-boundary"

sourceSprint131GovernancePath : String
sourceSprint131GovernancePath = S131-GOV.modulePath

sourceSprint132RedTeamPath : String
sourceSprint132RedTeamPath = S132-RED.modulePath

sourceSprint132ReproducibilityPath : String
sourceSprint132ReproducibilityPath = S132-REPRO.modulePath

internalCandidatePacketReady : Bool
internalCandidatePacketReady = S131-GOV.internalCandidateReady

internalSubmissionPacketReady : Bool
internalSubmissionPacketReady = S131-GOV.internalSubmissionReady

internalRedTeamResolved : Bool
internalRedTeamResolved = S132-RED.internalObjectionsResolved

internalReproducibilityVerified : Bool
internalReproducibilityVerified =
  S132-REPRO.internalReproducibilityVerified

qualifyingPublicationGatePresent : Bool
qualifyingPublicationGatePresent = S131-GOV.publicationGatePresent

peerCommunityReviewGatePresent : Bool
peerCommunityReviewGatePresent = S131-GOV.reviewGatePresent

twoYearWaitGatePresent : Bool
twoYearWaitGatePresent = S131-GOV.waitingIntervalGatePresent

cmiDecisionGatePresent : Bool
cmiDecisionGatePresent = S131-GOV.cmiDecisionGatePresent

acceptanceTokenPresent : Bool
acceptanceTokenPresent = S132-REPRO.externalAcceptanceTokenPresent

humanSubmissionPacketHandoffExternalGatePresent : Bool
humanSubmissionPacketHandoffExternalGatePresent = false

externalReviewDocketComplete : Bool
externalReviewDocketComplete = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

internalCandidatePacketReadyIsTrue :
  internalCandidatePacketReady ≡ true
internalCandidatePacketReadyIsTrue =
  S131-GOV.internalCandidateReadyIsTrue

internalSubmissionPacketReadyIsTrue :
  internalSubmissionPacketReady ≡ true
internalSubmissionPacketReadyIsTrue =
  S131-GOV.internalSubmissionReadyIsTrue

internalRedTeamResolvedIsTrue :
  internalRedTeamResolved ≡ true
internalRedTeamResolvedIsTrue =
  S132-RED.internalObjectionsResolvedIsTrue

internalReproducibilityVerifiedIsTrue :
  internalReproducibilityVerified ≡ true
internalReproducibilityVerifiedIsTrue =
  S132-REPRO.internalReproducibilityVerifiedIsTrue

qualifyingPublicationGatePresentIsFalse :
  qualifyingPublicationGatePresent ≡ false
qualifyingPublicationGatePresentIsFalse =
  S131-GOV.publicationGatePresentIsFalse

peerCommunityReviewGatePresentIsFalse :
  peerCommunityReviewGatePresent ≡ false
peerCommunityReviewGatePresentIsFalse =
  S131-GOV.reviewGatePresentIsFalse

twoYearWaitGatePresentIsFalse :
  twoYearWaitGatePresent ≡ false
twoYearWaitGatePresentIsFalse =
  S131-GOV.waitingIntervalGatePresentIsFalse

cmiDecisionGatePresentIsFalse :
  cmiDecisionGatePresent ≡ false
cmiDecisionGatePresentIsFalse =
  S131-GOV.cmiDecisionGatePresentIsFalse

acceptanceTokenPresentIsFalse :
  acceptanceTokenPresent ≡ false
acceptanceTokenPresentIsFalse =
  S132-REPRO.externalAcceptanceTokenPresentIsFalse

humanSubmissionPacketHandoffExternalGatePresentIsFalse :
  humanSubmissionPacketHandoffExternalGatePresent ≡ false
humanSubmissionPacketHandoffExternalGatePresentIsFalse = refl

externalReviewDocketCompleteIsFalse :
  externalReviewDocketComplete ≡ false
externalReviewDocketCompleteIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data ExternalReviewDocketCode : Set where
  qualifying-publication :
    ExternalReviewDocketCode
  peer-community-review :
    ExternalReviewDocketCode
  two-year-wait :
    ExternalReviewDocketCode
  cmi-decision :
    ExternalReviewDocketCode
  acceptance-token :
    ExternalReviewDocketCode
  human-submission-packet-handoff :
    ExternalReviewDocketCode

data ExternalReviewDocketStatus : Set where
  absent-external-gate :
    ExternalReviewDocketStatus
  absent-acceptance-token :
    ExternalReviewDocketStatus
  internal-packet-ready-external-handoff-open :
    ExternalReviewDocketStatus

data ExternalReviewDocketAuthority : Set where
  sprint131-external-governance :
    ExternalReviewDocketAuthority
  sprint132-red-team-ledger :
    ExternalReviewDocketAuthority
  sprint132-reproducibility-ledger :
    ExternalReviewDocketAuthority

record ExternalReviewDocketRow : Set where
  constructor mkExternalReviewDocketRow
  field
    code :
      ExternalReviewDocketCode
    rowCode :
      String
    description :
      String
    authority :
      ExternalReviewDocketAuthority
    sourcePath :
      String
    internalPacketReady :
      Bool
    internalPacketReadyIsTrue :
      internalPacketReady ≡ true
    externalGatePresent :
      Bool
    externalGatePresentIsFalse :
      externalGatePresent ≡ false
    status :
      ExternalReviewDocketStatus
    docketText :
      String

qualifyingPublicationRow : ExternalReviewDocketRow
qualifyingPublicationRow =
  mkExternalReviewDocketRow
    qualifying-publication
    "qualifying-publication"
    "Qualifying publication for the Clay-facing Yang-Mills claim"
    sprint131-external-governance
    sourceSprint131GovernancePath
    internalSubmissionPacketReady
    internalSubmissionPacketReadyIsTrue
    qualifyingPublicationGatePresent
    qualifyingPublicationGatePresentIsFalse
    absent-external-gate
    "No qualifying publication gate is present in the repository."

peerCommunityReviewRow : ExternalReviewDocketRow
peerCommunityReviewRow =
  mkExternalReviewDocketRow
    peer-community-review
    "peer-community-review"
    "Peer and community review after qualifying publication"
    sprint132-red-team-ledger
    sourceSprint132RedTeamPath
    internalRedTeamResolved
    internalRedTeamResolvedIsTrue
    peerCommunityReviewGatePresent
    peerCommunityReviewGatePresentIsFalse
    absent-external-gate
    "Internal red-team objections are resolved by imported evidence; external peer and community review is absent."

twoYearWaitRow : ExternalReviewDocketRow
twoYearWaitRow =
  mkExternalReviewDocketRow
    two-year-wait
    "two-year-wait"
    "Two-year external waiting interval after publication"
    sprint131-external-governance
    sourceSprint131GovernancePath
    internalSubmissionPacketReady
    internalSubmissionPacketReadyIsTrue
    twoYearWaitGatePresent
    twoYearWaitGatePresentIsFalse
    absent-external-gate
    "No elapsed two-year external waiting interval is present in the repository."

cmiDecisionRow : ExternalReviewDocketRow
cmiDecisionRow =
  mkExternalReviewDocketRow
    cmi-decision
    "CMI-decision"
    "Clay Mathematics Institute decision on the claim"
    sprint131-external-governance
    sourceSprint131GovernancePath
    internalSubmissionPacketReady
    internalSubmissionPacketReadyIsTrue
    cmiDecisionGatePresent
    cmiDecisionGatePresentIsFalse
    absent-external-gate
    "No CMI decision gate is present, so promotion cannot be exported."

acceptanceTokenRow : ExternalReviewDocketRow
acceptanceTokenRow =
  mkExternalReviewDocketRow
    acceptance-token
    "acceptance-token"
    "External acceptance token for Clay/CMI promotion"
    sprint132-reproducibility-ledger
    sourceSprint132ReproducibilityPath
    internalReproducibilityVerified
    internalReproducibilityVerifiedIsTrue
    acceptanceTokenPresent
    acceptanceTokenPresentIsFalse
    absent-acceptance-token
    "Sprint132 reproducibility is verified internally; the external acceptance token remains false."

humanSubmissionPacketHandoffRow : ExternalReviewDocketRow
humanSubmissionPacketHandoffRow =
  mkExternalReviewDocketRow
    human-submission-packet-handoff
    "human-submission-packet-handoff"
    "Human submission packet handoff to external publication and review process"
    sprint131-external-governance
    sourceSprint131GovernancePath
    internalSubmissionPacketReady
    internalSubmissionPacketReadyIsTrue
    humanSubmissionPacketHandoffExternalGatePresent
    humanSubmissionPacketHandoffExternalGatePresentIsFalse
    internal-packet-ready-external-handoff-open
    "Imported internal submission packet readiness is true; external human handoff completion is absent."

externalReviewDocketRows : List ExternalReviewDocketRow
externalReviewDocketRows =
  qualifyingPublicationRow
  ∷ peerCommunityReviewRow
  ∷ twoYearWaitRow
  ∷ cmiDecisionRow
  ∷ acceptanceTokenRow
  ∷ humanSubmissionPacketHandoffRow
  ∷ []

canonicalExternalReviewDocketCodes : List ExternalReviewDocketCode
canonicalExternalReviewDocketCodes =
  qualifying-publication
  ∷ peer-community-review
  ∷ two-year-wait
  ∷ cmi-decision
  ∷ acceptance-token
  ∷ human-submission-packet-handoff
  ∷ []

record ExternalReviewDocketBoundaryFlags : Set where
  constructor mkExternalReviewDocketBoundaryFlags
  field
    qualifyingPublicationAbsent :
      qualifyingPublicationGatePresent ≡ false
    peerCommunityReviewAbsent :
      peerCommunityReviewGatePresent ≡ false
    twoYearWaitAbsent :
      twoYearWaitGatePresent ≡ false
    cmiDecisionAbsent :
      cmiDecisionGatePresent ≡ false
    acceptanceTokenAbsent :
      acceptanceTokenPresent ≡ false
    humanSubmissionPacketHandoffExternalAbsent :
      humanSubmissionPacketHandoffExternalGatePresent ≡ false
    docketCompleteFalse :
      externalReviewDocketComplete ≡ false
    promotionFalse :
      clayYangMillsPromoted ≡ false

canonicalExternalReviewDocketBoundaryFlags :
  ExternalReviewDocketBoundaryFlags
canonicalExternalReviewDocketBoundaryFlags =
  mkExternalReviewDocketBoundaryFlags
    qualifyingPublicationGatePresentIsFalse
    peerCommunityReviewGatePresentIsFalse
    twoYearWaitGatePresentIsFalse
    cmiDecisionGatePresentIsFalse
    acceptanceTokenPresentIsFalse
    humanSubmissionPacketHandoffExternalGatePresentIsFalse
    externalReviewDocketCompleteIsFalse
    clayYangMillsPromotedIsFalse

record ImportedInternalReadinessEvidence : Set where
  constructor mkImportedInternalReadinessEvidence
  field
    sprint131GovernanceReceipt :
      S131-GOV.ExternalClayCmiGovernanceBoundary
    sprint132ReproducibilityReceipt :
      S132-REPRO.ReproducibilityBoundaryLedger
    candidatePacketReady :
      internalCandidatePacketReady ≡ true
    submissionPacketReady :
      internalSubmissionPacketReady ≡ true
    redTeamResolved :
      internalRedTeamResolved ≡ true
    reproducibilityVerified :
      internalReproducibilityVerified ≡ true
    sprint131NoPromotion :
      S131-GOV.externalClayCmiPromotion ≡ false
    sprint132NoPromotion :
      S132-REPRO.clayYangMillsPromoted ≡ false

canonicalImportedInternalReadinessEvidence :
  ImportedInternalReadinessEvidence
canonicalImportedInternalReadinessEvidence =
  mkImportedInternalReadinessEvidence
    S131-GOV.canonicalReceipt
    S132-REPRO.sprint132ReproducibilityBoundaryLedger
    internalCandidatePacketReadyIsTrue
    internalSubmissionPacketReadyIsTrue
    internalRedTeamResolvedIsTrue
    internalReproducibilityVerifiedIsTrue
    S131-GOV.externalClayCmiPromotionIsFalse
    S132-REPRO.clayYangMillsPromotedIsFalse

record ExternalReviewDocketBoundary : Set where
  constructor mkExternalReviewDocketBoundary
  field
    receiptSprint :
      Nat
    receiptPath :
      String
    receiptName :
      String
    receiptLane :
      String
    readinessEvidence :
      ImportedInternalReadinessEvidence
    docketRows :
      List ExternalReviewDocketRow
    docketCodes :
      List ExternalReviewDocketCode
    boundaryFlags :
      ExternalReviewDocketBoundaryFlags
    terminalStatus :
      ExternalReviewDocketStatus
    terminalText :
      String
    candidatePacketReady :
      internalCandidatePacketReady ≡ true
    submissionPacketReady :
      internalSubmissionPacketReady ≡ true
    allExternalDocketGatesAbsent :
      externalReviewDocketComplete ≡ false
    noClayYangMillsPromotion :
      clayYangMillsPromoted ≡ false

canonicalExternalReviewDocketBoundary :
  ExternalReviewDocketBoundary
canonicalExternalReviewDocketBoundary =
  mkExternalReviewDocketBoundary
    sprintNumber
    modulePath
    docketName
    docketLane
    canonicalImportedInternalReadinessEvidence
    externalReviewDocketRows
    canonicalExternalReviewDocketCodes
    canonicalExternalReviewDocketBoundaryFlags
    absent-acceptance-token
    "Internal packet readiness, red-team resolution, and reproducibility are imported as true; qualifying publication, peer/community review, two-year wait, CMI decision, acceptance token, and human handoff external gates are absent; clayYangMillsPromoted=false."
    internalCandidatePacketReadyIsTrue
    internalSubmissionPacketReadyIsTrue
    externalReviewDocketCompleteIsFalse
    clayYangMillsPromotedIsFalse

canonicalReceipt : ExternalReviewDocketBoundary
canonicalReceipt = canonicalExternalReviewDocketBoundary

canonicalNoAcceptanceToken :
  ExternalReviewDocketBoundaryFlags.acceptanceTokenAbsent
    (ExternalReviewDocketBoundary.boundaryFlags canonicalReceipt)
    ≡ acceptanceTokenPresentIsFalse
canonicalNoAcceptanceToken = refl

canonicalNoHumanSubmissionPacketHandoffExternalGate :
  ExternalReviewDocketBoundaryFlags.humanSubmissionPacketHandoffExternalAbsent
    (ExternalReviewDocketBoundary.boundaryFlags canonicalReceipt)
    ≡ humanSubmissionPacketHandoffExternalGatePresentIsFalse
canonicalNoHumanSubmissionPacketHandoffExternalGate = refl

canonicalNoClayYangMillsPromotion :
  ExternalReviewDocketBoundary.noClayYangMillsPromotion canonicalReceipt
    ≡ clayYangMillsPromotedIsFalse
canonicalNoClayYangMillsPromotion = refl
