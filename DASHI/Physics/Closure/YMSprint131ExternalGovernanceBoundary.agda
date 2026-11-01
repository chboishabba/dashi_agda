module DASHI.Physics.Closure.YMSprint131ExternalGovernanceBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint130FinalClayAssemblyLedger as S130

------------------------------------------------------------------------
-- Sprint131 external Clay/CMI governance boundary.
--
-- Sprint130 is consumed as the internal readiness ledger: candidate packet
-- ready, submission packet ready, external acceptance absent, and no Clay
-- Yang-Mills promotion.  Sprint131 records the next boundary outside the
-- repository: publication, review, waiting interval, community validation,
-- and CMI decision gates are absent here.  Internal readiness is therefore
-- preserved as true while promotion remains false.

sprintNumber : Nat
sprintNumber = 131

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint131ExternalGovernanceBoundary.agda"

boundaryName : String
boundaryName =
  "Sprint131 external Clay/CMI governance boundary"

boundaryLane : String
boundaryLane = "Sprint131-external-governance-boundary"

sourceSprint130Path : String
sourceSprint130Path = S130.modulePath

internalCandidateReady : Bool
internalCandidateReady =
  S130.internalCandidatePacketReady

internalSubmissionReady : Bool
internalSubmissionReady =
  S130.internalSubmissionPacketReady

sprint130ExternalAcceptanceAbsent : Bool
sprint130ExternalAcceptanceAbsent =
  S130.externalAcceptanceTokenPresent

sprint130PromotionFalse : Bool
sprint130PromotionFalse =
  S130.clayYangMillsPromoted

publicationGatePresent : Bool
publicationGatePresent = false

reviewGatePresent : Bool
reviewGatePresent = false

waitingIntervalGatePresent : Bool
waitingIntervalGatePresent = false

communityValidationGatePresent : Bool
communityValidationGatePresent = false

cmiDecisionGatePresent : Bool
cmiDecisionGatePresent = false

externalGovernanceComplete : Bool
externalGovernanceComplete = false

externalClayCmiPromotion : Bool
externalClayCmiPromotion = false

internalCandidateReadyIsTrue : internalCandidateReady ≡ true
internalCandidateReadyIsTrue = refl

internalSubmissionReadyIsTrue : internalSubmissionReady ≡ true
internalSubmissionReadyIsTrue = refl

sprint130ExternalAcceptanceAbsentIsFalse :
  sprint130ExternalAcceptanceAbsent ≡ false
sprint130ExternalAcceptanceAbsentIsFalse = refl

sprint130PromotionFalseIsFalse :
  sprint130PromotionFalse ≡ false
sprint130PromotionFalseIsFalse = refl

publicationGatePresentIsFalse : publicationGatePresent ≡ false
publicationGatePresentIsFalse = refl

reviewGatePresentIsFalse : reviewGatePresent ≡ false
reviewGatePresentIsFalse = refl

waitingIntervalGatePresentIsFalse : waitingIntervalGatePresent ≡ false
waitingIntervalGatePresentIsFalse = refl

communityValidationGatePresentIsFalse :
  communityValidationGatePresent ≡ false
communityValidationGatePresentIsFalse = refl

cmiDecisionGatePresentIsFalse : cmiDecisionGatePresent ≡ false
cmiDecisionGatePresentIsFalse = refl

externalGovernanceCompleteIsFalse :
  externalGovernanceComplete ≡ false
externalGovernanceCompleteIsFalse = refl

externalClayCmiPromotionIsFalse :
  externalClayCmiPromotion ≡ false
externalClayCmiPromotionIsFalse = refl

data ExternalGovernanceGate : Set where
  publication-gate :
    ExternalGovernanceGate
  review-gate :
    ExternalGovernanceGate
  waiting-interval-gate :
    ExternalGovernanceGate
  community-validation-gate :
    ExternalGovernanceGate
  cmi-decision-gate :
    ExternalGovernanceGate

data ExternalGovernanceStatus : Set where
  recorded-absent :
    ExternalGovernanceStatus
  waits-outside-repository :
    ExternalGovernanceStatus
  blocks-promotion :
    ExternalGovernanceStatus

canonicalExternalGovernanceGates : List ExternalGovernanceGate
canonicalExternalGovernanceGates =
  publication-gate
  ∷ review-gate
  ∷ waiting-interval-gate
  ∷ community-validation-gate
  ∷ cmi-decision-gate
  ∷ []

record ExternalGovernanceRow : Set where
  constructor mkExternalGovernanceRow
  field
    gate :
      ExternalGovernanceGate
    gateCode :
      String
    gateDescription :
      String
    gatePresent :
      Bool
    gatePresentIsFalse :
      gatePresent ≡ false
    status :
      ExternalGovernanceStatus
    statusText :
      String

publicationRow : ExternalGovernanceRow
publicationRow =
  mkExternalGovernanceRow
    publication-gate
    "publication"
    "Public Clay-facing publication record"
    publicationGatePresent
    publicationGatePresentIsFalse
    recorded-absent
    "No publication gate is present in the repository boundary."

reviewRow : ExternalGovernanceRow
reviewRow =
  mkExternalGovernanceRow
    review-gate
    "review"
    "External mathematical review record"
    reviewGatePresent
    reviewGatePresentIsFalse
    recorded-absent
    "No external review gate is present in the repository boundary."

waitingIntervalRow : ExternalGovernanceRow
waitingIntervalRow =
  mkExternalGovernanceRow
    waiting-interval-gate
    "wait"
    "External waiting interval required by Clay/CMI governance"
    waitingIntervalGatePresent
    waitingIntervalGatePresentIsFalse
    waits-outside-repository
    "No elapsed external waiting interval gate is present here."

communityValidationRow : ExternalGovernanceRow
communityValidationRow =
  mkExternalGovernanceRow
    community-validation-gate
    "community"
    "Community validation and objection-clearance record"
    communityValidationGatePresent
    communityValidationGatePresentIsFalse
    waits-outside-repository
    "No community validation gate is present in this Agda module."

cmiDecisionRow : ExternalGovernanceRow
cmiDecisionRow =
  mkExternalGovernanceRow
    cmi-decision-gate
    "CMI-decision"
    "Clay Mathematics Institute decision record"
    cmiDecisionGatePresent
    cmiDecisionGatePresentIsFalse
    blocks-promotion
    "No CMI decision gate is present, so no promotion is exported."

canonicalExternalGovernanceRows : List ExternalGovernanceRow
canonicalExternalGovernanceRows =
  publicationRow
  ∷ reviewRow
  ∷ waitingIntervalRow
  ∷ communityValidationRow
  ∷ cmiDecisionRow
  ∷ []

record Sprint130InternalReadinessInput : Set where
  constructor mkSprint130InternalReadinessInput
  field
    sourceLedger :
      S130.FinalClayAssemblyLedger
    sourcePath :
      String
    candidateReady :
      Bool
    candidateReadyIsTrue :
      candidateReady ≡ true
    submissionReady :
      Bool
    submissionReadyIsTrue :
      submissionReady ≡ true
    sourceExternalAcceptancePresent :
      Bool
    sourceExternalAcceptancePresentIsFalse :
      sourceExternalAcceptancePresent ≡ false
    sourceClayPromoted :
      Bool
    sourceClayPromotedIsFalse :
      sourceClayPromoted ≡ false

canonicalSprint130InternalReadinessInput :
  Sprint130InternalReadinessInput
canonicalSprint130InternalReadinessInput =
  mkSprint130InternalReadinessInput
    S130.canonicalReceipt
    sourceSprint130Path
    internalCandidateReady
    internalCandidateReadyIsTrue
    internalSubmissionReady
    internalSubmissionReadyIsTrue
    sprint130ExternalAcceptanceAbsent
    sprint130ExternalAcceptanceAbsentIsFalse
    sprint130PromotionFalse
    sprint130PromotionFalseIsFalse

record ExternalGovernanceBoundaryFlags : Set where
  constructor mkExternalGovernanceBoundaryFlags
  field
    publicationAbsent :
      publicationGatePresent ≡ false
    reviewAbsent :
      reviewGatePresent ≡ false
    waitingIntervalAbsent :
      waitingIntervalGatePresent ≡ false
    communityValidationAbsent :
      communityValidationGatePresent ≡ false
    cmiDecisionAbsent :
      cmiDecisionGatePresent ≡ false
    governanceCompleteFalse :
      externalGovernanceComplete ≡ false
    promotionFalse :
      externalClayCmiPromotion ≡ false

canonicalExternalGovernanceBoundaryFlags :
  ExternalGovernanceBoundaryFlags
canonicalExternalGovernanceBoundaryFlags =
  mkExternalGovernanceBoundaryFlags
    publicationGatePresentIsFalse
    reviewGatePresentIsFalse
    waitingIntervalGatePresentIsFalse
    communityValidationGatePresentIsFalse
    cmiDecisionGatePresentIsFalse
    externalGovernanceCompleteIsFalse
    externalClayCmiPromotionIsFalse

record ExternalClayCmiGovernanceBoundary : Set where
  constructor mkExternalClayCmiGovernanceBoundary
  field
    receiptSprint :
      Nat
    receiptPath :
      String
    receiptName :
      String
    receiptLane :
      String
    sprint130Input :
      Sprint130InternalReadinessInput
    externalRows :
      List ExternalGovernanceRow
    externalGates :
      List ExternalGovernanceGate
    externalFlags :
      ExternalGovernanceBoundaryFlags
    terminalStatus :
      ExternalGovernanceStatus
    terminalText :
      String
    candidateReady :
      internalCandidateReady ≡ true
    submissionReady :
      internalSubmissionReady ≡ true
    publicationAbsent :
      publicationGatePresent ≡ false
    reviewAbsent :
      reviewGatePresent ≡ false
    waitingIntervalAbsent :
      waitingIntervalGatePresent ≡ false
    communityValidationAbsent :
      communityValidationGatePresent ≡ false
    cmiDecisionAbsent :
      cmiDecisionGatePresent ≡ false
    noGovernanceCompletion :
      externalGovernanceComplete ≡ false
    noPromotion :
      externalClayCmiPromotion ≡ false

canonicalExternalClayCmiGovernanceBoundary :
  ExternalClayCmiGovernanceBoundary
canonicalExternalClayCmiGovernanceBoundary =
  mkExternalClayCmiGovernanceBoundary
    sprintNumber
    modulePath
    boundaryName
    boundaryLane
    canonicalSprint130InternalReadinessInput
    canonicalExternalGovernanceRows
    canonicalExternalGovernanceGates
    canonicalExternalGovernanceBoundaryFlags
    blocks-promotion
    "Sprint130 internal candidate readiness is true; publication, review, waiting, community, and CMI decision gates are absent; Clay/CMI promotion remains false."
    internalCandidateReadyIsTrue
    internalSubmissionReadyIsTrue
    publicationGatePresentIsFalse
    reviewGatePresentIsFalse
    waitingIntervalGatePresentIsFalse
    communityValidationGatePresentIsFalse
    cmiDecisionGatePresentIsFalse
    externalGovernanceCompleteIsFalse
    externalClayCmiPromotionIsFalse

canonicalReceipt : ExternalClayCmiGovernanceBoundary
canonicalReceipt = canonicalExternalClayCmiGovernanceBoundary

canonicalInternalCandidateReady :
  ExternalClayCmiGovernanceBoundary.candidateReady canonicalReceipt
    ≡ internalCandidateReadyIsTrue
canonicalInternalCandidateReady = refl

canonicalPublicationGateAbsent :
  ExternalGovernanceBoundaryFlags.publicationAbsent
    (ExternalClayCmiGovernanceBoundary.externalFlags canonicalReceipt)
    ≡ publicationGatePresentIsFalse
canonicalPublicationGateAbsent = refl

canonicalCmiDecisionGateAbsent :
  ExternalGovernanceBoundaryFlags.cmiDecisionAbsent
    (ExternalClayCmiGovernanceBoundary.externalFlags canonicalReceipt)
    ≡ cmiDecisionGatePresentIsFalse
canonicalCmiDecisionGateAbsent = refl

canonicalNoExternalClayCmiPromotion :
  ExternalGovernanceBoundaryFlags.promotionFalse
    (ExternalClayCmiGovernanceBoundary.externalFlags canonicalReceipt)
    ≡ externalClayCmiPromotionIsFalse
canonicalNoExternalClayCmiPromotion = refl
