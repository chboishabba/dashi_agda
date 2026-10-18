module DASHI.Wikimedia.MaboLeanSlrP7dBidiBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawImmutableLegalResearchWorldExact as World
import DASHI.Law.SensibLawMultiResidualProofFrontierExact as Frontier
import DASHI.Law.SensibLawResearchCompoundingLoopExact as Compound
import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact as Observation
import DASHI.Wikimedia.LeanWikidataVerificationExact as Verification
import DASHI.Wikimedia.SlrLeanChallengeBidiExact as Challenge
import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionStepExact as Step

------------------------------------------------------------------------
-- SAME-OBJECT / RELATION ATTACHMENT
------------------------------------------------------------------------

record LeanP7AttachmentReceipt : Set where
  constructor leanP7AttachmentReceipt
  field
    attachmentReference : String
    verificationReceipt : Verification.LeanVerificationReceipt
    candidateObjectReference : String
    candidateRelationReference : String
    candidateSourceRevisionReference : String
    candidateContentDigestReference : String
    objectAlignment : Verification.ObjectAlignmentStatus
    relationAlignment : Verification.RelationAlignmentStatus
    attachmentCreatesExpansionCandidate : Bool
    attachmentCreatesSemanticAuthority : Bool
    attachmentCreatesClaimTruth : Bool

open LeanP7AttachmentReceipt public

------------------------------------------------------------------------
-- FRESHNESS REOPENING
------------------------------------------------------------------------

record FreshnessReopeningReceipt : Set where
  constructor freshnessReopeningReceipt
  field
    reopeningReference : String
    priorVerificationReceipt : Verification.LeanVerificationReceipt
    currentSourceRevisionReference : String
    currentApplicabilityReopened : Bool
    historicalKernelReceiptNegated : Bool
    staleRevisionCreatesWorldNegation : Bool

open FreshnessReopeningReceipt public

------------------------------------------------------------------------
-- OBSERVED WORLD DELTA
------------------------------------------------------------------------

data LeanVerificationUse : Set where
  noLeanVerification : LeanVerificationUse
  withLeanVerification : Verification.LeanVerificationReceipt → LeanVerificationUse

record ObservedWorldDelta
    (priorWorld posteriorWorld : World.LegalResearchWorldSnapshot) : Set₁ where
  constructor observedWorldDelta
  field
    deltaReference : String
    triggeringResidualReference : String
    selectedCandidateReference : String
    reviewedAdmissionReference : String
    observation : Observation.WorldObservation
    leanVerification : LeanVerificationUse
    challengeResolutionReferences : List String
    predictedResidualContraction : Nat
    observedResidualContraction : Nat
    contractedResidualReferences : List String
    unchangedResidualReferences : List String
    newlyExposedResidualReferences : List String
    reopenedResidualReferences : List String
    newReasoningDeltaReferences : List String
    newIdentityAliasReferences : List String
    newLineageReferences : List String
    newPnfDeltaReferences : List String
    appendOnlyExtension : World.AppendOnlyResearchExtension priorWorld posteriorWorld
    deltaCreatesClaimTruth : Bool
    deltaCreatesLegalAuthority : Bool

open ObservedWorldDelta public

record P7dBidiIteration : Set₂ where
  constructor p7dBidiIteration
  field
    priorFrontier : Frontier.ProofFrontier
    priorWorld : World.LegalResearchWorldSnapshot
    selectedCandidateReference : String
    reviewedAdmissionReference : String
    observation : Observation.WorldObservation
    verificationUse : LeanVerificationUse
    challengeResolutionReferences : List String
    posteriorWorld : World.LegalResearchWorldSnapshot
    delta : ObservedWorldDelta priorWorld posteriorWorld
    posteriorFrontier : Frontier.ProofFrontier
    nextFrontierCandidates : List Frontier.FrontierMoveCandidate
    compoundingOwnerReference : String

open P7dBidiIteration public

------------------------------------------------------------------------
-- GOLDEN BOUNDARY
------------------------------------------------------------------------

record P7dBidiBoundary : Set where
  constructor p7dBidiBoundary
  field
    agdaOwnsGoldenSemantics : Bool
    slrOwnsProductionExecution : Bool
    jmdLeanOwnsExecutableVerification : Bool
    predictedContractionEqualsObservedByDefinition : Bool
    kernelPassedCreatesAdmission : Bool
    admissionCreatesClaimTruth : Bool
    representationIdentityEqualsWorldIdentity : Bool
    sameWorldObjectImpliesSameRelation : Bool
    derivationalNoveltyCountsAsExternalWorldNovelty : Bool
    staleRevisionNegatesHistoricalKernelReceipt : Bool
    worldDeltaRequiresLeanVerification : Bool

open P7dBidiBoundary public

canonicalP7dBidiBoundary : P7dBidiBoundary
canonicalP7dBidiBoundary =
  p7dBidiBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false

data PredictedContractionEqualsObservedContraction : Set where
data KernelPassedEqualsReviewedAdmission : Set where
data ReviewedAdmissionEqualsClaimTruth : Set where
data RepresentationIdentityEqualsWorldObjectIdentity : Set where
data SameWorldObjectDeterminesSameRelation : Set where
data DerivationalNoveltyEqualsExternalWorldNovelty : Set where
data StaleRevisionNegatesHistoricalKernelTheorem : Set where
data WorldDeltaFactorsThroughLeanVerification : Set where

predictedDoesNotEqualObservedByDefinition :
  PredictedContractionEqualsObservedContraction → ⊥
predictedDoesNotEqualObservedByDefinition ()

kernelPassedDoesNotCreateAdmission : KernelPassedEqualsReviewedAdmission → ⊥
kernelPassedDoesNotCreateAdmission ()

reviewedAdmissionDoesNotCreateClaimTruth : ReviewedAdmissionEqualsClaimTruth → ⊥
reviewedAdmissionDoesNotCreateClaimTruth ()

representationIdentityDoesNotEqualWorldIdentity :
  RepresentationIdentityEqualsWorldObjectIdentity → ⊥
representationIdentityDoesNotEqualWorldIdentity ()

sameWorldObjectDoesNotDetermineSameRelation :
  SameWorldObjectDeterminesSameRelation → ⊥
sameWorldObjectDoesNotDetermineSameRelation ()

derivationalNoveltyDoesNotEqualExternalWorldNovelty :
  DerivationalNoveltyEqualsExternalWorldNovelty → ⊥
derivationalNoveltyDoesNotEqualExternalWorldNovelty ()

staleRevisionDoesNotNegateHistoricalKernelTheorem :
  StaleRevisionNegatesHistoricalKernelTheorem → ⊥
staleRevisionDoesNotNegateHistoricalKernelTheorem ()

worldDeltaNeedNotFactorThroughLeanVerification :
  WorldDeltaFactorsThroughLeanVerification → ⊥
worldDeltaNeedNotFactorThroughLeanVerification ()

------------------------------------------------------------------------
-- REUSE PINS
------------------------------------------------------------------------

compoundingLoopOwner : String
compoundingLoopOwner = "DASHI.Law.SensibLawResearchCompoundingLoopExact"

worldExpansionStepOwner : String
worldExpansionStepOwner = "DASHI.Wikimedia.MaboResidualDrivenWorldExpansionStepExact"

_ : Set₂
_ = Compound.ResearchCompoundingIteration

_ : Set
_ = Step.ReviewedExpansionStepBoundary

_ : Set
_ = Challenge.SLRLeanChallenge
