module DASHI.Physics.Closure.NSPaperSubmissionPacketBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSPaperSubmissionPacketClause : Set where
  reviewerPacketContainsCandidateCompleteSuitableWeakSolutionNarrative :
    NSPaperSubmissionPacketClause

  reviewerPacketContainsCandidateCompletePressureLocalEnergyAndCKNESSLRTIntakeNarrative :
    NSPaperSubmissionPacketClause

  reviewerNarrativeDependsOnCandidateCompleteA1A3Package :
    NSPaperSubmissionPacketClause

  constantsAppendixDependsOnCandidateCompleteA4Package :
    NSPaperSubmissionPacketClause

  contradictionEndgameDependsOnCandidateCompleteA5A9Package :
    NSPaperSubmissionPacketClause

  reviewerPacketDependsOnCandidateCompleteClassicalPDEAndA1A3A4A5A9Packages :
    NSPaperSubmissionPacketClause

  reviewerPacketMarksRemainingBurdenAsPromotionEvidenceAndAcceptance :
    NSPaperSubmissionPacketClause

  submissionStillFalseUntilCandidatePacketAcceptedInExactNormsAndConstants :
    NSPaperSubmissionPacketClause

  clayAndTerminalPromotionRemainFalseUntilReviewCloses :
    NSPaperSubmissionPacketClause

canonicalNSPaperSubmissionPacketClauses :
  List NSPaperSubmissionPacketClause
canonicalNSPaperSubmissionPacketClauses =
  reviewerPacketContainsCandidateCompleteSuitableWeakSolutionNarrative
  ∷ reviewerPacketContainsCandidateCompletePressureLocalEnergyAndCKNESSLRTIntakeNarrative
  ∷ reviewerNarrativeDependsOnCandidateCompleteA1A3Package
  ∷ constantsAppendixDependsOnCandidateCompleteA4Package
  ∷ contradictionEndgameDependsOnCandidateCompleteA5A9Package
  ∷ reviewerPacketDependsOnCandidateCompleteClassicalPDEAndA1A3A4A5A9Packages
  ∷ reviewerPacketMarksRemainingBurdenAsPromotionEvidenceAndAcceptance
  ∷ submissionStillFalseUntilCandidatePacketAcceptedInExactNormsAndConstants
  ∷ clayAndTerminalPromotionRemainFalseUntilReviewCloses
  ∷ []

nsPaperSubmissionPacketClauseCount : Nat
nsPaperSubmissionPacketClauseCount =
  listLength canonicalNSPaperSubmissionPacketClauses

nsPaperSubmissionPacketClauseCountIs9 :
  nsPaperSubmissionPacketClauseCount ≡ 9
nsPaperSubmissionPacketClauseCountIs9 = refl

data NSPaperSubmissionPacketBlocker : Set where
  candidateSuitableWeakSolutionNarrativeNeedsPromotionEvidenceInConsumedNorms :
    NSPaperSubmissionPacketBlocker

  candidatePressureLocalEnergyAndCKNESSLRTIntakeNeedAcceptanceInConsumedForm :
    NSPaperSubmissionPacketBlocker

  candidateA1BoundedMassRouteNeedsPromotionEvidence :
    NSPaperSubmissionPacketBlocker

  candidateA3ThresholdAndApproximateStationarityNeedsPromotionEvidence :
    NSPaperSubmissionPacketBlocker

  candidateA4OutputSupportCouplingNeedsAcceptedConstantsAndGeometry :
    NSPaperSubmissionPacketBlocker

  candidateA5A9ConsumerLadderNeedsPromotionEvidence :
    NSPaperSubmissionPacketBlocker

  exactConstantsAppendixAcceptanceStillOpen :
    NSPaperSubmissionPacketBlocker

  candidateStandardPDEPacketAcceptanceStillOpen :
    NSPaperSubmissionPacketBlocker

  externalReviewAcceptanceOfCandidateSelfContainedPacketStillOpen :
    NSPaperSubmissionPacketBlocker

  clayPromotionForbiddenUntilSubmissionAuthorityCloses :
    NSPaperSubmissionPacketBlocker

canonicalNSPaperSubmissionPacketBlockers :
  List NSPaperSubmissionPacketBlocker
canonicalNSPaperSubmissionPacketBlockers =
  candidateSuitableWeakSolutionNarrativeNeedsPromotionEvidenceInConsumedNorms
  ∷ candidatePressureLocalEnergyAndCKNESSLRTIntakeNeedAcceptanceInConsumedForm
  ∷ candidateA1BoundedMassRouteNeedsPromotionEvidence
  ∷ candidateA3ThresholdAndApproximateStationarityNeedsPromotionEvidence
  ∷ candidateA4OutputSupportCouplingNeedsAcceptedConstantsAndGeometry
  ∷ candidateA5A9ConsumerLadderNeedsPromotionEvidence
  ∷ exactConstantsAppendixAcceptanceStillOpen
  ∷ candidateStandardPDEPacketAcceptanceStillOpen
  ∷ externalReviewAcceptanceOfCandidateSelfContainedPacketStillOpen
  ∷ clayPromotionForbiddenUntilSubmissionAuthorityCloses
  ∷ []

nsPaperSubmissionPacketBlockerCount : Nat
nsPaperSubmissionPacketBlockerCount =
  listLength canonicalNSPaperSubmissionPacketBlockers

nsPaperSubmissionPacketBlockerCountIs10 :
  nsPaperSubmissionPacketBlockerCount ≡ 10
nsPaperSubmissionPacketBlockerCountIs10 = refl

nsPaperSubmissionPacketSummary : String
nsPaperSubmissionPacketSummary =
  "Reviewer packet grammar: the NS submission packet is a fail-closed candidate-complete classical PDE package consisting of suitable-weak-solution, pressure-reconstruction, local-energy, and classical CKN/ESS/LRT intake grammar, explicitly consuming theorem-shape grammar for A1-A9; what remains is promotion evidence and acceptance of that candidate self-contained packet in the exact consumed norms and constants, so submission and all promotion bits remain false until review authority closes."

NSPaperSubmissionPacketRecorded : Bool
NSPaperSubmissionPacketRecorded = true

NSPaperSubmissionUsesExistingA1ToA9Math : Bool
NSPaperSubmissionUsesExistingA1ToA9Math = true

NSPaperSubmissionStillFalse : Bool
NSPaperSubmissionStillFalse = false

NSPaperSubmissionAuthorityAudited : Bool
NSPaperSubmissionAuthorityAudited = false

NSPaperSubmissionSubmissionReady : Bool
NSPaperSubmissionSubmissionReady = false

NSClayPromotionFromPaperSubmissionPacket : Bool
NSClayPromotionFromPaperSubmissionPacket = false

NSTerminalPromotionFromPaperSubmissionPacket : Bool
NSTerminalPromotionFromPaperSubmissionPacket = false

record NSPaperSubmissionPacketBoundary : Set where
  field
    clauses : List NSPaperSubmissionPacketClause
    clausesCanonical :
      clauses ≡ canonicalNSPaperSubmissionPacketClauses
    blockers : List NSPaperSubmissionPacketBlocker
    blockersCanonical :
      blockers ≡ canonicalNSPaperSubmissionPacketBlockers
    clauseCountIs9 :
      nsPaperSubmissionPacketClauseCount ≡ 9
    blockerCountIs10 :
      nsPaperSubmissionPacketBlockerCount ≡ 10
    packetRecordedField :
      NSPaperSubmissionPacketRecorded ≡ true
    existingMathReuseField :
      NSPaperSubmissionUsesExistingA1ToA9Math ≡ true
    authorityAuditStillFalse :
      NSPaperSubmissionAuthorityAudited ≡ false
    submissionReadyStillFalse :
      NSPaperSubmissionSubmissionReady ≡ false
    submissionStillFalseField :
      NSPaperSubmissionStillFalse ≡ false
    clayPromotionStillFalseField :
      NSClayPromotionFromPaperSubmissionPacket ≡ false
    terminalPromotionStillFalseField :
      NSTerminalPromotionFromPaperSubmissionPacket ≡ false

canonicalNSPaperSubmissionPacketBoundary :
  NSPaperSubmissionPacketBoundary
canonicalNSPaperSubmissionPacketBoundary =
  record
    { clauses = canonicalNSPaperSubmissionPacketClauses
    ; clausesCanonical = refl
    ; blockers = canonicalNSPaperSubmissionPacketBlockers
    ; blockersCanonical = refl
    ; clauseCountIs9 = refl
    ; blockerCountIs10 = refl
    ; packetRecordedField = refl
    ; existingMathReuseField = refl
    ; authorityAuditStillFalse = refl
    ; submissionReadyStillFalse = refl
    ; submissionStillFalseField = refl
    ; clayPromotionStillFalseField = refl
    ; terminalPromotionStillFalseField = refl
    }

NSPaperSubmissionPacketRecordedIsTrue :
  NSPaperSubmissionPacketRecorded ≡ true
NSPaperSubmissionPacketRecordedIsTrue = refl

NSPaperSubmissionUsesExistingA1ToA9MathIsTrue :
  NSPaperSubmissionUsesExistingA1ToA9Math ≡ true
NSPaperSubmissionUsesExistingA1ToA9MathIsTrue = refl
