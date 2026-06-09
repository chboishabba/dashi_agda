module DASHI.Physics.Closure.NSPaperSubmissionPacketBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSPaperSubmissionPacketClause : Set where
  pdeLanguageNarrativeAssembled :
    NSPaperSubmissionPacketClause

  constantsAppendixPacketAssembled :
    NSPaperSubmissionPacketClause

  solutionClassAndCriterionPacketAssembled :
    NSPaperSubmissionPacketClause

  reviewerFacingAuthorityBlockersRecorded :
    NSPaperSubmissionPacketClause

  submissionStillFalseUntilAuthorityCloses :
    NSPaperSubmissionPacketClause

  clayPromotionStillFalseUntilSubmissionCloses :
    NSPaperSubmissionPacketClause

  terminalPromotionStillFalseUntilReviewCloses :
    NSPaperSubmissionPacketClause

canonicalNSPaperSubmissionPacketClauses :
  List NSPaperSubmissionPacketClause
canonicalNSPaperSubmissionPacketClauses =
  pdeLanguageNarrativeAssembled
  ∷ constantsAppendixPacketAssembled
  ∷ solutionClassAndCriterionPacketAssembled
  ∷ reviewerFacingAuthorityBlockersRecorded
  ∷ submissionStillFalseUntilAuthorityCloses
  ∷ clayPromotionStillFalseUntilSubmissionCloses
  ∷ terminalPromotionStillFalseUntilReviewCloses
  ∷ []

nsPaperSubmissionPacketClauseCount : Nat
nsPaperSubmissionPacketClauseCount =
  listLength canonicalNSPaperSubmissionPacketClauses

nsPaperSubmissionPacketClauseCountIs7 :
  nsPaperSubmissionPacketClauseCount ≡ 7
nsPaperSubmissionPacketClauseCountIs7 = refl

data NSPaperSubmissionPacketBlocker : Set where
  pdeNarrativePolishStillOpen :
    NSPaperSubmissionPacketBlocker

  constantsAppendixExtractionStillOpen :
    NSPaperSubmissionPacketBlocker

  solutionClassNarrativeAlignmentStillOpen :
    NSPaperSubmissionPacketBlocker

  reviewerResponsePacketStillOpen :
    NSPaperSubmissionPacketBlocker

  externalReviewAndAcceptanceStillOpen :
    NSPaperSubmissionPacketBlocker

  clayPromotionForbiddenUntilSubmissionAuthorityCloses :
    NSPaperSubmissionPacketBlocker

  terminalPromotionForbiddenUntilReviewAuthorityCloses :
    NSPaperSubmissionPacketBlocker

canonicalNSPaperSubmissionPacketBlockers :
  List NSPaperSubmissionPacketBlocker
canonicalNSPaperSubmissionPacketBlockers =
  pdeNarrativePolishStillOpen
  ∷ constantsAppendixExtractionStillOpen
  ∷ solutionClassNarrativeAlignmentStillOpen
  ∷ reviewerResponsePacketStillOpen
  ∷ externalReviewAndAcceptanceStillOpen
  ∷ clayPromotionForbiddenUntilSubmissionAuthorityCloses
  ∷ terminalPromotionForbiddenUntilReviewAuthorityCloses
  ∷ []

nsPaperSubmissionPacketBlockerCount : Nat
nsPaperSubmissionPacketBlockerCount =
  listLength canonicalNSPaperSubmissionPacketBlockers

nsPaperSubmissionPacketBlockerCountIs7 :
  nsPaperSubmissionPacketBlockerCount ≡ 7
nsPaperSubmissionPacketBlockerCountIs7 = refl

NSPaperSubmissionPacketRecorded : Bool
NSPaperSubmissionPacketRecorded = true

NSPaperSubmissionUsesExistingA1ToA9Math : Bool
NSPaperSubmissionUsesExistingA1ToA9Math = true

NSPaperSubmissionStillFalse : Bool
NSPaperSubmissionStillFalse = false

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
    clauseCountIs7 :
      nsPaperSubmissionPacketClauseCount ≡ 7
    blockerCountIs7 :
      nsPaperSubmissionPacketBlockerCount ≡ 7
    packetRecordedField :
      NSPaperSubmissionPacketRecorded ≡ true
    existingMathReuseField :
      NSPaperSubmissionUsesExistingA1ToA9Math ≡ true
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
    ; clauseCountIs7 = refl
    ; blockerCountIs7 = refl
    ; packetRecordedField = refl
    ; existingMathReuseField = refl
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
