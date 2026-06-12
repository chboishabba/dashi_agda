module DASHI.Physics.Closure.NSStandardPDEWriteupAssemblyBoundary where

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

data NSStandardPDEWriteupAssemblyClause : Set where
  candidateCompleteSuitableWeakSolutionGrammarRecordedInReviewerFacingLanguage :
    NSStandardPDEWriteupAssemblyClause

  candidateCompleteLocalPressureGrammarRecordedForPacket :
    NSStandardPDEWriteupAssemblyClause

  candidateCompleteLocalEnergyAndEnstrophyGrammarRecorded :
    NSStandardPDEWriteupAssemblyClause

  classicalPDEWriteupExplicitlyConsumesCandidateCompleteA1A3AndA4Grammar :
    NSStandardPDEWriteupAssemblyClause

  classicalPDEWriteupExplicitlyHandsOffToCandidateCompleteA5A9Grammar :
    NSStandardPDEWriteupAssemblyClause

  classicalCKNESSLRTIntakeRecordedAsCandidateCompleteReviewerSocket :
    NSStandardPDEWriteupAssemblyClause

  remainingBurdenIsPromotionEvidenceAndAcceptanceNotMissingGrammar :
    NSStandardPDEWriteupAssemblyClause

canonicalNSStandardPDEWriteupAssemblyClauses :
  List NSStandardPDEWriteupAssemblyClause
canonicalNSStandardPDEWriteupAssemblyClauses =
  candidateCompleteSuitableWeakSolutionGrammarRecordedInReviewerFacingLanguage
  ∷ candidateCompleteLocalPressureGrammarRecordedForPacket
  ∷ candidateCompleteLocalEnergyAndEnstrophyGrammarRecorded
  ∷ classicalPDEWriteupExplicitlyConsumesCandidateCompleteA1A3AndA4Grammar
  ∷ classicalPDEWriteupExplicitlyHandsOffToCandidateCompleteA5A9Grammar
  ∷ classicalCKNESSLRTIntakeRecordedAsCandidateCompleteReviewerSocket
  ∷ remainingBurdenIsPromotionEvidenceAndAcceptanceNotMissingGrammar
  ∷ []

nsStandardPDEWriteupAssemblyClauseCount : Nat
nsStandardPDEWriteupAssemblyClauseCount =
  listLength canonicalNSStandardPDEWriteupAssemblyClauses

nsStandardPDEWriteupAssemblyClauseCountIs7 :
  nsStandardPDEWriteupAssemblyClauseCount ≡ 7
nsStandardPDEWriteupAssemblyClauseCountIs7 = refl

data NSStandardPDEWriteupAssemblyBlocker : Set where
  candidateSuitableWeakSolutionPackageNeedsPromotionEvidenceInConsumedNorms :
    NSStandardPDEWriteupAssemblyBlocker

  candidateLocalPressurePackageNeedsPromotionEvidenceInConsumedNormalization :
    NSStandardPDEWriteupAssemblyBlocker

  candidateLocalEnergyAndEnstrophyPackageNeedsPromotionEvidenceForAcceptance :
    NSStandardPDEWriteupAssemblyBlocker

  candidateA1A3PackageNeedsAcceptedRouteNormsAndConstants :
    NSStandardPDEWriteupAssemblyBlocker

  candidateA4PackageNeedsAcceptedConstantsAndGeometryCompatibility :
    NSStandardPDEWriteupAssemblyBlocker

  candidateA5A9PackageNeedsAcceptedConsumerNormsAndConstants :
    NSStandardPDEWriteupAssemblyBlocker

  classicalCKNESSLRTIntakeNeedsReviewerAcceptanceAsConsumedAuthority :
    NSStandardPDEWriteupAssemblyBlocker

  candidateSelfContainedPacketAcceptanceStillOpen :
    NSStandardPDEWriteupAssemblyBlocker

  clayPromotionForbiddenUntilPaperAuthorityCloses :
    NSStandardPDEWriteupAssemblyBlocker

canonicalNSStandardPDEWriteupAssemblyBlockers :
  List NSStandardPDEWriteupAssemblyBlocker
canonicalNSStandardPDEWriteupAssemblyBlockers =
  candidateSuitableWeakSolutionPackageNeedsPromotionEvidenceInConsumedNorms
  ∷ candidateLocalPressurePackageNeedsPromotionEvidenceInConsumedNormalization
  ∷ candidateLocalEnergyAndEnstrophyPackageNeedsPromotionEvidenceForAcceptance
  ∷ candidateA1A3PackageNeedsAcceptedRouteNormsAndConstants
  ∷ candidateA4PackageNeedsAcceptedConstantsAndGeometryCompatibility
  ∷ candidateA5A9PackageNeedsAcceptedConsumerNormsAndConstants
  ∷ classicalCKNESSLRTIntakeNeedsReviewerAcceptanceAsConsumedAuthority
  ∷ candidateSelfContainedPacketAcceptanceStillOpen
  ∷ clayPromotionForbiddenUntilPaperAuthorityCloses
  ∷ []

nsStandardPDEWriteupAssemblyBlockerCount : Nat
nsStandardPDEWriteupAssemblyBlockerCount =
  listLength canonicalNSStandardPDEWriteupAssemblyBlockers

nsStandardPDEWriteupAssemblyBlockerCountIs9 :
  nsStandardPDEWriteupAssemblyBlockerCount ≡ 9
nsStandardPDEWriteupAssemblyBlockerCountIs9 = refl

nsStandardPDEWriteupAssemblySummary : String
nsStandardPDEWriteupAssemblySummary =
  "Classical NS packet grammar: the reviewer-facing PDE writeup now presents a candidate-complete self-contained package consisting of suitable-weak-solution, local-pressure, and local-energy/enstrophy grammar, explicitly consuming theorem-shape grammar for A1-A9 together with classical CKN/ESS/LRT intake; the remaining burden is promotion evidence and reviewer acceptance in the exact consumed norms and constants, so completion and Clay promotion stay fail-closed."

NSStandardPDEWriteupAssemblyRecorded : Bool
NSStandardPDEWriteupAssemblyRecorded = true

NSStandardPDEAssemblyUsesExistingA1ToA9Math : Bool
NSStandardPDEAssemblyUsesExistingA1ToA9Math = true

NSStandardPDEWriteupCompleted : Bool
NSStandardPDEWriteupCompleted = false

NSClayPromotionFromStandardPDEAssembly : Bool
NSClayPromotionFromStandardPDEAssembly = false

record NSStandardPDEWriteupAssemblyBoundary : Set where
  field
    clauses : List NSStandardPDEWriteupAssemblyClause
    clausesCanonical :
      clauses ≡ canonicalNSStandardPDEWriteupAssemblyClauses
    blockers : List NSStandardPDEWriteupAssemblyBlocker
    blockersCanonical :
      blockers ≡ canonicalNSStandardPDEWriteupAssemblyBlockers
    clauseCountIs7 :
      nsStandardPDEWriteupAssemblyClauseCount ≡ 7
    blockerCountIs9 :
      nsStandardPDEWriteupAssemblyBlockerCount ≡ 9
    assemblyRecordedField :
      NSStandardPDEWriteupAssemblyRecorded ≡ true
    existingMathReuseField :
      NSStandardPDEAssemblyUsesExistingA1ToA9Math ≡ true
    completionStillFalse :
      NSStandardPDEWriteupCompleted ≡ false
    clayPromotionStillFalse :
      NSClayPromotionFromStandardPDEAssembly ≡ false

canonicalNSStandardPDEWriteupAssemblyBoundary :
  NSStandardPDEWriteupAssemblyBoundary
canonicalNSStandardPDEWriteupAssemblyBoundary =
  record
    { clauses = canonicalNSStandardPDEWriteupAssemblyClauses
    ; clausesCanonical = refl
    ; blockers = canonicalNSStandardPDEWriteupAssemblyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; blockerCountIs9 = refl
    ; assemblyRecordedField = refl
    ; existingMathReuseField = refl
    ; completionStillFalse = refl
    ; clayPromotionStillFalse = refl
    }

NSStandardPDEWriteupAssemblyRecordedIsTrue :
  NSStandardPDEWriteupAssemblyRecorded ≡ true
NSStandardPDEWriteupAssemblyRecordedIsTrue = refl

NSStandardPDEAssemblyUsesExistingA1ToA9MathIsTrue :
  NSStandardPDEAssemblyUsesExistingA1ToA9Math ≡ true
NSStandardPDEAssemblyUsesExistingA1ToA9MathIsTrue = refl
