module DASHI.Physics.Closure.NSStandardPDEWriteupAssemblyBoundary where

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

data NSStandardPDEWriteupAssemblyClause : Set where
  suitableWeakSolutionLanguageAssemblyRecorded :
    NSStandardPDEWriteupAssemblyClause

  pressureReconstructionAssemblyRecorded :
    NSStandardPDEWriteupAssemblyClause

  localEnstrophyCriterionAssemblyRecorded :
    NSStandardPDEWriteupAssemblyClause

  constantCompatibilityWriteupAssemblyRecorded :
    NSStandardPDEWriteupAssemblyClause

  externalReviewBlockersRecorded :
    NSStandardPDEWriteupAssemblyClause

  promotionStaysFalseUntilAuthorityCloses :
    NSStandardPDEWriteupAssemblyClause

canonicalNSStandardPDEWriteupAssemblyClauses :
  List NSStandardPDEWriteupAssemblyClause
canonicalNSStandardPDEWriteupAssemblyClauses =
  suitableWeakSolutionLanguageAssemblyRecorded
  ∷ pressureReconstructionAssemblyRecorded
  ∷ localEnstrophyCriterionAssemblyRecorded
  ∷ constantCompatibilityWriteupAssemblyRecorded
  ∷ externalReviewBlockersRecorded
  ∷ promotionStaysFalseUntilAuthorityCloses
  ∷ []

nsStandardPDEWriteupAssemblyClauseCount : Nat
nsStandardPDEWriteupAssemblyClauseCount =
  listLength canonicalNSStandardPDEWriteupAssemblyClauses

nsStandardPDEWriteupAssemblyClauseCountIs6 :
  nsStandardPDEWriteupAssemblyClauseCount ≡ 6
nsStandardPDEWriteupAssemblyClauseCountIs6 = refl

data NSStandardPDEWriteupAssemblyBlocker : Set where
  suitableWeakSolutionPaperAssemblyStillOpen :
    NSStandardPDEWriteupAssemblyBlocker

  pressureReconstructionWriteupStillOpen :
    NSStandardPDEWriteupAssemblyBlocker

  localEnstrophyCriterionWriteupStillOpen :
    NSStandardPDEWriteupAssemblyBlocker

  constantCompatibilityNarrativeStillOpen :
    NSStandardPDEWriteupAssemblyBlocker

  externalReviewAndAcceptanceStillOpen :
    NSStandardPDEWriteupAssemblyBlocker

  clayPromotionForbiddenUntilPaperAuthorityCloses :
    NSStandardPDEWriteupAssemblyBlocker

canonicalNSStandardPDEWriteupAssemblyBlockers :
  List NSStandardPDEWriteupAssemblyBlocker
canonicalNSStandardPDEWriteupAssemblyBlockers =
  suitableWeakSolutionPaperAssemblyStillOpen
  ∷ pressureReconstructionWriteupStillOpen
  ∷ localEnstrophyCriterionWriteupStillOpen
  ∷ constantCompatibilityNarrativeStillOpen
  ∷ externalReviewAndAcceptanceStillOpen
  ∷ clayPromotionForbiddenUntilPaperAuthorityCloses
  ∷ []

nsStandardPDEWriteupAssemblyBlockerCount : Nat
nsStandardPDEWriteupAssemblyBlockerCount =
  listLength canonicalNSStandardPDEWriteupAssemblyBlockers

nsStandardPDEWriteupAssemblyBlockerCountIs6 :
  nsStandardPDEWriteupAssemblyBlockerCount ≡ 6
nsStandardPDEWriteupAssemblyBlockerCountIs6 = refl

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
    clauseCountIs6 :
      nsStandardPDEWriteupAssemblyClauseCount ≡ 6
    blockerCountIs6 :
      nsStandardPDEWriteupAssemblyBlockerCount ≡ 6
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
    ; clauseCountIs6 = refl
    ; blockerCountIs6 = refl
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
