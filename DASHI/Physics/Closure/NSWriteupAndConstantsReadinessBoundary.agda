module DASHI.Physics.Closure.NSWriteupAndConstantsReadinessBoundary where

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

data NSWriteupAndConstantsReadinessClause : Set where
  a4ToA9LocalRouteStructureRecorded :
    NSWriteupAndConstantsReadinessClause

  localReceiptLadderPresent :
    NSWriteupAndConstantsReadinessClause

  localHarnessCoveragePresent :
    NSWriteupAndConstantsReadinessClause

  remainingGapIsWriteupAndAuthorityShaped :
    NSWriteupAndConstantsReadinessClause

  missingGapIsNotLocalRouteStructure :
    NSWriteupAndConstantsReadinessClause

  noClayPromotionWithoutExternalReview :
    NSWriteupAndConstantsReadinessClause

canonicalNSWriteupAndConstantsReadinessClauses :
  List NSWriteupAndConstantsReadinessClause
canonicalNSWriteupAndConstantsReadinessClauses =
  a4ToA9LocalRouteStructureRecorded
  ∷ localReceiptLadderPresent
  ∷ localHarnessCoveragePresent
  ∷ remainingGapIsWriteupAndAuthorityShaped
  ∷ missingGapIsNotLocalRouteStructure
  ∷ noClayPromotionWithoutExternalReview
  ∷ []

nsWriteupAndConstantsReadinessClauseCount : Nat
nsWriteupAndConstantsReadinessClauseCount =
  listLength canonicalNSWriteupAndConstantsReadinessClauses

nsWriteupAndConstantsReadinessClauseCountIs6 :
  nsWriteupAndConstantsReadinessClauseCount ≡ 6
nsWriteupAndConstantsReadinessClauseCountIs6 = refl

data NSWriteupAndConstantsReadinessBlocker : Set where
  writeupAssemblyStillOpen :
    NSWriteupAndConstantsReadinessBlocker

  constantsCompatibilityExtractionStillOpen :
    NSWriteupAndConstantsReadinessBlocker

  standardPDETranslationStillOpen :
    NSWriteupAndConstantsReadinessBlocker

  externalReviewStillOpen :
    NSWriteupAndConstantsReadinessBlocker

  clayPromotionForbiddenUntilAuthorityCloses :
    NSWriteupAndConstantsReadinessBlocker

canonicalNSWriteupAndConstantsReadinessBlockers :
  List NSWriteupAndConstantsReadinessBlocker
canonicalNSWriteupAndConstantsReadinessBlockers =
  writeupAssemblyStillOpen
  ∷ constantsCompatibilityExtractionStillOpen
  ∷ standardPDETranslationStillOpen
  ∷ externalReviewStillOpen
  ∷ clayPromotionForbiddenUntilAuthorityCloses
  ∷ []

nsWriteupAndConstantsReadinessBlockerCount : Nat
nsWriteupAndConstantsReadinessBlockerCount =
  listLength canonicalNSWriteupAndConstantsReadinessBlockers

nsWriteupAndConstantsReadinessBlockerCountIs5 :
  nsWriteupAndConstantsReadinessBlockerCount ≡ 5
nsWriteupAndConstantsReadinessBlockerCountIs5 = refl

NSWriteupAndConstantsReadinessRecorded : Bool
NSWriteupAndConstantsReadinessRecorded = true

NSLocalRouteStructureReady : Bool
NSLocalRouteStructureReady = true

NSWriteupAndConstantsCompleted : Bool
NSWriteupAndConstantsCompleted = false

NSClayPromotionFromWriteupAndConstantsReady : Bool
NSClayPromotionFromWriteupAndConstantsReady = false

record NSWriteupAndConstantsReadinessBoundary : Set where
  field
    clauses : List NSWriteupAndConstantsReadinessClause
    clausesCanonical :
      clauses ≡ canonicalNSWriteupAndConstantsReadinessClauses
    blockers : List NSWriteupAndConstantsReadinessBlocker
    blockersCanonical :
      blockers ≡ canonicalNSWriteupAndConstantsReadinessBlockers
    clauseCountIs6 :
      nsWriteupAndConstantsReadinessClauseCount ≡ 6
    blockerCountIs5 :
      nsWriteupAndConstantsReadinessBlockerCount ≡ 5
    readinessRecordedField :
      NSWriteupAndConstantsReadinessRecorded ≡ true
    localRouteStructureReadyField :
      NSLocalRouteStructureReady ≡ true
    completionStillFalse :
      NSWriteupAndConstantsCompleted ≡ false
    clayPromotionStillFalse :
      NSClayPromotionFromWriteupAndConstantsReady ≡ false

canonicalNSWriteupAndConstantsReadinessBoundary :
  NSWriteupAndConstantsReadinessBoundary
canonicalNSWriteupAndConstantsReadinessBoundary =
  record
    { clauses = canonicalNSWriteupAndConstantsReadinessClauses
    ; clausesCanonical = refl
    ; blockers = canonicalNSWriteupAndConstantsReadinessBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; blockerCountIs5 = refl
    ; readinessRecordedField = refl
    ; localRouteStructureReadyField = refl
    ; completionStillFalse = refl
    ; clayPromotionStillFalse = refl
    }

NSWriteupAndConstantsReadinessRecordedIsTrue :
  NSWriteupAndConstantsReadinessRecorded ≡ true
NSWriteupAndConstantsReadinessRecordedIsTrue = refl

NSLocalRouteStructureReadyIsTrue :
  NSLocalRouteStructureReady ≡ true
NSLocalRouteStructureReadyIsTrue = refl
