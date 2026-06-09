module DASHI.Physics.Closure.YMStandardLanguageWriteupReadinessBoundary where

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

data YMStandardLanguageWriteupClause : Set where
  localRouteStructureRecorded : YMStandardLanguageWriteupClause
  finiteBoundarySelfAdjointnessRouteRecorded : YMStandardLanguageWriteupClause
  hamiltonianDominationRouteRecorded : YMStandardLanguageWriteupClause
  spectralMarginRouteRecorded : YMStandardLanguageWriteupClause
  reflectionPositivityRouteRecorded : YMStandardLanguageWriteupClause
  osWightmanTransferRouteRecorded : YMStandardLanguageWriteupClause
  continuumMassGapAuthorityRouteRecorded : YMStandardLanguageWriteupClause
  remainingGapIsStandardLanguageWriteupPackaging : YMStandardLanguageWriteupClause

canonicalYMStandardLanguageWriteupClauses :
  List YMStandardLanguageWriteupClause
canonicalYMStandardLanguageWriteupClauses =
  localRouteStructureRecorded
  ∷ finiteBoundarySelfAdjointnessRouteRecorded
  ∷ hamiltonianDominationRouteRecorded
  ∷ spectralMarginRouteRecorded
  ∷ reflectionPositivityRouteRecorded
  ∷ osWightmanTransferRouteRecorded
  ∷ continuumMassGapAuthorityRouteRecorded
  ∷ remainingGapIsStandardLanguageWriteupPackaging
  ∷ []

ymStandardLanguageWriteupClauseCount : Nat
ymStandardLanguageWriteupClauseCount =
  listLength canonicalYMStandardLanguageWriteupClauses

ymStandardLanguageWriteupClauseCountIs8 :
  ymStandardLanguageWriteupClauseCount ≡ 8
ymStandardLanguageWriteupClauseCountIs8 = refl

data YMStandardLanguageWriteupBlocker : Set where
  blocker-standardGaugeLanguageWriteupStillOpen :
    YMStandardLanguageWriteupBlocker
  blocker-authorityPackagingStillOpen :
    YMStandardLanguageWriteupBlocker
  blocker-externalReviewStillOpen :
    YMStandardLanguageWriteupBlocker
  blocker-ymClayPromotionForbidden :
    YMStandardLanguageWriteupBlocker
  blocker-terminalPromotionForbidden :
    YMStandardLanguageWriteupBlocker

canonicalYMStandardLanguageWriteupBlockers :
  List YMStandardLanguageWriteupBlocker
canonicalYMStandardLanguageWriteupBlockers =
  blocker-standardGaugeLanguageWriteupStillOpen
  ∷ blocker-authorityPackagingStillOpen
  ∷ blocker-externalReviewStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ blocker-terminalPromotionForbidden
  ∷ []

ymStandardLanguageWriteupBlockerCount : Nat
ymStandardLanguageWriteupBlockerCount =
  listLength canonicalYMStandardLanguageWriteupBlockers

ymStandardLanguageWriteupBlockerCountIs5 :
  ymStandardLanguageWriteupBlockerCount ≡ 5
ymStandardLanguageWriteupBlockerCountIs5 = refl

YMStandardLanguageWriteupReadinessRecorded : Bool
YMStandardLanguageWriteupReadinessRecorded = true

YMStandardLanguageWriteupReady : Bool
YMStandardLanguageWriteupReady = false

YMStandardLanguageWriteupPublished : Bool
YMStandardLanguageWriteupPublished = false

YMClayPromotionFromStandardLanguageWriteup : Bool
YMClayPromotionFromStandardLanguageWriteup = false

record YMStandardLanguageWriteupReadinessBoundary : Set where
  field
    clauses : List YMStandardLanguageWriteupClause
    clausesCanonical : clauses ≡ canonicalYMStandardLanguageWriteupClauses
    blockers : List YMStandardLanguageWriteupBlocker
    blockersCanonical : blockers ≡ canonicalYMStandardLanguageWriteupBlockers
    clauseCountIs8 : ymStandardLanguageWriteupClauseCount ≡ 8
    blockerCountIs5 : ymStandardLanguageWriteupBlockerCount ≡ 5
    writeupStillFalse : YMStandardLanguageWriteupReady ≡ false
    publicationStillFalse : YMStandardLanguageWriteupPublished ≡ false
    clayPromotionStillFalse :
      YMClayPromotionFromStandardLanguageWriteup ≡ false

canonicalYMStandardLanguageWriteupReadinessBoundary :
  YMStandardLanguageWriteupReadinessBoundary
canonicalYMStandardLanguageWriteupReadinessBoundary =
  record
    { clauses = canonicalYMStandardLanguageWriteupClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMStandardLanguageWriteupBlockers
    ; blockersCanonical = refl
    ; clauseCountIs8 = refl
    ; blockerCountIs5 = refl
    ; writeupStillFalse = refl
    ; publicationStillFalse = refl
    ; clayPromotionStillFalse = refl
    }

YMStandardLanguageWriteupReadinessRecordedIsTrue :
  YMStandardLanguageWriteupReadinessRecorded ≡ true
YMStandardLanguageWriteupReadinessRecordedIsTrue = refl
