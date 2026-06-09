module DASHI.Physics.Closure.YMReflectionPositivitySpatialTauBoundary where

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

data YMTauSpatialClause : Set where
  oppositeFaceBoundaryConventionConsumed : YMTauSpatialClause
  tauActsOnSpatialIndicesOnlyRecorded : YMTauSpatialClause
  temporalLinksUnaffectedRecorded : YMTauSpatialClause
  reflectionPositivityCompatibilityFeedsNextStepOnly : YMTauSpatialClause

canonicalYMTauSpatialClauses : List YMTauSpatialClause
canonicalYMTauSpatialClauses =
  oppositeFaceBoundaryConventionConsumed
  ∷ tauActsOnSpatialIndicesOnlyRecorded
  ∷ temporalLinksUnaffectedRecorded
  ∷ reflectionPositivityCompatibilityFeedsNextStepOnly
  ∷ []

ymTauSpatialClauseCount : Nat
ymTauSpatialClauseCount = listLength canonicalYMTauSpatialClauses

ymTauSpatialClauseCountIs4 : ymTauSpatialClauseCount ≡ 4
ymTauSpatialClauseCountIs4 = refl

data YMTauSpatialBlocker : Set where
  blocker-spatialOnlyTauProofOpen : YMTauSpatialBlocker
  blocker-temporalLinkSeparationProofOpen : YMTauSpatialBlocker
  blocker-reflectionPositivityStillOpen : YMTauSpatialBlocker
  blocker-ymClayPromotionForbidden : YMTauSpatialBlocker

canonicalYMTauSpatialBlockers : List YMTauSpatialBlocker
canonicalYMTauSpatialBlockers =
  blocker-spatialOnlyTauProofOpen
  ∷ blocker-temporalLinkSeparationProofOpen
  ∷ blocker-reflectionPositivityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivitySpatialTauRecorded : Bool
YMReflectionPositivitySpatialTauRecorded = true

YMReflectionPositivitySpatialTauProved : Bool
YMReflectionPositivitySpatialTauProved = false

record YMReflectionPositivitySpatialTauBoundary : Set where
  field
    clauses : List YMTauSpatialClause
    clausesCanonical : clauses ≡ canonicalYMTauSpatialClauses
    blockers : List YMTauSpatialBlocker
    blockersCanonical : blockers ≡ canonicalYMTauSpatialBlockers
    clauseCountIs4 : ymTauSpatialClauseCount ≡ 4
    theoremStillFalse : YMReflectionPositivitySpatialTauProved ≡ false

canonicalYMReflectionPositivitySpatialTauBoundary :
  YMReflectionPositivitySpatialTauBoundary
canonicalYMReflectionPositivitySpatialTauBoundary =
  record
    { clauses = canonicalYMTauSpatialClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMTauSpatialBlockers
    ; blockersCanonical = refl
    ; clauseCountIs4 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivitySpatialTauRecordedIsTrue :
  YMReflectionPositivitySpatialTauRecorded ≡ true
YMReflectionPositivitySpatialTauRecordedIsTrue = refl
