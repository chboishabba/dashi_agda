module DASHI.Physics.Closure.YMFinalAuthorityPackagingCompositeLightweightBoundary where

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

data YMFinalAuthorityClause : Set where
  finalAssemblyBoundaryImported : YMFinalAuthorityClause
  clayAuthorityBlockerImported : YMFinalAuthorityClause
  externalAcceptanceBoundaryImported : YMFinalAuthorityClause
  finalAuthorityPackagingRecorded : YMFinalAuthorityClause
  clayPromotionStillBlocked : YMFinalAuthorityClause

canonicalYMFinalAuthorityClauses : List YMFinalAuthorityClause
canonicalYMFinalAuthorityClauses =
  finalAssemblyBoundaryImported
  ∷ clayAuthorityBlockerImported
  ∷ externalAcceptanceBoundaryImported
  ∷ finalAuthorityPackagingRecorded
  ∷ clayPromotionStillBlocked
  ∷ []

ymFinalAuthorityClauseCount : Nat
ymFinalAuthorityClauseCount = listLength canonicalYMFinalAuthorityClauses

ymFinalAuthorityClauseCountIs5 : ymFinalAuthorityClauseCount ≡ 5
ymFinalAuthorityClauseCountIs5 = refl

data YMFinalAuthorityBlocker : Set where
  blocker-finalAssemblyAuthorityStillOpen : YMFinalAuthorityBlocker
  blocker-externalAcceptanceStillOpen : YMFinalAuthorityBlocker
  blocker-clayAuthorityStillOpen : YMFinalAuthorityBlocker
  blocker-ymClayPromotionForbidden : YMFinalAuthorityBlocker

canonicalYMFinalAuthorityBlockers : List YMFinalAuthorityBlocker
canonicalYMFinalAuthorityBlockers =
  blocker-finalAssemblyAuthorityStillOpen
  ∷ blocker-externalAcceptanceStillOpen
  ∷ blocker-clayAuthorityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMFinalAuthorityPackagingCompositeRecorded : Bool
YMFinalAuthorityPackagingCompositeRecorded = true

YMFinalAuthorityPackagingCompositeProved : Bool
YMFinalAuthorityPackagingCompositeProved = false

record YMFinalAuthorityPackagingCompositeLightweightBoundary : Set where
  field
    clauses : List YMFinalAuthorityClause
    clausesCanonical : clauses ≡ canonicalYMFinalAuthorityClauses
    blockers : List YMFinalAuthorityBlocker
    blockersCanonical : blockers ≡ canonicalYMFinalAuthorityBlockers
    clauseCountIs5 : ymFinalAuthorityClauseCount ≡ 5
    provedStillFalse : YMFinalAuthorityPackagingCompositeProved ≡ false

canonicalYMFinalAuthorityPackagingCompositeLightweightBoundary :
  YMFinalAuthorityPackagingCompositeLightweightBoundary
canonicalYMFinalAuthorityPackagingCompositeLightweightBoundary =
  record
    { clauses = canonicalYMFinalAuthorityClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMFinalAuthorityBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; provedStillFalse = refl
    }

YMFinalAuthorityPackagingCompositeRecordedIsTrue :
  YMFinalAuthorityPackagingCompositeRecorded ≡ true
YMFinalAuthorityPackagingCompositeRecordedIsTrue = refl
