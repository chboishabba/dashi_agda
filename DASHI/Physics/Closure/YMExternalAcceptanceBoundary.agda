module DASHI.Physics.Closure.YMExternalAcceptanceBoundary where

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

data YMExternalAcceptanceClause : Set where
  finalAssemblyBoundaryImported : YMExternalAcceptanceClause
  reflectionPositivityAuthorityNamed : YMExternalAcceptanceClause
  osWightmanAuthorityNamed : YMExternalAcceptanceClause
  externalReviewPacketRequired : YMExternalAcceptanceClause
  publicationAuthorityStillExternal : YMExternalAcceptanceClause
  clayPromotionStillBlocked : YMExternalAcceptanceClause

canonicalYMExternalAcceptanceClauses : List YMExternalAcceptanceClause
canonicalYMExternalAcceptanceClauses =
  finalAssemblyBoundaryImported
  ∷ reflectionPositivityAuthorityNamed
  ∷ osWightmanAuthorityNamed
  ∷ externalReviewPacketRequired
  ∷ publicationAuthorityStillExternal
  ∷ clayPromotionStillBlocked
  ∷ []

ymExternalAcceptanceClauseCount : Nat
ymExternalAcceptanceClauseCount = listLength canonicalYMExternalAcceptanceClauses

ymExternalAcceptanceClauseCountIs6 : ymExternalAcceptanceClauseCount ≡ 6
ymExternalAcceptanceClauseCountIs6 = refl

data YMExternalAcceptanceBlocker : Set where
  blocker-reflectionPositivityAuthorityStillOpen : YMExternalAcceptanceBlocker
  blocker-osWightmanAuthorityStillOpen : YMExternalAcceptanceBlocker
  blocker-finalAssemblyAuthorityStillOpen : YMExternalAcceptanceBlocker
  blocker-externalReviewStillOpen : YMExternalAcceptanceBlocker
  blocker-ymClayPromotionForbidden : YMExternalAcceptanceBlocker

canonicalYMExternalAcceptanceBlockers : List YMExternalAcceptanceBlocker
canonicalYMExternalAcceptanceBlockers =
  blocker-reflectionPositivityAuthorityStillOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalAssemblyAuthorityStillOpen
  ∷ blocker-externalReviewStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMExternalAcceptanceBoundaryRecorded : Bool
YMExternalAcceptanceBoundaryRecorded = true

YMExternalAcceptanceBoundaryProved : Bool
YMExternalAcceptanceBoundaryProved = false

record YMExternalAcceptanceBoundary : Set where
  field
    clauses : List YMExternalAcceptanceClause
    clausesCanonical : clauses ≡ canonicalYMExternalAcceptanceClauses
    blockers : List YMExternalAcceptanceBlocker
    blockersCanonical : blockers ≡ canonicalYMExternalAcceptanceBlockers
    clauseCountIs6 : ymExternalAcceptanceClauseCount ≡ 6
    theoremStillFalse : YMExternalAcceptanceBoundaryProved ≡ false

canonicalYMExternalAcceptanceBoundary :
  YMExternalAcceptanceBoundary
canonicalYMExternalAcceptanceBoundary =
  record
    { clauses = canonicalYMExternalAcceptanceClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMExternalAcceptanceBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; theoremStillFalse = refl
    }

YMExternalAcceptanceBoundaryRecordedIsTrue :
  YMExternalAcceptanceBoundaryRecorded ≡ true
YMExternalAcceptanceBoundaryRecordedIsTrue = refl
