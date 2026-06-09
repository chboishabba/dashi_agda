module DASHI.Physics.Closure.YMContinuumMassGapToClayAuthorityBlockerCompositeLightweightBoundary where

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

data YMClayAuthorityClause : Set where
  finalAssemblyBoundaryImported : YMClayAuthorityClause
  reflectionPositivityBoundaryStillNamed : YMClayAuthorityClause
  osWightmanAuthorityStillNamed : YMClayAuthorityClause
  externalAcceptanceStillRequired : YMClayAuthorityClause
  continuumMassGapAuthorityStillBlocked : YMClayAuthorityClause
  clayPromotionStillForbidden : YMClayAuthorityClause

canonicalYMClayAuthorityClauses : List YMClayAuthorityClause
canonicalYMClayAuthorityClauses =
  finalAssemblyBoundaryImported
  ∷ reflectionPositivityBoundaryStillNamed
  ∷ osWightmanAuthorityStillNamed
  ∷ externalAcceptanceStillRequired
  ∷ continuumMassGapAuthorityStillBlocked
  ∷ clayPromotionStillForbidden
  ∷ []

ymClayAuthorityClauseCount : Nat
ymClayAuthorityClauseCount = listLength canonicalYMClayAuthorityClauses

ymClayAuthorityClauseCountIs6 : ymClayAuthorityClauseCount ≡ 6
ymClayAuthorityClauseCountIs6 = refl

data YMClayAuthorityBlocker : Set where
  blocker-reflectionPositivityBoundaryStillOpen : YMClayAuthorityBlocker
  blocker-osWightmanAuthorityStillOpen : YMClayAuthorityBlocker
  blocker-finalAssemblyTheoremStillOpen : YMClayAuthorityBlocker
  blocker-externalAcceptanceStillOpen : YMClayAuthorityBlocker
  blocker-clayPromotionForbidden : YMClayAuthorityBlocker

canonicalYMClayAuthorityBlockers : List YMClayAuthorityBlocker
canonicalYMClayAuthorityBlockers =
  blocker-reflectionPositivityBoundaryStillOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalAssemblyTheoremStillOpen
  ∷ blocker-externalAcceptanceStillOpen
  ∷ blocker-clayPromotionForbidden
  ∷ []

YMContinuumMassGapToClayAuthorityBlockerCompositeRecorded : Bool
YMContinuumMassGapToClayAuthorityBlockerCompositeRecorded = true

YMContinuumMassGapToClayAuthorityBlockerCompositeProved : Bool
YMContinuumMassGapToClayAuthorityBlockerCompositeProved = false

record YMContinuumMassGapToClayAuthorityBlockerCompositeLightweightBoundary : Set where
  field
    clauses : List YMClayAuthorityClause
    clausesCanonical : clauses ≡ canonicalYMClayAuthorityClauses
    blockers : List YMClayAuthorityBlocker
    blockersCanonical : blockers ≡ canonicalYMClayAuthorityBlockers
    clauseCountIs6 : ymClayAuthorityClauseCount ≡ 6
    provedStillFalse :
      YMContinuumMassGapToClayAuthorityBlockerCompositeProved ≡ false

canonicalYMContinuumMassGapToClayAuthorityBlockerCompositeLightweightBoundary :
  YMContinuumMassGapToClayAuthorityBlockerCompositeLightweightBoundary
canonicalYMContinuumMassGapToClayAuthorityBlockerCompositeLightweightBoundary =
  record
    { clauses = canonicalYMClayAuthorityClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMClayAuthorityBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMContinuumMassGapToClayAuthorityBlockerCompositeRecordedIsTrue :
  YMContinuumMassGapToClayAuthorityBlockerCompositeRecorded ≡ true
YMContinuumMassGapToClayAuthorityBlockerCompositeRecordedIsTrue = refl
