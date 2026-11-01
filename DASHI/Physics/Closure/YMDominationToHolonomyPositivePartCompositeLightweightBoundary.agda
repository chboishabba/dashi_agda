module DASHI.Physics.Closure.YMDominationToHolonomyPositivePartCompositeLightweightBoundary where

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

preconditionReference : String
preconditionReference =
  "DASHI.Physics.Closure.YMSelfAdjointToDominationPreconditionCompositeLightweightBoundary"

holonomyReference : String
holonomyReference =
  "DASHI.Physics.Closure.YMUniformPositiveHolonomyActionBoundary"

dominationReference : String
dominationReference =
  "DASHI.Physics.Closure.YMHolonomyActionToDominationCompositeBoundary"

data YMDominationHolonomyClause : Set where
  selfAdjointDominationSocketImported : YMDominationHolonomyClause
  positiveHolonomyBudgetImported : YMDominationHolonomyClause
  bochnerWeitzenbockConsumerReferenced : YMDominationHolonomyClause
  vacuumExclusionRouteRecorded : YMDominationHolonomyClause
  finiteSpectralMarginSocketRecorded : YMDominationHolonomyClause
  clayPromotionStillBlocked : YMDominationHolonomyClause

canonicalYMDominationHolonomyClauses : List YMDominationHolonomyClause
canonicalYMDominationHolonomyClauses =
  selfAdjointDominationSocketImported
  ∷ positiveHolonomyBudgetImported
  ∷ bochnerWeitzenbockConsumerReferenced
  ∷ vacuumExclusionRouteRecorded
  ∷ finiteSpectralMarginSocketRecorded
  ∷ clayPromotionStillBlocked
  ∷ []

ymDominationHolonomyClauseCount : Nat
ymDominationHolonomyClauseCount = listLength canonicalYMDominationHolonomyClauses

ymDominationHolonomyClauseCountIs6 : ymDominationHolonomyClauseCount ≡ 6
ymDominationHolonomyClauseCountIs6 = refl

data YMDominationHolonomyBlocker : Set where
  blocker-dominationTheoremStillOpen : YMDominationHolonomyBlocker
  blocker-holonomyPositivePartStillOpen : YMDominationHolonomyBlocker
  blocker-spectralMarginStillOpen : YMDominationHolonomyBlocker
  blocker-osWightmanStillOpen : YMDominationHolonomyBlocker

canonicalYMDominationHolonomyBlockers : List YMDominationHolonomyBlocker
canonicalYMDominationHolonomyBlockers =
  blocker-dominationTheoremStillOpen
  ∷ blocker-holonomyPositivePartStillOpen
  ∷ blocker-spectralMarginStillOpen
  ∷ blocker-osWightmanStillOpen
  ∷ []

YMDominationToHolonomyPositivePartCompositeRecorded : Bool
YMDominationToHolonomyPositivePartCompositeRecorded = true

YMDominationToHolonomyPositivePartCompositeProved : Bool
YMDominationToHolonomyPositivePartCompositeProved = false

record YMDominationToHolonomyPositivePartCompositeLightweightBoundary : Set where
  field
    clauses : List YMDominationHolonomyClause
    clausesCanonical : clauses ≡ canonicalYMDominationHolonomyClauses
    blockers : List YMDominationHolonomyBlocker
    blockersCanonical : blockers ≡ canonicalYMDominationHolonomyBlockers
    clauseCountIs6 : ymDominationHolonomyClauseCount ≡ 6
    provedStillFalse :
      YMDominationToHolonomyPositivePartCompositeProved ≡ false

canonicalYMDominationToHolonomyPositivePartCompositeLightweightBoundary :
  YMDominationToHolonomyPositivePartCompositeLightweightBoundary
canonicalYMDominationToHolonomyPositivePartCompositeLightweightBoundary =
  record
    { clauses = canonicalYMDominationHolonomyClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMDominationHolonomyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMDominationToHolonomyPositivePartCompositeRecordedIsTrue :
  YMDominationToHolonomyPositivePartCompositeRecorded ≡ true
YMDominationToHolonomyPositivePartCompositeRecordedIsTrue = refl
