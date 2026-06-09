module DASHI.Physics.Closure.YMKillingBoundaryGreenIdentityBoundary where

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

greenIdentityText : String
greenIdentityText =
  "<dA,B>=<A,d*B> after paired boundary sum cancellation"

hamiltonianSymmetryText : String
hamiltonianSymmetryText =
  "<H_d A,B>=<A,H_d B>"

data YMGreenIdentityClause : Set where
  orientationSignCancellationConsumed : YMGreenIdentityClause
  pairedBoundarySumZeroConsumed : YMGreenIdentityClause
  finiteHodgeAdjointnessRecorded : YMGreenIdentityClause
  discreteGreenIdentityRecorded : YMGreenIdentityClause
  hamiltonianSymmetryRecorded : YMGreenIdentityClause
  quotientDescentFeedsSelfAdjointness : YMGreenIdentityClause
  dominationAndOSTransferRemainLater : YMGreenIdentityClause

canonicalYMGreenIdentityClauses : List YMGreenIdentityClause
canonicalYMGreenIdentityClauses =
  orientationSignCancellationConsumed
  ∷ pairedBoundarySumZeroConsumed
  ∷ finiteHodgeAdjointnessRecorded
  ∷ discreteGreenIdentityRecorded
  ∷ hamiltonianSymmetryRecorded
  ∷ quotientDescentFeedsSelfAdjointness
  ∷ dominationAndOSTransferRemainLater
  ∷ []

ymGreenIdentityClauseCount : Nat
ymGreenIdentityClauseCount = listLength canonicalYMGreenIdentityClauses

ymGreenIdentityClauseCountIs7 : ymGreenIdentityClauseCount ≡ 7
ymGreenIdentityClauseCountIs7 = refl

data YMGreenIdentityBlocker : Set where
  blocker-orientationSignCancellationOpen : YMGreenIdentityBlocker
  blocker-finiteHodgeAdjointnessProofOpen : YMGreenIdentityBlocker
  blocker-greenIdentityProofOpen : YMGreenIdentityBlocker
  blocker-selfAdjointnessTheoremStillOpen : YMGreenIdentityBlocker
  blocker-dominationStillOpen : YMGreenIdentityBlocker
  blocker-ymClayPromotionForbidden : YMGreenIdentityBlocker

canonicalYMGreenIdentityBlockers : List YMGreenIdentityBlocker
canonicalYMGreenIdentityBlockers =
  blocker-orientationSignCancellationOpen
  ∷ blocker-finiteHodgeAdjointnessProofOpen
  ∷ blocker-greenIdentityProofOpen
  ∷ blocker-selfAdjointnessTheoremStillOpen
  ∷ blocker-dominationStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMKillingBoundaryGreenIdentityRecorded : Bool
YMKillingBoundaryGreenIdentityRecorded = true

YMKillingBoundaryGreenIdentityProved : Bool
YMKillingBoundaryGreenIdentityProved = false

record YMKillingBoundaryGreenIdentityBoundary : Set where
  field
    clauses : List YMGreenIdentityClause
    clausesCanonical : clauses ≡ canonicalYMGreenIdentityClauses
    blockers : List YMGreenIdentityBlocker
    blockersCanonical : blockers ≡ canonicalYMGreenIdentityBlockers
    clauseCountIs7 : ymGreenIdentityClauseCount ≡ 7
    theoremStillFalse : YMKillingBoundaryGreenIdentityProved ≡ false

canonicalYMKillingBoundaryGreenIdentityBoundary :
  YMKillingBoundaryGreenIdentityBoundary
canonicalYMKillingBoundaryGreenIdentityBoundary =
  record
    { clauses = canonicalYMGreenIdentityClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMGreenIdentityBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMKillingBoundaryGreenIdentityRecordedIsTrue :
  YMKillingBoundaryGreenIdentityRecorded ≡ true
YMKillingBoundaryGreenIdentityRecordedIsTrue = refl
