module DASHI.Physics.Closure.YMKillingBoundaryOrientationSignCancellationBoundary where

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

orientationPairFormulaText : String
orientationPairFormulaText =
  "K(A(s),B(s))*eps(s)+K(A(tau(s)),B(tau(s)))*eps(tau(s))=0"

data YMOrientationSignClause : Set where
  oppositeFacePairingRecorded : YMOrientationSignClause
  orientationReversalRecorded : YMOrientationSignClause
  killingFormBilinearityRecorded : YMOrientationSignClause
  killingWeightEqualityAcrossPairRecorded : YMOrientationSignClause
  pairedBoundaryTermCancellationRecorded : YMOrientationSignClause
  boundarySumZeroRecorded : YMOrientationSignClause
  greenIdentityFeedsNextStepOnly : YMOrientationSignClause

canonicalYMOrientationSignClauses : List YMOrientationSignClause
canonicalYMOrientationSignClauses =
  oppositeFacePairingRecorded
  ∷ orientationReversalRecorded
  ∷ killingFormBilinearityRecorded
  ∷ killingWeightEqualityAcrossPairRecorded
  ∷ pairedBoundaryTermCancellationRecorded
  ∷ boundarySumZeroRecorded
  ∷ greenIdentityFeedsNextStepOnly
  ∷ []

ymOrientationSignClauseCount : Nat
ymOrientationSignClauseCount = listLength canonicalYMOrientationSignClauses

ymOrientationSignClauseCountIs7 : ymOrientationSignClauseCount ≡ 7
ymOrientationSignClauseCountIs7 = refl

data YMOrientationSignBlocker : Set where
  blocker-oppositeFacePairingProofOpen : YMOrientationSignBlocker
  blocker-orientationReversalProofOpen : YMOrientationSignBlocker
  blocker-killingWeightEqualityProofOpen : YMOrientationSignBlocker
  blocker-pairedCancellationProofOpen : YMOrientationSignBlocker
  blocker-greenIdentityStillOpen : YMOrientationSignBlocker
  blocker-ymClayPromotionForbidden : YMOrientationSignBlocker

canonicalYMOrientationSignBlockers : List YMOrientationSignBlocker
canonicalYMOrientationSignBlockers =
  blocker-oppositeFacePairingProofOpen
  ∷ blocker-orientationReversalProofOpen
  ∷ blocker-killingWeightEqualityProofOpen
  ∷ blocker-pairedCancellationProofOpen
  ∷ blocker-greenIdentityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMKillingBoundaryOrientationSignCancellationRecorded : Bool
YMKillingBoundaryOrientationSignCancellationRecorded = true

YMKillingBoundaryOrientationSignCancellationProved : Bool
YMKillingBoundaryOrientationSignCancellationProved = false

record YMKillingBoundaryOrientationSignCancellationBoundary : Set where
  field
    clauses : List YMOrientationSignClause
    clausesCanonical : clauses ≡ canonicalYMOrientationSignClauses
    blockers : List YMOrientationSignBlocker
    blockersCanonical : blockers ≡ canonicalYMOrientationSignBlockers
    clauseCountIs7 : ymOrientationSignClauseCount ≡ 7
    theoremStillFalse :
      YMKillingBoundaryOrientationSignCancellationProved ≡ false

canonicalYMKillingBoundaryOrientationSignCancellationBoundary :
  YMKillingBoundaryOrientationSignCancellationBoundary
canonicalYMKillingBoundaryOrientationSignCancellationBoundary =
  record
    { clauses = canonicalYMOrientationSignClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMOrientationSignBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMKillingBoundaryOrientationSignCancellationRecordedIsTrue :
  YMKillingBoundaryOrientationSignCancellationRecorded ≡ true
YMKillingBoundaryOrientationSignCancellationRecordedIsTrue = refl
