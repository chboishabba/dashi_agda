module DASHI.Physics.Closure.YMHyperbolicShimuraToEuclideanUniversalityBoundary where

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

rhoBoundaryReference : String
rhoBoundaryReference =
  "DASHI.Physics.Closure.YMContinuumUniformRhoBoundBoundary"

leakageBoundaryReference : String
leakageBoundaryReference =
  "DASHI.Physics.Closure.YMContinuumUniformLeakageBoundBoundary"

routeBoundaryReference : String
routeBoundaryReference =
  "DASHI.Physics.Closure.YMBTToFourDimensionalContinuumRouteBoundary"

gapTransferText : String
gapTransferText =
  "gap(H_L^Eucl) >= gamma_d - C*beta*p^(-d)"

data YMUniversalityClause : Set where
  z4EmbedsIntoBT4Recorded : YMUniversalityClause
  bulkPlaquetteActionMatchesRecorded : YMUniversalityClause
  boundaryPlaquetteFractionDecaysRecorded : YMUniversalityClause
  operatorNormDifferenceBudgetRecorded : YMUniversalityClause
  weylGapTransferRecorded : YMUniversalityClause
  rgResidualHonestyClauseRecorded : YMUniversalityClause

canonicalYMUniversalityClauses : List YMUniversalityClause
canonicalYMUniversalityClauses =
  z4EmbedsIntoBT4Recorded
  ∷ bulkPlaquetteActionMatchesRecorded
  ∷ boundaryPlaquetteFractionDecaysRecorded
  ∷ operatorNormDifferenceBudgetRecorded
  ∷ weylGapTransferRecorded
  ∷ rgResidualHonestyClauseRecorded
  ∷ []

ymUniversalityClauseCount : Nat
ymUniversalityClauseCount = listLength canonicalYMUniversalityClauses

ymUniversalityClauseCountIs6 : ymUniversalityClauseCount ≡ 6
ymUniversalityClauseCountIs6 = refl

data YMUniversalityBlocker : Set where
  blocker-btToEuclideanMatchingProofOpen : YMUniversalityBlocker
  blocker-boundaryErrorToOperatorNormProofOpen : YMUniversalityBlocker
  blocker-rgDimensionalTransmutationOpen : YMUniversalityBlocker
  blocker-osWightmanContinuumAuthorityOpen : YMUniversalityBlocker
  blocker-ymClayPromotionForbidden : YMUniversalityBlocker

canonicalYMUniversalityBlockers : List YMUniversalityBlocker
canonicalYMUniversalityBlockers =
  blocker-btToEuclideanMatchingProofOpen
  ∷ blocker-boundaryErrorToOperatorNormProofOpen
  ∷ blocker-rgDimensionalTransmutationOpen
  ∷ blocker-osWightmanContinuumAuthorityOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMHyperbolicShimuraToEuclideanUniversalityRecorded : Bool
YMHyperbolicShimuraToEuclideanUniversalityRecorded = true

YMHyperbolicShimuraToEuclideanUniversalityProved : Bool
YMHyperbolicShimuraToEuclideanUniversalityProved = false

record YMHyperbolicShimuraToEuclideanUniversalityBoundary : Set where
  field
    clauses : List YMUniversalityClause
    clausesCanonical : clauses ≡ canonicalYMUniversalityClauses
    blockers : List YMUniversalityBlocker
    blockersCanonical : blockers ≡ canonicalYMUniversalityBlockers
    clauseCountIs6 : ymUniversalityClauseCount ≡ 6
    universalityStillFalse :
      YMHyperbolicShimuraToEuclideanUniversalityProved ≡ false

canonicalYMHyperbolicShimuraToEuclideanUniversalityBoundary :
  YMHyperbolicShimuraToEuclideanUniversalityBoundary
canonicalYMHyperbolicShimuraToEuclideanUniversalityBoundary =
  record
    { clauses = canonicalYMUniversalityClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMUniversalityBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; universalityStillFalse = refl
    }

YMHyperbolicShimuraToEuclideanUniversalityRecordedIsTrue :
  YMHyperbolicShimuraToEuclideanUniversalityRecorded ≡ true
YMHyperbolicShimuraToEuclideanUniversalityRecordedIsTrue = refl
