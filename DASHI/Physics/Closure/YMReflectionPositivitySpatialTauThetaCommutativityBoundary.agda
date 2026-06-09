module DASHI.Physics.Closure.YMReflectionPositivitySpatialTauThetaCommutativityBoundary where

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

commutativityText : String
commutativityText =
  "tau(theta(sigma)) = theta(tau(sigma)) because tau reverses orientation while theta reflects coordinates"

data YMReflectionPositivityTauThetaClause : Set where
  tauActsOnOrientationOnlyRecorded : YMReflectionPositivityTauThetaClause
  thetaActsOnCoordinatesOnlyRecorded : YMReflectionPositivityTauThetaClause
  tauThetaCommutativityRecorded : YMReflectionPositivityTauThetaClause
  fourEdgeFamilyChecksRecorded : YMReflectionPositivityTauThetaClause
  thetaStarPreservesDomainInputRecorded : YMReflectionPositivityTauThetaClause

canonicalYMReflectionPositivityTauThetaClauses :
  List YMReflectionPositivityTauThetaClause
canonicalYMReflectionPositivityTauThetaClauses =
  tauActsOnOrientationOnlyRecorded
  ∷ thetaActsOnCoordinatesOnlyRecorded
  ∷ tauThetaCommutativityRecorded
  ∷ fourEdgeFamilyChecksRecorded
  ∷ thetaStarPreservesDomainInputRecorded
  ∷ []

ymReflectionPositivityTauThetaClauseCount : Nat
ymReflectionPositivityTauThetaClauseCount =
  listLength canonicalYMReflectionPositivityTauThetaClauses

ymReflectionPositivityTauThetaClauseCountIs5 :
  ymReflectionPositivityTauThetaClauseCount ≡ 5
ymReflectionPositivityTauThetaClauseCountIs5 = refl

data YMReflectionPositivityTauThetaBlocker : Set where
  blocker-edgeFamilyProofStillAbstract : YMReflectionPositivityTauThetaBlocker
  blocker-domainPreservationStillOpen : YMReflectionPositivityTauThetaBlocker
  blocker-osAxiomStillOpen : YMReflectionPositivityTauThetaBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityTauThetaBlocker

canonicalYMReflectionPositivityTauThetaBlockers :
  List YMReflectionPositivityTauThetaBlocker
canonicalYMReflectionPositivityTauThetaBlockers =
  blocker-edgeFamilyProofStillAbstract
  ∷ blocker-domainPreservationStillOpen
  ∷ blocker-osAxiomStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivitySpatialTauThetaCommutativityRecorded : Bool
YMReflectionPositivitySpatialTauThetaCommutativityRecorded = true

YMReflectionPositivitySpatialTauThetaCommutativityProved : Bool
YMReflectionPositivitySpatialTauThetaCommutativityProved = false

record YMReflectionPositivitySpatialTauThetaCommutativityBoundary : Set where
  field
    clauses : List YMReflectionPositivityTauThetaClause
    clausesCanonical : clauses ≡ canonicalYMReflectionPositivityTauThetaClauses
    blockers : List YMReflectionPositivityTauThetaBlocker
    blockersCanonical : blockers ≡ canonicalYMReflectionPositivityTauThetaBlockers
    clauseCountIs5 : ymReflectionPositivityTauThetaClauseCount ≡ 5
    theoremStillFalse :
      YMReflectionPositivitySpatialTauThetaCommutativityProved ≡ false

canonicalYMReflectionPositivitySpatialTauThetaCommutativityBoundary :
  YMReflectionPositivitySpatialTauThetaCommutativityBoundary
canonicalYMReflectionPositivitySpatialTauThetaCommutativityBoundary =
  record
    { clauses = canonicalYMReflectionPositivityTauThetaClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMReflectionPositivityTauThetaBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivitySpatialTauThetaCommutativityRecordedIsTrue :
  YMReflectionPositivitySpatialTauThetaCommutativityRecorded ≡ true
YMReflectionPositivitySpatialTauThetaCommutativityRecordedIsTrue = refl
