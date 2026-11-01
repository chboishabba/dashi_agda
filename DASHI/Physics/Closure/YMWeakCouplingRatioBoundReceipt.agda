module DASHI.Physics.Closure.YMWeakCouplingRatioBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Weak-coupling ratio bound receipt.
--
-- This module records the typed surface of the tuned polymer ratio
-- argument supplied by the user:
--
--   a = c_K / (4 g^2)
--
-- together with the 16e logarithmic threshold and the target geometric
-- ratio bound below 1/4.  It is a fail-closed receipt only.  It does not
-- promote KP, the continuum construction, or Clay Yang-Mills.

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data YMWeakCouplingRatioBoundStatus : Set where
  weakCouplingRatioBoundRecorded_noPromotion :
    YMWeakCouplingRatioBoundStatus

data YMWeakCouplingRatioBoundClause : Set where
  tuningLawRecorded :
    YMWeakCouplingRatioBoundClause

  logarithmicThresholdRecorded :
    YMWeakCouplingRatioBoundClause

  ratioDefinitionRecorded :
    YMWeakCouplingRatioBoundClause

  quarterTargetRecorded :
    YMWeakCouplingRatioBoundClause

  dependencyInventoryRecorded :
    YMWeakCouplingRatioBoundClause

  nonClaimBoundaryRecorded :
    YMWeakCouplingRatioBoundClause

  promotionLockedRecorded :
    YMWeakCouplingRatioBoundClause

canonicalYMWeakCouplingRatioBoundClauses :
  List YMWeakCouplingRatioBoundClause
canonicalYMWeakCouplingRatioBoundClauses =
  tuningLawRecorded
  ∷ logarithmicThresholdRecorded
  ∷ ratioDefinitionRecorded
  ∷ quarterTargetRecorded
  ∷ dependencyInventoryRecorded
  ∷ nonClaimBoundaryRecorded
  ∷ promotionLockedRecorded
  ∷ []

ymWeakCouplingRatioBoundClauseCount : Nat
ymWeakCouplingRatioBoundClauseCount =
  listCount canonicalYMWeakCouplingRatioBoundClauses

ymWeakCouplingRatioBoundClauseCountIs7 :
  ymWeakCouplingRatioBoundClauseCount ≡ 7
ymWeakCouplingRatioBoundClauseCountIs7 =
  refl

data YMWeakCouplingRatioDependency : Set where
  dependencyUserTunedScaleLaw :
    YMWeakCouplingRatioDependency

  dependencyLogThreshold16e :
    YMWeakCouplingRatioDependency

  dependencyGeometricRatioTargetQuarter :
    YMWeakCouplingRatioDependency

  dependencyFailClosedReceiptSurface :
    YMWeakCouplingRatioDependency

  dependencyNoPromotionBoundary :
    YMWeakCouplingRatioDependency

canonicalYMWeakCouplingRatioDependencies :
  List YMWeakCouplingRatioDependency
canonicalYMWeakCouplingRatioDependencies =
  dependencyUserTunedScaleLaw
  ∷ dependencyLogThreshold16e
  ∷ dependencyGeometricRatioTargetQuarter
  ∷ dependencyFailClosedReceiptSurface
  ∷ dependencyNoPromotionBoundary
  ∷ []

ymWeakCouplingRatioDependencyCount : Nat
ymWeakCouplingRatioDependencyCount =
  listCount canonicalYMWeakCouplingRatioDependencies

ymWeakCouplingRatioDependencyCountIs5 :
  ymWeakCouplingRatioDependencyCount ≡ 5
ymWeakCouplingRatioDependencyCountIs5 =
  refl

data YMWeakCouplingRatioBoundNonClaim : Set where
  noKPPromotionClaim :
    YMWeakCouplingRatioBoundNonClaim

  noContinuumPromotionClaim :
    YMWeakCouplingRatioBoundNonClaim

  noClayPromotionClaim :
    YMWeakCouplingRatioBoundNonClaim

  noOptimalityClaim :
    YMWeakCouplingRatioBoundNonClaim

  noNewNumericEstimateClaim :
    YMWeakCouplingRatioBoundNonClaim

  noExternalAuthorityClaim :
    YMWeakCouplingRatioBoundNonClaim

canonicalYMWeakCouplingRatioBoundNonClaims :
  List YMWeakCouplingRatioBoundNonClaim
canonicalYMWeakCouplingRatioBoundNonClaims =
  noKPPromotionClaim
  ∷ noContinuumPromotionClaim
  ∷ noClayPromotionClaim
  ∷ noOptimalityClaim
  ∷ noNewNumericEstimateClaim
  ∷ noExternalAuthorityClaim
  ∷ []

ymWeakCouplingRatioBoundTuningLaw : String
ymWeakCouplingRatioBoundTuningLaw =
  "a = c_K / (4 g^2)"

ymWeakCouplingRatioBoundLogarithmicThreshold : String
ymWeakCouplingRatioBoundLogarithmicThreshold =
  "16e logarithmic threshold"

ymWeakCouplingRatioBoundRatioDefinition : String
ymWeakCouplingRatioBoundRatioDefinition =
  "the geometric ratio is tuned by the weak-coupling polymer argument rather than claimed as a fresh analytic theorem"

ymWeakCouplingRatioBoundQuarterTarget : String
ymWeakCouplingRatioBoundQuarterTarget =
  "geometric ratio <= 1/4"

ymWeakCouplingRatioBoundSummary : String
ymWeakCouplingRatioBoundSummary =
  "Weak-coupling ratio receipt: the tuned scale law a = c_K / (4 g^2), the 16e logarithmic threshold, and the target geometric ratio bound below 1/4 are recorded as a fail-closed typed surface. No KP, continuum, or Clay promotion is introduced."

ymWeakCouplingRatioBoundBoundary : String
ymWeakCouplingRatioBoundBoundary =
  "Boundary: this is a receipt for the supplied tuning argument only; it records the ratio target and dependencies, but it does not manufacture analytic estimates, optimality, or external authority."

record YMWeakCouplingRatioBoundCore : Set where
  constructor mkYMWeakCouplingRatioBoundCore
  field
    tuningLaw :
      String

    tuningLawIsCanonical :
      tuningLaw ≡ ymWeakCouplingRatioBoundTuningLaw

    logarithmicThreshold :
      String

    logarithmicThresholdIsCanonical :
      logarithmicThreshold
      ≡
      ymWeakCouplingRatioBoundLogarithmicThreshold

    ratioDefinition :
      String

    ratioDefinitionIsCanonical :
      ratioDefinition ≡ ymWeakCouplingRatioBoundRatioDefinition

    quarterTarget :
      String

    quarterTargetIsCanonical :
      quarterTarget ≡ ymWeakCouplingRatioBoundQuarterTarget

    summary :
      String

    summaryIsCanonical :
      summary ≡ ymWeakCouplingRatioBoundSummary

record YMWeakCouplingRatioBoundReceipt : Setω where
  field
    status :
      YMWeakCouplingRatioBoundStatus

    statusIsCanonical :
      status ≡ weakCouplingRatioBoundRecorded_noPromotion

    core :
      YMWeakCouplingRatioBoundCore

    dependencyInventory :
      List YMWeakCouplingRatioDependency

    dependencyInventoryIsCanonical :
      dependencyInventory ≡ canonicalYMWeakCouplingRatioDependencies

    clauseInventory :
      List YMWeakCouplingRatioBoundClause

    clauseInventoryIsCanonical :
      clauseInventory ≡ canonicalYMWeakCouplingRatioBoundClauses

    nonClaims :
      List YMWeakCouplingRatioBoundNonClaim

    nonClaimsIsCanonical :
      nonClaims ≡ canonicalYMWeakCouplingRatioBoundNonClaims

    dependencyCount :
      Nat

    dependencyCountIsCanonical :
      dependencyCount ≡ ymWeakCouplingRatioDependencyCount

    clauseCount :
      Nat

    clauseCountIsCanonical :
      clauseCount ≡ ymWeakCouplingRatioBoundClauseCount

    ratioBoundRecorded :
      Bool

    ratioBoundRecordedIsTrue :
      ratioBoundRecorded ≡ true

    kpPromotion :
      Bool

    kpPromotionIsFalse :
      kpPromotion ≡ false

    continuumPromotion :
      Bool

    continuumPromotionIsFalse :
      continuumPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ ymWeakCouplingRatioBoundBoundary

open YMWeakCouplingRatioBoundCore public
open YMWeakCouplingRatioBoundReceipt public

canonicalYMWeakCouplingRatioBoundCore :
  YMWeakCouplingRatioBoundCore
canonicalYMWeakCouplingRatioBoundCore =
  mkYMWeakCouplingRatioBoundCore
    ymWeakCouplingRatioBoundTuningLaw
    refl
    ymWeakCouplingRatioBoundLogarithmicThreshold
    refl
    ymWeakCouplingRatioBoundRatioDefinition
    refl
    ymWeakCouplingRatioBoundQuarterTarget
    refl
    ymWeakCouplingRatioBoundSummary
    refl

data YMWeakCouplingRatioBoundPromotion : Set where

ymWeakCouplingRatioBoundPromotionImpossibleHere :
  YMWeakCouplingRatioBoundPromotion →
  ⊥
ymWeakCouplingRatioBoundPromotionImpossibleHere ()

canonicalYMWeakCouplingRatioBoundReceipt :
  YMWeakCouplingRatioBoundReceipt
canonicalYMWeakCouplingRatioBoundReceipt =
  record
    { status =
        weakCouplingRatioBoundRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; core =
        canonicalYMWeakCouplingRatioBoundCore
    ; dependencyInventory =
        canonicalYMWeakCouplingRatioDependencies
    ; dependencyInventoryIsCanonical =
        refl
    ; clauseInventory =
        canonicalYMWeakCouplingRatioBoundClauses
    ; clauseInventoryIsCanonical =
        refl
    ; nonClaims =
        canonicalYMWeakCouplingRatioBoundNonClaims
    ; nonClaimsIsCanonical =
        refl
    ; dependencyCount =
        ymWeakCouplingRatioDependencyCount
    ; dependencyCountIsCanonical =
        refl
    ; clauseCount =
        ymWeakCouplingRatioBoundClauseCount
    ; clauseCountIsCanonical =
        refl
    ; ratioBoundRecorded =
        true
    ; ratioBoundRecordedIsTrue =
        refl
    ; kpPromotion =
        false
    ; kpPromotionIsFalse =
        refl
    ; continuumPromotion =
        false
    ; continuumPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; boundary =
        ymWeakCouplingRatioBoundBoundary
    ; boundaryIsCanonical =
        refl
    }

ymWeakCouplingRatioBoundRecordedIsTrue :
  ratioBoundRecorded canonicalYMWeakCouplingRatioBoundReceipt ≡ true
ymWeakCouplingRatioBoundRecordedIsTrue =
  refl

ymWeakCouplingRatioBoundNoClay :
  clayPromotion canonicalYMWeakCouplingRatioBoundReceipt ≡ false
ymWeakCouplingRatioBoundNoClay =
  refl
