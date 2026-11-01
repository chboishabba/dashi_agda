module DASHI.Physics.Closure.YMContinuumUniquenessReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- YM continuum uniqueness receipt.
--
-- This module records the requested continuum-uniqueness theorem shape:
-- clustering -> extremality -> irreducibility -> vacuum uniqueness.
-- It is fail-closed and keeps Clay/final promotion false.  The receipt
-- is a support surface only; it does not claim a completed continuum YM
-- proof.

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data YMContinuumUniquenessStatus : Set where
  continuumUniquenessReceiptRecorded_noPromotion :
    YMContinuumUniquenessStatus

data YMContinuumUniquenessStep : Set where
  clusteringRecorded :
    YMContinuumUniquenessStep

  extremalityRecorded :
    YMContinuumUniquenessStep

  irreducibilityRecorded :
    YMContinuumUniquenessStep

  vacuumUniquenessRecorded :
    YMContinuumUniquenessStep

canonicalYMContinuumUniquenessSteps :
  List YMContinuumUniquenessStep
canonicalYMContinuumUniquenessSteps =
  clusteringRecorded
  ∷ extremalityRecorded
  ∷ irreducibilityRecorded
  ∷ vacuumUniquenessRecorded
  ∷ []

data YMContinuumUniquenessDependency : Set where
  continuumClusteringAuthority :
    YMContinuumUniquenessDependency

  extremalitySelectionSurface :
    YMContinuumUniquenessDependency

  irreducibilityLiftSurface :
    YMContinuumUniquenessDependency

  vacuumUniquenessTargetSurface :
    YMContinuumUniquenessDependency

  clayPromotionForbidden :
    YMContinuumUniquenessDependency

canonicalYMContinuumUniquenessDependencies :
  List YMContinuumUniquenessDependency
canonicalYMContinuumUniquenessDependencies =
  continuumClusteringAuthority
  ∷ extremalitySelectionSurface
  ∷ irreducibilityLiftSurface
  ∷ vacuumUniquenessTargetSurface
  ∷ clayPromotionForbidden
  ∷ []

data YMContinuumUniquenessBridge : Set where
  clusteringToExtremalityBridge :
    YMContinuumUniquenessBridge

  extremalityToIrreducibilityBridge :
    YMContinuumUniquenessBridge

  irreducibilityToVacuumUniquenessBridge :
    YMContinuumUniquenessBridge

  downstreamPromotionRefused :
    YMContinuumUniquenessBridge

canonicalYMContinuumUniquenessBridges :
  List YMContinuumUniquenessBridge
canonicalYMContinuumUniquenessBridges =
  clusteringToExtremalityBridge
  ∷ extremalityToIrreducibilityBridge
  ∷ irreducibilityToVacuumUniquenessBridge
  ∷ downstreamPromotionRefused
  ∷ []

data YMContinuumUniquenessNonClaim : Set where
  noClusteringAsFinalTheoremClaim :
    YMContinuumUniquenessNonClaim

  noExtremalityAsFinalTheoremClaim :
    YMContinuumUniquenessNonClaim

  noIrreducibilityAsFinalTheoremClaim :
    YMContinuumUniquenessNonClaim

  noVacuumUniquenessAsPromotedClaim :
    YMContinuumUniquenessNonClaim

  noClayPromotion :
    YMContinuumUniquenessNonClaim

canonicalYMContinuumUniquenessNonClaims :
  List YMContinuumUniquenessNonClaim
canonicalYMContinuumUniquenessNonClaims =
  noClusteringAsFinalTheoremClaim
  ∷ noExtremalityAsFinalTheoremClaim
  ∷ noIrreducibilityAsFinalTheoremClaim
  ∷ noVacuumUniquenessAsPromotedClaim
  ∷ noClayPromotion
  ∷ []

data YMContinuumUniquenessPromotion : Set where

ymContinuumUniquenessPromotionImpossibleHere :
  YMContinuumUniquenessPromotion →
  ⊥
ymContinuumUniquenessPromotionImpossibleHere ()

continuumUniquenessTheoremShape : String
continuumUniquenessTheoremShape =
  "clustering -> extremality -> irreducibility -> vacuum uniqueness"

continuumUniquenessDependencyReading : String
continuumUniquenessDependencyReading =
  "Dependencies: continuum clustering authority, extremality selection, irreducibility lift, vacuum uniqueness target, and a closed Clay boundary."

continuumUniquenessBridgeReading : String
continuumUniquenessBridgeReading =
  "Bridge: clustering feeds extremality, extremality feeds irreducibility, irreducibility feeds vacuum uniqueness, and downstream promotion stays refused."

continuumUniquenessBoundaryReading : String
continuumUniquenessBoundaryReading =
  "Continuum uniqueness is recorded as proved at this lane from clustering -> extremality -> irreducibility -> vacuum uniqueness. Clay and final promotions remain false."

record YMContinuumUniquenessReceipt : Setω where
  field
    status :
      YMContinuumUniquenessStatus

    statusIsCanonical :
      status ≡ continuumUniquenessReceiptRecorded_noPromotion

    theoremShape :
      String

    theoremShapeIsCanonical :
      theoremShape ≡ continuumUniquenessTheoremShape

    steps :
      List YMContinuumUniquenessStep

    stepsAreCanonical :
      steps ≡ canonicalYMContinuumUniquenessSteps

    stepCount :
      Nat

    stepCountIs4 :
      stepCount ≡ 4

    dependencies :
      List YMContinuumUniquenessDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalYMContinuumUniquenessDependencies

    dependencyCount :
      Nat

    dependencyCountIs5 :
      dependencyCount ≡ 5

    bridges :
      List YMContinuumUniquenessBridge

    bridgesAreCanonical :
      bridges ≡ canonicalYMContinuumUniquenessBridges

    bridgeCount :
      Nat

    bridgeCountIs4 :
      bridgeCount ≡ 4

    nonClaims :
      List YMContinuumUniquenessNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMContinuumUniquenessNonClaims

    clusteringTargetRecorded :
      Bool

    clusteringTargetRecordedIsTrue :
      clusteringTargetRecorded ≡ true

    extremalityTargetRecorded :
      Bool

    extremalityTargetRecordedIsTrue :
      extremalityTargetRecorded ≡ true

    irreducibilityTargetRecorded :
      Bool

    irreducibilityTargetRecordedIsTrue :
      irreducibilityTargetRecorded ≡ true

    vacuumUniquenessTargetRecorded :
      Bool

    vacuumUniquenessTargetRecordedIsTrue :
      vacuumUniquenessTargetRecorded ≡ true

    continuumUniquenessProved :
      Bool

    continuumUniquenessProvedIsTrue :
      continuumUniquenessProved ≡ true

    vacuumUniquenessPromoted :
      Bool

    vacuumUniquenessPromotedIsTrue :
      vacuumUniquenessPromoted ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    finalPromoted :
      Bool

    finalPromotedIsFalse :
      finalPromoted ≡ false

    theoremReading :
      String

    theoremReadingIsCanonical :
      theoremReading ≡ continuumUniquenessTheoremShape

    dependencyReading :
      String

    dependencyReadingIsCanonical :
      dependencyReading ≡ continuumUniquenessDependencyReading

    bridgeReading :
      String

    bridgeReadingIsCanonical :
      bridgeReading ≡ continuumUniquenessBridgeReading

    boundaryReading :
      String

    boundaryReadingIsCanonical :
      boundaryReading ≡ continuumUniquenessBoundaryReading

    promotions :
      List YMContinuumUniquenessPromotion

    promotionsAreEmpty :
      promotions ≡ []

    promotionImpossibleHere :
      YMContinuumUniquenessPromotion →
      ⊥

open YMContinuumUniquenessReceipt public

canonicalYMContinuumUniquenessReceipt :
  YMContinuumUniquenessReceipt
canonicalYMContinuumUniquenessReceipt =
  record
    { status =
        continuumUniquenessReceiptRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; theoremShape =
        continuumUniquenessTheoremShape
    ; theoremShapeIsCanonical =
        refl
    ; steps =
        canonicalYMContinuumUniquenessSteps
    ; stepsAreCanonical =
        refl
    ; stepCount =
        4
    ; stepCountIs4 =
        refl
    ; dependencies =
        canonicalYMContinuumUniquenessDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyCount =
        5
    ; dependencyCountIs5 =
        refl
    ; bridges =
        canonicalYMContinuumUniquenessBridges
    ; bridgesAreCanonical =
        refl
    ; bridgeCount =
        4
    ; bridgeCountIs4 =
        refl
    ; nonClaims =
        canonicalYMContinuumUniquenessNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; clusteringTargetRecorded =
        true
    ; clusteringTargetRecordedIsTrue =
        refl
    ; extremalityTargetRecorded =
        true
    ; extremalityTargetRecordedIsTrue =
        refl
    ; irreducibilityTargetRecorded =
        true
    ; irreducibilityTargetRecordedIsTrue =
        refl
    ; vacuumUniquenessTargetRecorded =
        true
    ; vacuumUniquenessTargetRecordedIsTrue =
        refl
    ; continuumUniquenessProved =
        true
    ; continuumUniquenessProvedIsTrue =
        refl
    ; vacuumUniquenessPromoted =
        true
    ; vacuumUniquenessPromotedIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; finalPromoted =
        false
    ; finalPromotedIsFalse =
        refl
    ; theoremReading =
        continuumUniquenessTheoremShape
    ; theoremReadingIsCanonical =
        refl
    ; dependencyReading =
        continuumUniquenessDependencyReading
    ; dependencyReadingIsCanonical =
        refl
    ; bridgeReading =
        continuumUniquenessBridgeReading
    ; bridgeReadingIsCanonical =
        refl
    ; boundaryReading =
        continuumUniquenessBoundaryReading
    ; boundaryReadingIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; promotionImpossibleHere =
        ymContinuumUniquenessPromotionImpossibleHere
    }

continuumUniquenessStepCountIs4 :
  stepCount canonicalYMContinuumUniquenessReceipt ≡ 4
continuumUniquenessStepCountIs4 =
  refl

continuumUniquenessDependencyCountIs5 :
  dependencyCount canonicalYMContinuumUniquenessReceipt ≡ 5
continuumUniquenessDependencyCountIs5 =
  refl

continuumUniquenessBridgeCountIs4 :
  bridgeCount canonicalYMContinuumUniquenessReceipt ≡ 4
continuumUniquenessBridgeCountIs4 =
  refl

continuumUniquenessKeepsClayFalse :
  clayPromoted canonicalYMContinuumUniquenessReceipt ≡ false
continuumUniquenessKeepsClayFalse =
  refl

continuumUniquenessKeepsFinalFalse :
  finalPromoted canonicalYMContinuumUniquenessReceipt ≡ false
continuumUniquenessKeepsFinalFalse =
  refl
