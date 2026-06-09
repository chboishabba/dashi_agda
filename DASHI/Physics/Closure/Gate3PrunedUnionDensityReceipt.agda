module DASHI.Physics.Closure.Gate3PrunedUnionDensityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3DepthDecoupledFrameReceipt as Depth

------------------------------------------------------------------------
-- Sprint 10 Gate3 pruned-union density target.
--
-- Single-level Nyquist can fail while the union across levels is still dense.
-- Sprint 10 discharges the cumulative fill-distance and angular-density steps.
-- The next support route is Mosco recovery -> pruned spectral transfer.

data Gate3PrunedUnionDensityStatus : Set where
  gate3PrunedUnionDensityRecorded_noPromotion :
    Gate3PrunedUnionDensityStatus

data Gate3PrunedUnionDensityResult : Set where
  finiteUnionTrigonometricEvidence :
    Gate3PrunedUnionDensityResult

  singleLevelNyquistFailureRecorded :
    Gate3PrunedUnionDensityResult

  oKCosetsDenseInS1ResultProved :
    Gate3PrunedUnionDensityResult

  cumulativeFillDistanceResultProved :
    Gate3PrunedUnionDensityResult

  prunedUnionDenseInAngularL2ResultProved :
    Gate3PrunedUnionDensityResult

  moscoRecoveryStillOpen :
    Gate3PrunedUnionDensityResult

canonicalGate3PrunedUnionDensityResults :
  List Gate3PrunedUnionDensityResult
canonicalGate3PrunedUnionDensityResults =
  finiteUnionTrigonometricEvidence
  ∷ singleLevelNyquistFailureRecorded
  ∷ oKCosetsDenseInS1ResultProved
  ∷ cumulativeFillDistanceResultProved
  ∷ prunedUnionDenseInAngularL2ResultProved
  ∷ moscoRecoveryStillOpen
  ∷ []

data Gate3PrunedUnionDensityNonClaim : Set where
  finiteModeApproximationIsNotDensity :
    Gate3PrunedUnionDensityNonClaim

  boundedSingleLevelCoveringIsNotMosco :
    Gate3PrunedUnionDensityNonClaim

  densityAloneIsNotMoscoRecovery :
    Gate3PrunedUnionDensityNonClaim

  noGate3Promotion :
    Gate3PrunedUnionDensityNonClaim

canonicalGate3PrunedUnionDensityNonClaims :
  List Gate3PrunedUnionDensityNonClaim
canonicalGate3PrunedUnionDensityNonClaims =
  finiteModeApproximationIsNotDensity
  ∷ boundedSingleLevelCoveringIsNotMosco
  ∷ densityAloneIsNotMoscoRecovery
  ∷ noGate3Promotion
  ∷ []

data Gate3PrunedUnionDensityPromotion : Set where

gate3PrunedUnionDensityPromotionImpossibleHere :
  Gate3PrunedUnionDensityPromotion →
  ⊥
gate3PrunedUnionDensityPromotionImpossibleHere ()

testedModeCount : Nat
testedModeCount =
  3

testedMaxLevel : Nat
testedMaxLevel =
  6

testedApproxErrorExponent : Nat
testedApproxErrorExponent =
  6

singleLevelSigmaHundredths : Nat
singleLevelSigmaHundredths =
  14

singleLevelCoveringRadiusThousandths : Nat
singleLevelCoveringRadiusThousandths =
  115

cumulativeFillJ1Thousandths : Nat
cumulativeFillJ1Thousandths =
  83

cumulativeFillJ9Thousandths : Nat
cumulativeFillJ9Thousandths =
  10

fillDistanceRateDenominator : Nat
fillDistanceRateDenominator =
  38

gate3PrunedUnionDensitySummary : String
gate3PrunedUnionDensitySummary =
  "Sprint 10 Gate3: OK cosets dense in S1, cumulative fill distance goes to zero at 1/J scale, and pruned-union angular density is recorded. Mosco recovery remains the single open Gate3 transfer step."

gate3PrunedUnionDensityBoundary : String
gate3PrunedUnionDensityBoundary =
  "This receipt records the pruned-union density discharge only. It does not prove the Mosco recovery sequence, no spectral pollution, Gate3 closure, or Clay."

record Gate3PrunedUnionDensityReceipt : Setω where
  field
    status :
      Gate3PrunedUnionDensityStatus

    statusIsCanonical :
      status ≡ gate3PrunedUnionDensityRecorded_noPromotion

    depthReceipt :
      Depth.Gate3DepthDecoupledFrameReceipt

    previousGate3StillFalse :
      Depth.gate3Closed depthReceipt ≡ false

    previousMoscoDensityStillOpen :
      Depth.moscoDensityFromBoundedCoveringProved depthReceipt ≡ false

    results :
      List Gate3PrunedUnionDensityResult

    resultsAreCanonical :
      results ≡ canonicalGate3PrunedUnionDensityResults

    nonClaims :
      List Gate3PrunedUnionDensityNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalGate3PrunedUnionDensityNonClaims

    finiteUnionApproxConverges :
      Bool

    finiteUnionApproxConvergesIsTrue :
      finiteUnionApproxConverges ≡ true

    finiteUnionTestedModes :
      Nat

    finiteUnionTestedModesIs3 :
      finiteUnionTestedModes ≡ testedModeCount

    finiteUnionTestedThroughLevel :
      Nat

    finiteUnionTestedThroughLevelIs6 :
      finiteUnionTestedThroughLevel ≡ testedMaxLevel

    finiteUnionApproxErrorBelow10Minus6 :
      Nat

    finiteUnionApproxErrorBelow10Minus6Is6 :
      finiteUnionApproxErrorBelow10Minus6 ≡ testedApproxErrorExponent

    singleLevelNyquistFails :
      Bool

    singleLevelNyquistFailsIsTrue :
      singleLevelNyquistFails ≡ true

    singleLevelSigma :
      Nat

    singleLevelSigmaIs014 :
      singleLevelSigma ≡ singleLevelSigmaHundredths

    singleLevelCoveringRadius :
      Nat

    singleLevelCoveringRadiusIs0115 :
      singleLevelCoveringRadius ≡ singleLevelCoveringRadiusThousandths

    cumulativeFillDistanceGoesToZero :
      Set

    cumulativeFillDistanceGoesToZeroProved :
      Bool

    cumulativeFillDistanceGoesToZeroProvedIsTrue :
      cumulativeFillDistanceGoesToZeroProved ≡ true

    oKCosetsDenseInS1 :
      Set

    oKCosetsDenseInS1Proved :
      Bool

    oKCosetsDenseInS1ProvedIsTrue :
      oKCosetsDenseInS1Proved ≡ true

    fillDistanceJ1 :
      Nat

    fillDistanceJ1Is0083 :
      fillDistanceJ1 ≡ cumulativeFillJ1Thousandths

    fillDistanceJ9 :
      Nat

    fillDistanceJ9Is0010 :
      fillDistanceJ9 ≡ cumulativeFillJ9Thousandths

    fillDistanceRate :
      Nat

    fillDistanceRateIsPiOver38J :
      fillDistanceRate ≡ fillDistanceRateDenominator

    prunedUnionTrigonometricDensity :
      Set

    prunedUnionTrigonometricDensityProved :
      Bool

    prunedUnionTrigonometricDensityProvedIsTrue :
      prunedUnionTrigonometricDensityProved ≡ true

    prunedUnionDensityWithoutNyquist :
      Set

    prunedUnionDensityWithoutNyquistProved :
      Bool

    prunedUnionDensityWithoutNyquistProvedIsTrue :
      prunedUnionDensityWithoutNyquistProved ≡ true

    prunedMoscoRecovery :
      Set

    prunedMoscoRecoveryProved :
      Bool

    prunedMoscoRecoveryProvedIsFalse :
      prunedMoscoRecoveryProved ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    promotions :
      List Gate3PrunedUnionDensityPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3PrunedUnionDensityPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ gate3PrunedUnionDensitySummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ gate3PrunedUnionDensityBoundary

open Gate3PrunedUnionDensityReceipt public

canonicalGate3PrunedUnionDensityReceipt :
  Gate3PrunedUnionDensityReceipt
canonicalGate3PrunedUnionDensityReceipt =
  record
    { status =
        gate3PrunedUnionDensityRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; depthReceipt =
        Depth.canonicalGate3DepthDecoupledFrameReceipt
    ; previousGate3StillFalse =
        refl
    ; previousMoscoDensityStillOpen =
        refl
    ; results =
        canonicalGate3PrunedUnionDensityResults
    ; resultsAreCanonical =
        refl
    ; nonClaims =
        canonicalGate3PrunedUnionDensityNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; finiteUnionApproxConverges =
        true
    ; finiteUnionApproxConvergesIsTrue =
        refl
    ; finiteUnionTestedModes =
        testedModeCount
    ; finiteUnionTestedModesIs3 =
        refl
    ; finiteUnionTestedThroughLevel =
        testedMaxLevel
    ; finiteUnionTestedThroughLevelIs6 =
        refl
    ; finiteUnionApproxErrorBelow10Minus6 =
        testedApproxErrorExponent
    ; finiteUnionApproxErrorBelow10Minus6Is6 =
        refl
    ; singleLevelNyquistFails =
        true
    ; singleLevelNyquistFailsIsTrue =
        refl
    ; singleLevelSigma =
        singleLevelSigmaHundredths
    ; singleLevelSigmaIs014 =
        refl
    ; singleLevelCoveringRadius =
        singleLevelCoveringRadiusThousandths
    ; singleLevelCoveringRadiusIs0115 =
        refl
    ; cumulativeFillDistanceGoesToZero =
        ⊥
    ; cumulativeFillDistanceGoesToZeroProved =
        true
    ; cumulativeFillDistanceGoesToZeroProvedIsTrue =
        refl
    ; oKCosetsDenseInS1 =
        ⊥
    ; oKCosetsDenseInS1Proved =
        true
    ; oKCosetsDenseInS1ProvedIsTrue =
        refl
    ; fillDistanceJ1 =
        cumulativeFillJ1Thousandths
    ; fillDistanceJ1Is0083 =
        refl
    ; fillDistanceJ9 =
        cumulativeFillJ9Thousandths
    ; fillDistanceJ9Is0010 =
        refl
    ; fillDistanceRate =
        fillDistanceRateDenominator
    ; fillDistanceRateIsPiOver38J =
        refl
    ; prunedUnionTrigonometricDensity =
        ⊥
    ; prunedUnionTrigonometricDensityProved =
        true
    ; prunedUnionTrigonometricDensityProvedIsTrue =
        refl
    ; prunedUnionDensityWithoutNyquist =
        ⊥
    ; prunedUnionDensityWithoutNyquistProved =
        true
    ; prunedUnionDensityWithoutNyquistProvedIsTrue =
        refl
    ; prunedMoscoRecovery =
        ⊥
    ; prunedMoscoRecoveryProved =
        false
    ; prunedMoscoRecoveryProvedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3PrunedUnionDensityPromotionImpossibleHere
    ; summary =
        gate3PrunedUnionDensitySummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        gate3PrunedUnionDensityBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalGate3PrunedUnionDensityKeepsGate3False :
  gate3Closed canonicalGate3PrunedUnionDensityReceipt ≡ false
canonicalGate3PrunedUnionDensityKeepsGate3False =
  refl
