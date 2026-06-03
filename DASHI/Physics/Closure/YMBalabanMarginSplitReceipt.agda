module DASHI.Physics.Closure.YMBalabanMarginSplitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayOptimalKernelLemmaReceipt as Optimal
import DASHI.Physics.Closure.YMBalabanPhysicalBetaBridgeTargetReceipt
  as Bridge
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt
  as Frontier

------------------------------------------------------------------------
-- Yang-Mills Balaban margin split.
--
-- Concrete YM worker receipt.  It prevents the connected-animal KP threshold,
-- BT-tree convergence margin, strict Balaban seed margin, and demoted T7A
-- direct-count route from being used interchangeably.

data YMBalabanMarginSplitStatus : Set where
  ymBalabanMarginSplitRecorded_noPromotion :
    YMBalabanMarginSplitStatus

data YMBalabanRouteMargin : Set where
  connectedAnimalKPConvergenceRoute :
    YMBalabanRouteMargin

  btTreeConvergenceRoute :
    YMBalabanRouteMargin

  strictBalabanSeedRoute :
    YMBalabanRouteMargin

  t7aDirectCountingDemotedRoute :
    YMBalabanRouteMargin

canonicalYMBalabanRouteMargins : List YMBalabanRouteMargin
canonicalYMBalabanRouteMargins =
  connectedAnimalKPConvergenceRoute
  ∷ btTreeConvergenceRoute
  ∷ strictBalabanSeedRoute
  ∷ t7aDirectCountingDemotedRoute
  ∷ []

data YMBalabanTransferSublemma : Set where
  strictKPSeedAtActiveMargin :
    YMBalabanTransferSublemma

  uniformVolumeKPSeed :
    YMBalabanTransferSublemma

  balabanBlockSpinMapExists :
    YMBalabanTransferSublemma

  ultrametricLargeSmallFieldSplit :
    YMBalabanTransferSublemma

  effectiveBetaMonotonicity :
    YMBalabanTransferSublemma

  balabanContractionRhoLtOne :
    YMBalabanTransferSublemma

canonicalYMBalabanTransferSublemmas : List YMBalabanTransferSublemma
canonicalYMBalabanTransferSublemmas =
  strictKPSeedAtActiveMargin
  ∷ uniformVolumeKPSeed
  ∷ balabanBlockSpinMapExists
  ∷ ultrametricLargeSmallFieldSplit
  ∷ effectiveBetaMonotonicity
  ∷ balabanContractionRhoLtOne
  ∷ []

data YMBalabanMarginNonClaim : Set where
  connectedAnimalConvergenceIsNotStrictSeed :
    YMBalabanMarginNonClaim

  legacyStrict1297IsNotActiveSafe1364 :
    YMBalabanMarginNonClaim

  t7aDirectCountingIsNotPrimaryRoute :
    YMBalabanMarginNonClaim

  perturbativeRunningIsNotBalabanBridge :
    YMBalabanMarginNonClaim

  noClayPromotion :
    YMBalabanMarginNonClaim

canonicalYMBalabanMarginNonClaims : List YMBalabanMarginNonClaim
canonicalYMBalabanMarginNonClaims =
  connectedAnimalConvergenceIsNotStrictSeed
  ∷ legacyStrict1297IsNotActiveSafe1364
  ∷ t7aDirectCountingIsNotPrimaryRoute
  ∷ perturbativeRunningIsNotBalabanBridge
  ∷ noClayPromotion
  ∷ []

data YMBalabanMarginPromotion : Set where

ymBalabanMarginPromotionImpossibleHere :
  YMBalabanMarginPromotion →
  ⊥
ymBalabanMarginPromotionImpossibleHere ()

connectedAnimalThresholdHundredths : Nat
connectedAnimalThresholdHundredths =
  959

connectedAnimalThresholdMillionths : Nat
connectedAnimalThresholdMillionths =
  9593637

btTreeThresholdHundredths : Nat
btTreeThresholdHundredths =
  1013

btTreeThresholdMillionths : Nat
btTreeThresholdMillionths =
  10130860

legacyBridgeStrictThresholdHundredths : Nat
legacyBridgeStrictThresholdHundredths =
  1297

activeSafeStrictThresholdHundredths : Nat
activeSafeStrictThresholdHundredths =
  1364

strictAbsorptionThresholdMillionths : Nat
strictAbsorptionThresholdMillionths =
  13631603

strictAbsorptionSafeSampleTenths : Nat
strictAbsorptionSafeSampleTenths =
  137

t7aDirectThresholdHundredths : Nat
t7aDirectThresholdHundredths =
  1656

physicalBetaHundredths : Nat
physicalBetaHundredths =
  600

strictSafeGapHundredths : Nat
strictSafeGapHundredths =
  764

strictAbsorptionGapMillionths : Nat
strictAbsorptionGapMillionths =
  7631603

strictSafeSampleMinusThresholdMillionths : Nat
strictSafeSampleMinusThresholdMillionths =
  8397

ymBalabanMarginSplitSummary : String
ymBalabanMarginSplitSummary =
  "YM Balaban margin split: beta_eff > 9.593637 is connected-animal KP convergence, beta_eff > 10.13086 is p=7 BT-tree convergence, beta_eff must satisfy beta*c_min-a>log(2p) for strict Balaban seeding, and beta_eff > 16.56 is demoted direct T7A counting."

ymBalabanMarginSplitBoundary : String
ymBalabanMarginSplitBoundary =
  "This receipt proves no nonperturbative Balaban transfer. It records the active margin convention and blocks using 9.59 convergence or legacy 12.97 strict context as the 13.64 safe Balaban seed."

strictBalabanSeedExactStatement : String
strictBalabanSeedExactStatement =
  "StrictBalabanSeed exact target: beta_eff*c_min - a > log(2*p). With c_min=0.198, a=0.06, and p=7, beta_strict ~= 13.631603; beta=13.64 is barely safe and beta>=13.7 is the robust numeric sample."

record YMBalabanMarginSplitReceipt : Setω where
  field
    status :
      YMBalabanMarginSplitStatus

    statusIsCanonical :
      status ≡ ymBalabanMarginSplitRecorded_noPromotion

    optimalKernelReceipt :
      Optimal.ClayOptimalKernelLemmaReceipt

    optimalConnectedThreshold :
      Optimal.connectedAnimalThreshold optimalKernelReceipt
      ≡
      Optimal.connectedAnimalThresholdHundredths

    optimalBTTreeThreshold :
      Optimal.btTreeThreshold optimalKernelReceipt
      ≡
      Optimal.btTreeThresholdHundredths

    optimalStrictMargin :
      Optimal.strictKPMarginThreshold optimalKernelReceipt
      ≡
      Optimal.strictKPMarginThresholdHundredths

    optimalT7ADemoted :
      Optimal.ymT7ADirectCountingDemoted optimalKernelReceipt ≡ true

    bridgeTargetReceipt :
      Bridge.YMBalabanPhysicalBetaBridgeTargetReceipt

    bridgeNonperturbativeRequired :
      Bridge.nonperturbativeInputRequired bridgeTargetReceipt ≡ true

    bridgeProvedHereFalse :
      Bridge.physicalBetaBridgeProvedHere bridgeTargetReceipt ≡ false

    bridgeNoClay :
      Bridge.clayYangMillsPromoted bridgeTargetReceipt ≡ false

    frontierReceipt :
      Frontier.YMBalabanRGScaleTransferFrontierReceipt

    frontierBridgeRequired :
      Frontier.bridgeVerdict frontierReceipt
      ≡
      Frontier.nonperturbativeBridgeRequired

    frontierProofAbsent :
      Frontier.balabanRGProofPresent frontierReceipt ≡ false

    frontierNoClay :
      Frontier.clayYangMillsPromoted frontierReceipt ≡ false

    routeMargins :
      List YMBalabanRouteMargin

    routeMarginsAreCanonical :
      routeMargins ≡ canonicalYMBalabanRouteMargins

    transferSublemmas :
      List YMBalabanTransferSublemma

    transferSublemmasAreCanonical :
      transferSublemmas ≡ canonicalYMBalabanTransferSublemmas

    nonClaims :
      List YMBalabanMarginNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMBalabanMarginNonClaims

    physicalBeta :
      Nat

    physicalBetaIs600 :
      physicalBeta ≡ physicalBetaHundredths

    connectedAnimalThreshold :
      Nat

    connectedAnimalThresholdIs959 :
      connectedAnimalThreshold ≡ connectedAnimalThresholdHundredths

    connectedAnimalThresholdPrecise :
      Nat

    connectedAnimalThresholdPreciseIs9593637 :
      connectedAnimalThresholdPrecise ≡ connectedAnimalThresholdMillionths

    btTreeThreshold :
      Nat

    btTreeThresholdIs1013 :
      btTreeThreshold ≡ btTreeThresholdHundredths

    btTreeThresholdPrecise :
      Nat

    btTreeThresholdPreciseIs10130860 :
      btTreeThresholdPrecise ≡ btTreeThresholdMillionths

    legacyBridgeStrictThreshold :
      Nat

    legacyBridgeStrictThresholdIs1297 :
      legacyBridgeStrictThreshold ≡ legacyBridgeStrictThresholdHundredths

    activeSafeStrictThreshold :
      Nat

    activeSafeStrictThresholdIs1364 :
      activeSafeStrictThreshold ≡ activeSafeStrictThresholdHundredths

    strictAbsorptionThresholdPrecise :
      Nat

    strictAbsorptionThresholdPreciseIs13631603 :
      strictAbsorptionThresholdPrecise ≡
      strictAbsorptionThresholdMillionths

    strictAbsorptionSafeSample :
      Nat

    strictAbsorptionSafeSampleIs137 :
      strictAbsorptionSafeSample ≡ strictAbsorptionSafeSampleTenths

    t7aDirectThreshold :
      Nat

    t7aDirectThresholdIs1656 :
      t7aDirectThreshold ≡ t7aDirectThresholdHundredths

    strictSafeGap :
      Nat

    strictSafeGapIs764 :
      strictSafeGap ≡ strictSafeGapHundredths

    strictAbsorptionGapPrecise :
      Nat

    strictAbsorptionGapPreciseIs7631603 :
      strictAbsorptionGapPrecise ≡ strictAbsorptionGapMillionths

    strictSafeSampleMargin :
      Nat

    strictSafeSampleMarginIs8397 :
      strictSafeSampleMargin ≡ strictSafeSampleMinusThresholdMillionths

    connectedAnimalRouteStandard :
      Bool

    connectedAnimalRouteStandardIsTrue :
      connectedAnimalRouteStandard ≡ true

    strictAbsorptionRequiredForBalabanSeed :
      Bool

    strictAbsorptionRequiredForBalabanSeedIsTrue :
      strictAbsorptionRequiredForBalabanSeed ≡ true

    activeSafeMarginIs1364 :
      Bool

    activeSafeMarginIs1364IsTrue :
      activeSafeMarginIs1364 ≡ true

    legacy1297PromotedToActiveSafeMargin :
      Bool

    legacy1297PromotedToActiveSafeMarginIsFalse :
      legacy1297PromotedToActiveSafeMargin ≡ false

    t7aDirectCountingDemoted :
      Bool

    t7aDirectCountingDemotedIsTrue :
      t7aDirectCountingDemoted ≡ true

    t7aAllowedOnlyAsActivitySuppression :
      Bool

    t7aAllowedOnlyAsActivitySuppressionIsTrue :
      t7aAllowedOnlyAsActivitySuppression ≡ true

    balabanTransferProvedHere :
      Bool

    balabanTransferProvedHereIsFalse :
      balabanTransferProvedHere ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List YMBalabanMarginPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      YMBalabanMarginPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ ymBalabanMarginSplitSummary

    strictSeedExactText :
      String

    strictSeedExactTextIsCanonical :
      strictSeedExactText ≡ strictBalabanSeedExactStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ ymBalabanMarginSplitBoundary

open YMBalabanMarginSplitReceipt public

canonicalYMBalabanMarginSplitReceipt :
  YMBalabanMarginSplitReceipt
canonicalYMBalabanMarginSplitReceipt =
  record
    { status =
        ymBalabanMarginSplitRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; optimalKernelReceipt =
        Optimal.canonicalClayOptimalKernelLemmaReceipt
    ; optimalConnectedThreshold =
        refl
    ; optimalBTTreeThreshold =
        refl
    ; optimalStrictMargin =
        refl
    ; optimalT7ADemoted =
        refl
    ; bridgeTargetReceipt =
        Bridge.canonicalYMBalabanPhysicalBetaBridgeTargetReceipt
    ; bridgeNonperturbativeRequired =
        refl
    ; bridgeProvedHereFalse =
        refl
    ; bridgeNoClay =
        refl
    ; frontierReceipt =
        Frontier.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; frontierBridgeRequired =
        refl
    ; frontierProofAbsent =
        refl
    ; frontierNoClay =
        refl
    ; routeMargins =
        canonicalYMBalabanRouteMargins
    ; routeMarginsAreCanonical =
        refl
    ; transferSublemmas =
        canonicalYMBalabanTransferSublemmas
    ; transferSublemmasAreCanonical =
        refl
    ; nonClaims =
        canonicalYMBalabanMarginNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; physicalBeta =
        physicalBetaHundredths
    ; physicalBetaIs600 =
        refl
    ; connectedAnimalThreshold =
        connectedAnimalThresholdHundredths
    ; connectedAnimalThresholdIs959 =
        refl
    ; connectedAnimalThresholdPrecise =
        connectedAnimalThresholdMillionths
    ; connectedAnimalThresholdPreciseIs9593637 =
        refl
    ; btTreeThreshold =
        btTreeThresholdHundredths
    ; btTreeThresholdIs1013 =
        refl
    ; btTreeThresholdPrecise =
        btTreeThresholdMillionths
    ; btTreeThresholdPreciseIs10130860 =
        refl
    ; legacyBridgeStrictThreshold =
        legacyBridgeStrictThresholdHundredths
    ; legacyBridgeStrictThresholdIs1297 =
        refl
    ; activeSafeStrictThreshold =
        activeSafeStrictThresholdHundredths
    ; activeSafeStrictThresholdIs1364 =
        refl
    ; strictAbsorptionThresholdPrecise =
        strictAbsorptionThresholdMillionths
    ; strictAbsorptionThresholdPreciseIs13631603 =
        refl
    ; strictAbsorptionSafeSample =
        strictAbsorptionSafeSampleTenths
    ; strictAbsorptionSafeSampleIs137 =
        refl
    ; t7aDirectThreshold =
        t7aDirectThresholdHundredths
    ; t7aDirectThresholdIs1656 =
        refl
    ; strictSafeGap =
        strictSafeGapHundredths
    ; strictSafeGapIs764 =
        refl
    ; strictAbsorptionGapPrecise =
        strictAbsorptionGapMillionths
    ; strictAbsorptionGapPreciseIs7631603 =
        refl
    ; strictSafeSampleMargin =
        strictSafeSampleMinusThresholdMillionths
    ; strictSafeSampleMarginIs8397 =
        refl
    ; connectedAnimalRouteStandard =
        true
    ; connectedAnimalRouteStandardIsTrue =
        refl
    ; strictAbsorptionRequiredForBalabanSeed =
        true
    ; strictAbsorptionRequiredForBalabanSeedIsTrue =
        refl
    ; activeSafeMarginIs1364 =
        true
    ; activeSafeMarginIs1364IsTrue =
        refl
    ; legacy1297PromotedToActiveSafeMargin =
        false
    ; legacy1297PromotedToActiveSafeMarginIsFalse =
        refl
    ; t7aDirectCountingDemoted =
        true
    ; t7aDirectCountingDemotedIsTrue =
        refl
    ; t7aAllowedOnlyAsActivitySuppression =
        true
    ; t7aAllowedOnlyAsActivitySuppressionIsTrue =
        refl
    ; balabanTransferProvedHere =
        false
    ; balabanTransferProvedHereIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        ymBalabanMarginPromotionImpossibleHere
    ; summary =
        ymBalabanMarginSplitSummary
    ; summaryIsCanonical =
        refl
    ; strictSeedExactText =
        strictBalabanSeedExactStatement
    ; strictSeedExactTextIsCanonical =
        refl
    ; boundary =
        ymBalabanMarginSplitBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalYMBalabanTransferStillOpen :
  balabanTransferProvedHere canonicalYMBalabanMarginSplitReceipt ≡ false
canonicalYMBalabanTransferStillOpen =
  refl
