module DASHI.Physics.Closure.YMBetaBridgeQuantitativeGapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMPhysicalBetaBridgeOpenReceipt as Bridge
import DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt as Threshold
import DASHI.Physics.Closure.YMPaper3ClayTargetReceipt as Paper3

------------------------------------------------------------------------
-- Quantitative physical beta bridge receipt.
--
-- This module records the nonperturbative nature of the remaining YM bridge.
-- It does not prove a Balaban bridge.  It quantifies why the physical beta
-- gap cannot be closed by a naive perturbative iteration.

data YMBetaBridgeQuantitativeStatus : Set where
  betaBridgeQuantified_nonperturbativeInputRequired :
    YMBetaBridgeQuantitativeStatus

data YMBetaBridgeKnownWindow : Set where
  physicalBetaSixDivergent :
    YMBetaBridgeKnownWindow

  convergenceWindowAtTenPointEleven :
    YMBetaBridgeKnownWindow

  strictAbsorptionWindowAtTwelvePointNinetySeven :
    YMBetaBridgeKnownWindow

canonicalYMBetaBridgeKnownWindows :
  List YMBetaBridgeKnownWindow
canonicalYMBetaBridgeKnownWindows =
  physicalBetaSixDivergent
  ∷ convergenceWindowAtTenPointEleven
  ∷ strictAbsorptionWindowAtTwelvePointNinetySeven
  ∷ []

data YMBetaBridgeAttackRoute : Set where
  strongCouplingExpansionAreaLaw :
    YMBetaBridgeAttackRoute

  balabanBlockSpinCrossover :
    YMBetaBridgeAttackRoute

  nonperturbativeLargeFieldSuppression :
    YMBetaBridgeAttackRoute

canonicalYMBetaBridgeAttackRoute :
  List YMBetaBridgeAttackRoute
canonicalYMBetaBridgeAttackRoute =
  strongCouplingExpansionAreaLaw
  ∷ balabanBlockSpinCrossover
  ∷ nonperturbativeLargeFieldSuppression
  ∷ []

data YMBetaBridgeOpenObligation : Set where
  proveRGFlowConnectsPhysicalToCarrierSafeWindow :
    YMBetaBridgeOpenObligation

  controlPolymerActivitiesThroughCrossover :
    YMBetaBridgeOpenObligation

  preserveReflectionPositivityAndContinuumConstruction :
    YMBetaBridgeOpenObligation

canonicalYMBetaBridgeOpenObligations :
  List YMBetaBridgeOpenObligation
canonicalYMBetaBridgeOpenObligations =
  proveRGFlowConnectsPhysicalToCarrierSafeWindow
  ∷ controlPolymerActivitiesThroughCrossover
  ∷ preserveReflectionPositivityAndContinuumConstruction
  ∷ []

data YMBetaBridgePromotion : Set where

ymBetaBridgePromotionImpossibleHere :
  YMBetaBridgePromotion →
  ⊥
ymBetaBridgePromotionImpossibleHere ()

betaPhysicalHundredths :
  Nat
betaPhysicalHundredths =
  600

betaConvergenceHundredths :
  Nat
betaConvergenceHundredths =
  1011

betaStrictAbsorptionHundredths :
  Nat
betaStrictAbsorptionHundredths =
  1297

gapToConvergenceHundredths :
  Nat
gapToConvergenceHundredths =
  411

gapToStrictHundredths :
  Nat
gapToStrictHundredths =
  697

oneLoopB0TenThousandths :
  Nat
oneLoopB0TenThousandths =
  465

perturbativeExponentApprox :
  Nat
perturbativeExponentApprox =
  150

naiveScaleFactorPowerOfTen :
  Nat
naiveScaleFactorPowerOfTen =
  65

quantitativeGapStatement :
  String
quantitativeGapStatement =
  "At beta_phys ~= 6, the p=7 KP ratio is divergent; strict carrier absorption starts near beta ~= 12.97, leaving a gap ~= 6.97.  With b0 ~= 0.0465, a naive perturbative bridge is exp(150) ~= 10^65, so the bridge requires nonperturbative input."

promotionBoundary :
  String
promotionBoundary =
  "This receipt quantifies the beta gap only. It does not prove RGFlowConnects beta_phys beta_carrier, carrier area law at physical beta, continuum YM, a mass gap, or Clay Yang-Mills."

record YMBetaBridgeQuantitativeGapReceipt : Setω where
  field
    status :
      YMBetaBridgeQuantitativeStatus

    statusIsCanonical :
      status ≡ betaBridgeQuantified_nonperturbativeInputRequired

    physicalBetaBridgeReceipt :
      Bridge.YMPhysicalBetaBridgeOpenReceipt

    physicalBetaBridgeStillOpen :
      Bridge.physicalBridgeClosed physicalBetaBridgeReceipt ≡ false

    physicalBetaBridgeNoClay :
      Bridge.clayYangMillsPromoted physicalBetaBridgeReceipt ≡ false

    thresholdReceipt :
      Threshold.YMKPThresholdCorrectionReceipt

    paper3Receipt :
      Paper3.YMPaper3ClayTargetReceipt

    paper3NoClay :
      Paper3.clayYMMassGapPromoted paper3Receipt ≡ false

    knownWindows :
      List YMBetaBridgeKnownWindow

    knownWindowsAreCanonical :
      knownWindows ≡ canonicalYMBetaBridgeKnownWindows

    attackRoute :
      List YMBetaBridgeAttackRoute

    attackRouteIsCanonical :
      attackRoute ≡ canonicalYMBetaBridgeAttackRoute

    openObligations :
      List YMBetaBridgeOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMBetaBridgeOpenObligations

    betaPhysical :
      Nat

    betaPhysicalIsSixHundredths :
      betaPhysical ≡ betaPhysicalHundredths

    betaConvergence :
      Nat

    betaConvergenceIsTenElevenHundredths :
      betaConvergence ≡ betaConvergenceHundredths

    betaStrictAbsorption :
      Nat

    betaStrictAbsorptionIsTwelveNinetySevenHundredths :
      betaStrictAbsorption ≡ betaStrictAbsorptionHundredths

    gapToConvergence :
      Nat

    gapToConvergenceIsFourElevenHundredths :
      gapToConvergence ≡ gapToConvergenceHundredths

    gapToStrict :
      Nat

    gapToStrictIsSixNinetySevenHundredths :
      gapToStrict ≡ gapToStrictHundredths

    b0 :
      Nat

    b0Is0465 :
      b0 ≡ oneLoopB0TenThousandths

    perturbativeExponent :
      Nat

    perturbativeExponentIs150 :
      perturbativeExponent ≡ perturbativeExponentApprox

    naivePowerOfTen :
      Nat

    naivePowerOfTenIs65 :
      naivePowerOfTen ≡ naiveScaleFactorPowerOfTen

    perturbativeBridgeSuffices :
      Bool

    perturbativeBridgeSufficesIsFalse :
      perturbativeBridgeSuffices ≡ false

    nonperturbativeInputRequired :
      Bool

    nonperturbativeInputRequiredIsTrue :
      nonperturbativeInputRequired ≡ true

    physicalBetaBridgeProvedHere :
      Bool

    physicalBetaBridgeProvedHereIsFalse :
      physicalBetaBridgeProvedHere ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    promotions :
      List YMBetaBridgePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      YMBetaBridgePromotion →
      ⊥

    statement :
      String

    statementIsCanonical :
      statement ≡ quantitativeGapStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open YMBetaBridgeQuantitativeGapReceipt public

canonicalYMBetaBridgeQuantitativeGapReceipt :
  YMBetaBridgeQuantitativeGapReceipt
canonicalYMBetaBridgeQuantitativeGapReceipt =
  record
    { status =
        betaBridgeQuantified_nonperturbativeInputRequired
    ; statusIsCanonical =
        refl
    ; physicalBetaBridgeReceipt =
        Bridge.canonicalYMPhysicalBetaBridgeOpenReceipt
    ; physicalBetaBridgeStillOpen =
        refl
    ; physicalBetaBridgeNoClay =
        refl
    ; thresholdReceipt =
        Threshold.canonicalYMKPThresholdCorrectionReceipt
    ; paper3Receipt =
        Paper3.canonicalYMPaper3ClayTargetReceipt
    ; paper3NoClay =
        refl
    ; knownWindows =
        canonicalYMBetaBridgeKnownWindows
    ; knownWindowsAreCanonical =
        refl
    ; attackRoute =
        canonicalYMBetaBridgeAttackRoute
    ; attackRouteIsCanonical =
        refl
    ; openObligations =
        canonicalYMBetaBridgeOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; betaPhysical =
        betaPhysicalHundredths
    ; betaPhysicalIsSixHundredths =
        refl
    ; betaConvergence =
        betaConvergenceHundredths
    ; betaConvergenceIsTenElevenHundredths =
        refl
    ; betaStrictAbsorption =
        betaStrictAbsorptionHundredths
    ; betaStrictAbsorptionIsTwelveNinetySevenHundredths =
        refl
    ; gapToConvergence =
        gapToConvergenceHundredths
    ; gapToConvergenceIsFourElevenHundredths =
        refl
    ; gapToStrict =
        gapToStrictHundredths
    ; gapToStrictIsSixNinetySevenHundredths =
        refl
    ; b0 =
        oneLoopB0TenThousandths
    ; b0Is0465 =
        refl
    ; perturbativeExponent =
        perturbativeExponentApprox
    ; perturbativeExponentIs150 =
        refl
    ; naivePowerOfTen =
        naiveScaleFactorPowerOfTen
    ; naivePowerOfTenIs65 =
        refl
    ; perturbativeBridgeSuffices =
        false
    ; perturbativeBridgeSufficesIsFalse =
        refl
    ; nonperturbativeInputRequired =
        true
    ; nonperturbativeInputRequiredIsTrue =
        refl
    ; physicalBetaBridgeProvedHere =
        false
    ; physicalBetaBridgeProvedHereIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        ymBetaBridgePromotionImpossibleHere
    ; statement =
        quantitativeGapStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalYMBetaBridgeRequiresNonperturbativeInput :
  nonperturbativeInputRequired canonicalYMBetaBridgeQuantitativeGapReceipt
  ≡
  true
canonicalYMBetaBridgeRequiresNonperturbativeInput =
  refl

canonicalYMBetaBridgeNoClayPromotion :
  clayYMPromoted canonicalYMBetaBridgeQuantitativeGapReceipt ≡ false
canonicalYMBetaBridgeNoClayPromotion =
  refl
