module DASHI.Physics.Closure.YMC0EntropyThresholdSensitivityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MonsterMoonshineSSPQuotientControlReceipt
  as MonsterQuotient
import DASHI.Physics.Closure.YMBalabanPhysicalBetaBridgeTargetReceipt as Bridge
import DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt as Threshold

------------------------------------------------------------------------
-- YM C0 entropy threshold sensitivity receipt.
--
-- The strict KP absorption threshold is materially sensitive to the entropy
-- constant C0:
--
--   beta_abs(C0) = (a + log(2 p C0)) / c_min
--
-- with p=7, a=0.5, c_min=0.242.  This receipt records the recalculated
-- threshold table and the Monster q^2 stress test.  Raw Monster
-- representation multiplicity is not licensed as physical polymer entropy;
-- the 15SSP/moonshine quotient theorem is load-bearing.

data YMC0EntropyThresholdSensitivityStatus : Set where
  ymC0EntropyThresholdSensitivityRecorded_noPromotion :
    YMC0EntropyThresholdSensitivityStatus

data YMC0SensitivityDatum : Set where
  c0HalfAbsorptionBeta10107 :
    YMC0SensitivityDatum

  c0OneAbsorptionBeta12971 :
    YMC0SensitivityDatum

  c0TwoAbsorptionBeta15836 :
    YMC0SensitivityDatum

  c0FiveAbsorptionBeta19622 :
    YMC0SensitivityDatum

  monsterSqrtLeakAbsorptionBeta2266 :
    YMC0SensitivityDatum

  monsterRawLeakAbsorptionBeta3235 :
    YMC0SensitivityDatum

canonicalYMC0SensitivityData :
  List YMC0SensitivityDatum
canonicalYMC0SensitivityData =
  c0HalfAbsorptionBeta10107
  ∷ c0OneAbsorptionBeta12971
  ∷ c0TwoAbsorptionBeta15836
  ∷ c0FiveAbsorptionBeta19622
  ∷ monsterSqrtLeakAbsorptionBeta2266
  ∷ monsterRawLeakAbsorptionBeta3235
  ∷ []

data YMC0OpenObligation : Set where
  determineActualPolymerEntropyConstant :
    YMC0OpenObligation

  proveMonsterMultiplicityIsQuotientedBeforeYMActivity :
    YMC0OpenObligation

  proveEffectiveC0NearOneForSSPHeckeOrbitClasses :
    YMC0OpenObligation

  provePhysicalBetaBridgeWithActualC0 :
    YMC0OpenObligation

canonicalYMC0OpenObligations :
  List YMC0OpenObligation
canonicalYMC0OpenObligations =
  determineActualPolymerEntropyConstant
  ∷ proveMonsterMultiplicityIsQuotientedBeforeYMActivity
  ∷ proveEffectiveC0NearOneForSSPHeckeOrbitClasses
  ∷ provePhysicalBetaBridgeWithActualC0
  ∷ []

data YMC0EntropyPromotion : Set where

ymC0EntropyPromotionImpossibleHere :
  YMC0EntropyPromotion →
  ⊥
ymC0EntropyPromotionImpossibleHere ()

c0HalfBetaAbsThousandths :
  Nat
c0HalfBetaAbsThousandths =
  10107

c0HalfGapThousandths :
  Nat
c0HalfGapThousandths =
  4107

c0OneBetaAbsThousandths :
  Nat
c0OneBetaAbsThousandths =
  12971

c0TwoBetaAbsThousandths :
  Nat
c0TwoBetaAbsThousandths =
  15836

c0TwoGapThousandths :
  Nat
c0TwoGapThousandths =
  9836

c0FiveBetaAbsThousandths :
  Nat
c0FiveBetaAbsThousandths =
  19622

c0OneGapThousandths :
  Nat
c0OneGapThousandths =
  6971

c0FiveGapThousandths :
  Nat
c0FiveGapThousandths =
  13622

recordedPBranching :
  Nat
recordedPBranching =
  7

recordedAWeightNumerator :
  Nat
recordedAWeightNumerator =
  50

recordedAWeightDenominator :
  Nat
recordedAWeightDenominator =
  100

recordedCMinNumerator :
  Nat
recordedCMinNumerator =
  242

recordedCMinDenominator :
  Nat
recordedCMinDenominator =
  1000

monsterC1 :
  Nat
monsterC1 =
  196884

monsterC2 :
  Nat
monsterC2 =
  21493760

monsterRawRatioHundredths :
  Nat
monsterRawRatioHundredths =
  10917

monsterSqrtRatioHundredths :
  Nat
monsterSqrtRatioHundredths =
  1045

monsterRawRatioApprox :
  Nat
monsterRawRatioApprox =
  109

monsterSqrtLeakBetaAbsHundredths :
  Nat
monsterSqrtLeakBetaAbsHundredths =
  2266

monsterRawLeakBetaAbsHundredths :
  Nat
monsterRawLeakBetaAbsHundredths =
  3235

c0SensitivityStatement :
  String
c0SensitivityStatement =
  "YM beta_abs(C0) is load-bearing: C0=0.5 gives 10.107, C0=1 gives 12.971, C0=2 gives 15.836, C0=5 gives 19.622."

monsterStressStatement :
  String
monsterStressStatement =
  "If Monster q^2 multiplicity leaks into C0, beta_abs rises to about 22.66 for sqrt(c2/c1) and about 32.35 for raw c2/c1.  The 15SSP quotient must prevent that leak."

promotionBoundary :
  String
promotionBoundary =
  "This receipt records C0 sensitivity only.  It does not prove the quotient entropy bound, actual physical beta bridge, continuum mass gap, or Clay Yang-Mills."

record YMC0EntropyThresholdSensitivityReceipt : Setω where
  field
    status :
      YMC0EntropyThresholdSensitivityStatus

    statusIsCanonical :
      status ≡ ymC0EntropyThresholdSensitivityRecorded_noPromotion

    thresholdReceipt :
      Threshold.YMKPThresholdCorrectionReceipt

    pBranching :
      Nat

    pBranchingIs7 :
      pBranching ≡ recordedPBranching

    thresholdPBranchingMatches :
      Threshold.pBranching ≡ pBranching

    aWeightNumerator :
      Nat

    aWeightNumeratorIs50 :
      aWeightNumerator ≡ recordedAWeightNumerator

    thresholdAWeightNumeratorMatches :
      Threshold.aWeightNumerator ≡ aWeightNumerator

    aWeightDenominator :
      Nat

    aWeightDenominatorIs100 :
      aWeightDenominator ≡ recordedAWeightDenominator

    thresholdAWeightDenominatorMatches :
      Threshold.aWeightDenominator ≡ aWeightDenominator

    cMinNumerator :
      Nat

    cMinNumeratorIs242 :
      cMinNumerator ≡ recordedCMinNumerator

    thresholdCMinNumeratorMatches :
      Threshold.cMinPhysicalNumerator ≡ cMinNumerator

    cMinDenominator :
      Nat

    cMinDenominatorIs1000 :
      cMinDenominator ≡ recordedCMinDenominator

    thresholdCMinDenominatorMatches :
      Threshold.cMinPhysicalDenominator ≡ cMinDenominator

    thresholdNoClay :
      Threshold.clayYMPromoted thresholdReceipt ≡ false

    betaBridgeReceipt :
      Bridge.YMBalabanPhysicalBetaBridgeTargetReceipt

    betaBridgeStillOpen :
      Bridge.physicalBetaBridgeProvedHere betaBridgeReceipt ≡ false

    betaBridgeNoClay :
      Bridge.clayYangMillsPromoted betaBridgeReceipt ≡ false

    monsterQuotientReceipt :
      MonsterQuotient.MonsterMoonshineSSPQuotientControlReceipt

    monsterQuotientStillOpen :
      MonsterQuotient.quotientEntropyBoundProvedHere
        monsterQuotientReceipt
      ≡
      false

    monsterRawMultiplicityNotC0 :
      MonsterQuotient.rawMultiplicityIsPhysicalPolymerEntropy
        monsterQuotientReceipt
      ≡
      false

    monsterC1Coefficient :
      Nat

    monsterC1CoefficientIs196884 :
      monsterC1Coefficient ≡ monsterC1

    monsterC1MatchesReceipt :
      MonsterQuotient.c1 monsterQuotientReceipt ≡ monsterC1Coefficient

    monsterC2Coefficient :
      Nat

    monsterC2CoefficientIs21493760 :
      monsterC2Coefficient ≡ monsterC2

    monsterC2MatchesReceipt :
      MonsterQuotient.c2 monsterQuotientReceipt ≡ monsterC2Coefficient

    monsterRawRatioApprox10917Hundredths :
      Nat

    monsterRawRatioApprox10917HundredthsIsCanonical :
      monsterRawRatioApprox10917Hundredths ≡ monsterRawRatioHundredths

    monsterRawRatioApproxRounded :
      Nat

    monsterRawRatioApproxRoundedIs109 :
      monsterRawRatioApproxRounded ≡ monsterRawRatioApprox

    monsterRawRatioRoundedMatchesReceipt :
      MonsterQuotient.rawRatio monsterQuotientReceipt
      ≡
      monsterRawRatioApproxRounded

    monsterSqrtRatioApprox1045Hundredths :
      Nat

    monsterSqrtRatioApprox1045HundredthsIsCanonical :
      monsterSqrtRatioApprox1045Hundredths ≡ monsterSqrtRatioHundredths

    monsterSqrtRatioMatchesReceipt :
      MonsterQuotient.sqrtRawRatio monsterQuotientReceipt
      ≡
      monsterSqrtRatioApprox1045Hundredths

    sensitivityData :
      List YMC0SensitivityDatum

    sensitivityDataAreCanonical :
      sensitivityData ≡ canonicalYMC0SensitivityData

    openObligations :
      List YMC0OpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMC0OpenObligations

    c0HalfBetaAbs :
      Nat

    c0HalfBetaAbsIs10107 :
      c0HalfBetaAbs ≡ c0HalfBetaAbsThousandths

    c0HalfGapFromBeta6 :
      Nat

    c0HalfGapFromBeta6Is4107 :
      c0HalfGapFromBeta6 ≡ c0HalfGapThousandths

    c0OneBetaAbs :
      Nat

    c0OneBetaAbsIs12971 :
      c0OneBetaAbs ≡ c0OneBetaAbsThousandths

    c0TwoBetaAbs :
      Nat

    c0TwoBetaAbsIs15836 :
      c0TwoBetaAbs ≡ c0TwoBetaAbsThousandths

    c0TwoGapFromBeta6 :
      Nat

    c0TwoGapFromBeta6Is9836 :
      c0TwoGapFromBeta6 ≡ c0TwoGapThousandths

    c0FiveBetaAbs :
      Nat

    c0FiveBetaAbsIs19622 :
      c0FiveBetaAbs ≡ c0FiveBetaAbsThousandths

    c0FiveGapFromBeta6 :
      Nat

    c0FiveGapFromBeta6Is13622 :
      c0FiveGapFromBeta6 ≡ c0FiveGapThousandths

    c0OneGapFromBeta6 :
      Nat

    c0OneGapFromBeta6Is6971 :
      c0OneGapFromBeta6 ≡ c0OneGapThousandths

    monsterSqrtLeakBetaAbs :
      Nat

    monsterSqrtLeakBetaAbsIs2266 :
      monsterSqrtLeakBetaAbs ≡ monsterSqrtLeakBetaAbsHundredths

    monsterRawLeakBetaAbs :
      Nat

    monsterRawLeakBetaAbsIs3235 :
      monsterRawLeakBetaAbs ≡ monsterRawLeakBetaAbsHundredths

    c0IsLoadBearing :
      Bool

    c0IsLoadBearingIsTrue :
      c0IsLoadBearing ≡ true

    actualC0ProvedHere :
      Bool

    actualC0ProvedHereIsFalse :
      actualC0ProvedHere ≡ false

    quotientC0NearOneProvedHere :
      Bool

    quotientC0NearOneProvedHereIsFalse :
      quotientC0NearOneProvedHere ≡ false

    continuumMassGapPromoted :
      Bool

    continuumMassGapPromotedIsFalse :
      continuumMassGapPromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    promotions :
      List YMC0EntropyPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      YMC0EntropyPromotion →
      ⊥

    c0SensitivityText :
      String

    c0SensitivityTextIsCanonical :
      c0SensitivityText ≡ c0SensitivityStatement

    monsterStressText :
      String

    monsterStressTextIsCanonical :
      monsterStressText ≡ monsterStressStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open YMC0EntropyThresholdSensitivityReceipt public

canonicalYMC0EntropyThresholdSensitivityReceipt :
  YMC0EntropyThresholdSensitivityReceipt
canonicalYMC0EntropyThresholdSensitivityReceipt =
  record
    { status =
        ymC0EntropyThresholdSensitivityRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; thresholdReceipt =
        Threshold.canonicalYMKPThresholdCorrectionReceipt
    ; pBranching =
        recordedPBranching
    ; pBranchingIs7 =
        refl
    ; thresholdPBranchingMatches =
        refl
    ; aWeightNumerator =
        recordedAWeightNumerator
    ; aWeightNumeratorIs50 =
        refl
    ; thresholdAWeightNumeratorMatches =
        refl
    ; aWeightDenominator =
        recordedAWeightDenominator
    ; aWeightDenominatorIs100 =
        refl
    ; thresholdAWeightDenominatorMatches =
        refl
    ; cMinNumerator =
        recordedCMinNumerator
    ; cMinNumeratorIs242 =
        refl
    ; thresholdCMinNumeratorMatches =
        refl
    ; cMinDenominator =
        recordedCMinDenominator
    ; cMinDenominatorIs1000 =
        refl
    ; thresholdCMinDenominatorMatches =
        refl
    ; thresholdNoClay =
        refl
    ; betaBridgeReceipt =
        Bridge.canonicalYMBalabanPhysicalBetaBridgeTargetReceipt
    ; betaBridgeStillOpen =
        refl
    ; betaBridgeNoClay =
        refl
    ; monsterQuotientReceipt =
        MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; monsterQuotientStillOpen =
        refl
    ; monsterRawMultiplicityNotC0 =
        refl
    ; monsterC1Coefficient =
        monsterC1
    ; monsterC1CoefficientIs196884 =
        refl
    ; monsterC1MatchesReceipt =
        refl
    ; monsterC2Coefficient =
        monsterC2
    ; monsterC2CoefficientIs21493760 =
        refl
    ; monsterC2MatchesReceipt =
        refl
    ; monsterRawRatioApprox10917Hundredths =
        monsterRawRatioHundredths
    ; monsterRawRatioApprox10917HundredthsIsCanonical =
        refl
    ; monsterRawRatioApproxRounded =
        monsterRawRatioApprox
    ; monsterRawRatioApproxRoundedIs109 =
        refl
    ; monsterRawRatioRoundedMatchesReceipt =
        refl
    ; monsterSqrtRatioApprox1045Hundredths =
        monsterSqrtRatioHundredths
    ; monsterSqrtRatioApprox1045HundredthsIsCanonical =
        refl
    ; monsterSqrtRatioMatchesReceipt =
        refl
    ; sensitivityData =
        canonicalYMC0SensitivityData
    ; sensitivityDataAreCanonical =
        refl
    ; openObligations =
        canonicalYMC0OpenObligations
    ; openObligationsAreCanonical =
        refl
    ; c0HalfBetaAbs =
        c0HalfBetaAbsThousandths
    ; c0HalfBetaAbsIs10107 =
        refl
    ; c0HalfGapFromBeta6 =
        c0HalfGapThousandths
    ; c0HalfGapFromBeta6Is4107 =
        refl
    ; c0OneBetaAbs =
        c0OneBetaAbsThousandths
    ; c0OneBetaAbsIs12971 =
        refl
    ; c0TwoBetaAbs =
        c0TwoBetaAbsThousandths
    ; c0TwoBetaAbsIs15836 =
        refl
    ; c0TwoGapFromBeta6 =
        c0TwoGapThousandths
    ; c0TwoGapFromBeta6Is9836 =
        refl
    ; c0FiveBetaAbs =
        c0FiveBetaAbsThousandths
    ; c0FiveBetaAbsIs19622 =
        refl
    ; c0FiveGapFromBeta6 =
        c0FiveGapThousandths
    ; c0FiveGapFromBeta6Is13622 =
        refl
    ; c0OneGapFromBeta6 =
        c0OneGapThousandths
    ; c0OneGapFromBeta6Is6971 =
        refl
    ; monsterSqrtLeakBetaAbs =
        monsterSqrtLeakBetaAbsHundredths
    ; monsterSqrtLeakBetaAbsIs2266 =
        refl
    ; monsterRawLeakBetaAbs =
        monsterRawLeakBetaAbsHundredths
    ; monsterRawLeakBetaAbsIs3235 =
        refl
    ; c0IsLoadBearing =
        true
    ; c0IsLoadBearingIsTrue =
        refl
    ; actualC0ProvedHere =
        false
    ; actualC0ProvedHereIsFalse =
        refl
    ; quotientC0NearOneProvedHere =
        false
    ; quotientC0NearOneProvedHereIsFalse =
        refl
    ; continuumMassGapPromoted =
        false
    ; continuumMassGapPromotedIsFalse =
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
        ymC0EntropyPromotionImpossibleHere
    ; c0SensitivityText =
        c0SensitivityStatement
    ; c0SensitivityTextIsCanonical =
        refl
    ; monsterStressText =
        monsterStressStatement
    ; monsterStressTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalYMC0SensitivityLoadBearing :
  c0IsLoadBearing canonicalYMC0EntropyThresholdSensitivityReceipt ≡ true
canonicalYMC0SensitivityLoadBearing =
  refl

canonicalYMC0SensitivityNoClay :
  clayYMPromoted canonicalYMC0EntropyThresholdSensitivityReceipt ≡ false
canonicalYMC0SensitivityNoClay =
  refl
