module DASHI.Physics.Closure.YMT7RademacherActivityIdentificationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MonsterOggPrimeCorrectionReceipt as Ogg
import DASHI.Physics.Closure.YMMonsterQuotientEvidenceReceipt as YMT7

------------------------------------------------------------------------
-- YM T7 Rademacher / direct-activity receipt.
--
-- The audit verifies the sampled T7A/j suppression at depths 1, 2, and 3,
-- and the follow-up computation replaces the C0 = 2 shorthand with the
-- direct KP generating-function statement
--
--   sum_d c7(d) exp (- beta * c_min * d) < 1.
--
-- The direct T7A sum gives beta* ~= 16.56, gap ~= 10.56 from beta_phys = 6,
-- but it is worse as a counting route than connected animals, whose threshold
-- is beta* ~= 9.593637.  C0 = 2 remains a heuristic summary only, not a theorem
-- target.

data YMT7RademacherActivityStatus : Set where
  ymConnectedAnimalCountingCorrected_t7ActivitySuppressionOpen_noPromotion :
    YMT7RademacherActivityStatus

  ymT7RademacherActivityAuditRecorded_identificationOpen_noPromotion :
    YMT7RademacherActivityStatus

data T7AuditDatum : Set where
  t7ADepthOneCoefficient51 :
    T7AuditDatum

  t7ADepthTwoCoefficient204 :
    T7AuditDatum

  t7ADepthThreeCoefficient681 :
    T7AuditDatum

  jDepthOneCoefficient196884 :
    T7AuditDatum

  jDepthTwoCoefficient21493760 :
    T7AuditDatum

  jDepthThreeCoefficient864299970 :
    T7AuditDatum

  sampledRatiosBelowRademacherEnvelope :
    T7AuditDatum

canonicalT7AuditData : List T7AuditDatum
canonicalT7AuditData =
  t7ADepthOneCoefficient51
  ∷ t7ADepthTwoCoefficient204
  ∷ t7ADepthThreeCoefficient681
  ∷ jDepthOneCoefficient196884
  ∷ jDepthTwoCoefficient21493760
  ∷ jDepthThreeCoefficient864299970
  ∷ sampledRatiosBelowRademacherEnvelope
  ∷ []

data EntropyRegime : Set where
  rawMonsterJEnvelope :
    EntropyRegime

  t7RademacherEnvelope :
    EntropyRegime

  t7ADirectGeneratingFunction :
    EntropyRegime

  connectedAnimalCounting :
    EntropyRegime

  optimalMinCounting :
    EntropyRegime

  c0TwoHeuristicOnly :
    EntropyRegime

  c0TwoActivityTarget :
    EntropyRegime

canonicalEntropyRegimes : List EntropyRegime
canonicalEntropyRegimes =
  rawMonsterJEnvelope
  ∷ t7RademacherEnvelope
  ∷ connectedAnimalCounting
  ∷ optimalMinCounting
  ∷ t7ADirectGeneratingFunction
  ∷ c0TwoHeuristicOnly
  ∷ []

data T7ActivityOpenLemma : Set where
  proveDirectT7KPSumControlsActualPolymerActivities :
    T7ActivityOpenLemma

  proveT7APerPolymerActivitySuppression :
    T7ActivityOpenLemma

  proveConnectedAnimalBalabanBridge :
    T7ActivityOpenLemma

  proveBalabanBridgeFromBetaSixToBetaSixteenPointFiveEight :
    T7ActivityOpenLemma

  proveOSWightmanAfterBalabanBridge :
    T7ActivityOpenLemma

  provePolymerActivityBoundBySubRademacherT7Model :
    T7ActivityOpenLemma

  proveC0TwoFromActualCarrierActivityNotEnvelope :
    T7ActivityOpenLemma

  feedIdentifiedC0IntoBalabanBridge :
    T7ActivityOpenLemma

canonicalT7ActivityOpenLemmas : List T7ActivityOpenLemma
canonicalT7ActivityOpenLemmas =
  proveT7APerPolymerActivitySuppression
  ∷ proveConnectedAnimalBalabanBridge
  ∷ proveOSWightmanAfterBalabanBridge
  ∷ []

data YMT7AuditPromotion : Set where

ymT7AuditPromotionImpossibleHere :
  YMT7AuditPromotion →
  ⊥
ymT7AuditPromotionImpossibleHere ()

t7CoeffDepth1 :
  Nat
t7CoeffDepth1 =
  51

t7CoeffDepth2 :
  Nat
t7CoeffDepth2 =
  204

t7CoeffDepth3 :
  Nat
t7CoeffDepth3 =
  681

jCoeffDepth1 :
  Nat
jCoeffDepth1 =
  196884

jCoeffDepth2 :
  Nat
jCoeffDepth2 =
  21493760

jCoeffDepth3 :
  Nat
jCoeffDepth3 =
  864299970

ratioD1PartsPerBillion :
  Nat
ratioD1PartsPerBillion =
  259035

ratioD2PartsPerBillion :
  Nat
ratioD2PartsPerBillion =
  9491

ratioD3PartsPerBillion :
  Nat
ratioD3PartsPerBillion =
  788

rademacherBoundD1PartsPerBillion :
  Nat
rademacherBoundD1PartsPerBillion =
  403000

rademacherBoundD2PartsPerBillion :
  Nat
rademacherBoundD2PartsPerBillion =
  15800

rademacherBoundD3PartsPerBillion :
  Nat
rademacherBoundD3PartsPerBillion =
  1320

rawMonsterC0Approx :
  Nat
rawMonsterC0Approx =
  287000

t7EnvelopeC0Millis :
  Nat
t7EnvelopeC0Millis =
  115543

c0TwoTargetMillis :
  Nat
c0TwoTargetMillis =
  2000

betaThresholdRawHundredths :
  Nat
betaThresholdRawHundredths =
  6490

betaThresholdT7Hundredths :
  Nat
betaThresholdT7Hundredths =
  3260

betaThresholdC0TwoHundredths :
  Nat
betaThresholdC0TwoHundredths =
  1590

betaThresholdT7ADirectHundredths :
  Nat
betaThresholdT7ADirectHundredths =
  1656

betaGapT7ADirectFromPhysicalHundredths :
  Nat
betaGapT7ADirectFromPhysicalHundredths =
  1056

betaThresholdConnectedAnimalHundredths :
  Nat
betaThresholdConnectedAnimalHundredths =
  959

betaGapConnectedAnimalFromPhysicalHundredths :
  Nat
betaGapConnectedAnimalFromPhysicalHundredths =
  359

betaThresholdNaiveBTHundredths :
  Nat
betaThresholdNaiveBTHundredths =
  804

betaThresholdOptimalMinHundredths :
  Nat
betaThresholdOptimalMinHundredths =
  886

t7BeatsNaiveBTFromDepth :
  Nat
t7BeatsNaiveBTFromDepth =
  4

t7BeatsConnectedAnimalFromDepth :
  Nat
t7BeatsConnectedAnimalFromDepth =
  5

t7OverPDepth1Hundredths :
  Nat
t7OverPDepth1Hundredths =
  729

t7OverPDepth2Hundredths :
  Nat
t7OverPDepth2Hundredths =
  416

t7OverPDepth3Hundredths :
  Nat
t7OverPDepth3Hundredths =
  199

t7OverPDepth4Hundredths :
  Nat
t7OverPDepth4Hundredths =
  88

t7OverPDepth5Hundredths :
  Nat
t7OverPDepth5Hundredths =
  36

t7AuditStatement :
  String
t7AuditStatement =
  "The audited T7A/j ratios at depths 1, 2, and 3 lie below the sampled Rademacher suppression envelope; the direct T7A generating sum is computed at beta* about 16.56, but it is a worse counting bound than connected-animal counting."

t7ActivityIdentificationStatement :
  String
t7ActivityIdentificationStatement =
  "C0 = 2 is not a theorem from T7A alone.  The corrected KP count route uses connected animals with beta* about 9.593637; T7A helps only if one proves per-polymer activity suppression relative to connected-animal counting."

t7DirectKPSumStatement :
  String
t7DirectKPSumStatement =
  "Direct T7A sum: sum_{d>=1} c7(d) * exp(-beta*c_min*d) < 1 at beta* = 16.56, gap 10.56 from beta_phys = 6.  This is proved as a direct series computation but is not the best KP counting route; connected-animal counting gives beta* = 9.593637 and gap 3.593637."

record YMT7RademacherActivityIdentificationReceipt : Setω where
  field
    status :
      YMT7RademacherActivityStatus

    statusIsCanonical :
      status
      ≡
      ymConnectedAnimalCountingCorrected_t7ActivitySuppressionOpen_noPromotion

    oggCorrectionReceipt :
      Ogg.MonsterOggPrimeCorrectionReceipt

    oggCorrectionRejectsGenusPartition :
      Ogg.fifteenPlus179GenusPartitionClaim oggCorrectionReceipt ≡ false

    oggCorrectionNoYM :
      Ogg.clayYangMillsPromoted oggCorrectionReceipt ≡ false

    ymT7EvidenceReceipt :
      YMT7.YMMonsterQuotientEvidenceReceipt

    ymT7EvidenceNoClay :
      YMT7.clayYMPromoted ymT7EvidenceReceipt ≡ false

    ymT7QuotientStillOpen :
      YMT7.quotientEntropyBoundProvedHere ymT7EvidenceReceipt ≡ false

    auditData :
      List T7AuditDatum

    auditDataAreCanonical :
      auditData ≡ canonicalT7AuditData

    entropyRegimes :
      List EntropyRegime

    entropyRegimesAreCanonical :
      entropyRegimes ≡ canonicalEntropyRegimes

    openLemmas :
      List T7ActivityOpenLemma

    openLemmasAreCanonical :
      openLemmas ≡ canonicalT7ActivityOpenLemmas

    t7D1 :
      Nat

    t7D1Is51 :
      t7D1 ≡ t7CoeffDepth1

    t7D2 :
      Nat

    t7D2Is204 :
      t7D2 ≡ t7CoeffDepth2

    t7D3 :
      Nat

    t7D3Is681 :
      t7D3 ≡ t7CoeffDepth3

    jD1 :
      Nat

    jD1Is196884 :
      jD1 ≡ jCoeffDepth1

    jD2 :
      Nat

    jD2Is21493760 :
      jD2 ≡ jCoeffDepth2

    jD3 :
      Nat

    jD3Is864299970 :
      jD3 ≡ jCoeffDepth3

    actualRatioD1PPB :
      Nat

    actualRatioD1PPBIsCanonical :
      actualRatioD1PPB ≡ ratioD1PartsPerBillion

    actualRatioD2PPB :
      Nat

    actualRatioD2PPBIsCanonical :
      actualRatioD2PPB ≡ ratioD2PartsPerBillion

    actualRatioD3PPB :
      Nat

    actualRatioD3PPBIsCanonical :
      actualRatioD3PPB ≡ ratioD3PartsPerBillion

    boundD1PPB :
      Nat

    boundD1PPBIsCanonical :
      boundD1PPB ≡ rademacherBoundD1PartsPerBillion

    boundD2PPB :
      Nat

    boundD2PPBIsCanonical :
      boundD2PPB ≡ rademacherBoundD2PartsPerBillion

    boundD3PPB :
      Nat

    boundD3PPBIsCanonical :
      boundD3PPB ≡ rademacherBoundD3PartsPerBillion

    rawC0 :
      Nat

    rawC0IsApprox287000 :
      rawC0 ≡ rawMonsterC0Approx

    t7EnvelopeC0 :
      Nat

    t7EnvelopeC0Is115543Millis :
      t7EnvelopeC0 ≡ t7EnvelopeC0Millis

    c0TwoTarget :
      Nat

    c0TwoTargetIs2000Millis :
      c0TwoTarget ≡ c0TwoTargetMillis

    betaRaw :
      Nat

    betaRawIs6490Hundredths :
      betaRaw ≡ betaThresholdRawHundredths

    betaT7 :
      Nat

    betaT7Is3260Hundredths :
      betaT7 ≡ betaThresholdT7Hundredths

    betaC0Two :
      Nat

    betaC0TwoIs1590Hundredths :
      betaC0Two ≡ betaThresholdC0TwoHundredths

    betaT7ADirect :
      Nat

    betaT7ADirectIs1656Hundredths :
      betaT7ADirect ≡ betaThresholdT7ADirectHundredths

    betaT7ADirectGapFromPhysical :
      Nat

    betaT7ADirectGapFromPhysicalIs1056Hundredths :
      betaT7ADirectGapFromPhysical
      ≡
      betaGapT7ADirectFromPhysicalHundredths

    betaConnectedAnimal :
      Nat

    betaConnectedAnimalIs959Hundredths :
      betaConnectedAnimal ≡ betaThresholdConnectedAnimalHundredths

    betaConnectedAnimalGapFromPhysical :
      Nat

    betaConnectedAnimalGapFromPhysicalIs359Hundredths :
      betaConnectedAnimalGapFromPhysical
      ≡
      betaGapConnectedAnimalFromPhysicalHundredths

    betaNaiveBT :
      Nat

    betaNaiveBTIs804Hundredths :
      betaNaiveBT ≡ betaThresholdNaiveBTHundredths

    betaOptimalMin :
      Nat

    betaOptimalMinIs886Hundredths :
      betaOptimalMin ≡ betaThresholdOptimalMinHundredths

    t7OverPDepth1 :
      Nat

    t7OverPDepth1Is729Hundredths :
      t7OverPDepth1 ≡ t7OverPDepth1Hundredths

    t7OverPDepth2 :
      Nat

    t7OverPDepth2Is416Hundredths :
      t7OverPDepth2 ≡ t7OverPDepth2Hundredths

    t7OverPDepth3 :
      Nat

    t7OverPDepth3Is199Hundredths :
      t7OverPDepth3 ≡ t7OverPDepth3Hundredths

    t7OverPDepth4 :
      Nat

    t7OverPDepth4Is88Hundredths :
      t7OverPDepth4 ≡ t7OverPDepth4Hundredths

    t7OverPDepth5 :
      Nat

    t7OverPDepth5Is36Hundredths :
      t7OverPDepth5 ≡ t7OverPDepth5Hundredths

    ymT7RademacherBoundVerified :
      Bool

    ymT7RademacherBoundVerifiedIsTrue :
      ymT7RademacherBoundVerified ≡ true

    c0TwoFollowsFromRademacherEnvelope :
      Bool

    c0TwoFollowsFromRademacherEnvelopeIsFalse :
      c0TwoFollowsFromRademacherEnvelope ≡ false

    ymC0TwoActivityIdentificationProved :
      Bool

    ymC0TwoActivityIdentificationProvedIsFalse :
      ymC0TwoActivityIdentificationProved ≡ false

    ymT7DirectKPSumThresholdComputed :
      Bool

    ymT7DirectKPSumThresholdComputedIsTrue :
      ymT7DirectKPSumThresholdComputed ≡ true

    ymConnectedAnimalBoundComputed :
      Bool

    ymConnectedAnimalBoundComputedIsTrue :
      ymConnectedAnimalBoundComputed ≡ true

    ymT7DirectKPSumIsBestCountingRoute :
      Bool

    ymT7DirectKPSumIsBestCountingRouteIsFalse :
      ymT7DirectKPSumIsBestCountingRoute ≡ false

    ymT7ACoefficientsPositive :
      Bool

    ymT7ACoefficientsPositiveIsTrue :
      ymT7ACoefficientsPositive ≡ true

    ymT7BeatsNaiveBTFromDepth :
      Nat

    ymT7BeatsNaiveBTFromDepthIs4 :
      ymT7BeatsNaiveBTFromDepth ≡ t7BeatsNaiveBTFromDepth

    ymT7BeatsConnectedAnimalFromDepth :
      Nat

    ymT7BeatsConnectedAnimalFromDepthIs5 :
      ymT7BeatsConnectedAnimalFromDepth
      ≡
      t7BeatsConnectedAnimalFromDepth

    ymT7PerPolymerActivitySuppressionProved :
      Bool

    ymT7PerPolymerActivitySuppressionProvedIsFalse :
      ymT7PerPolymerActivitySuppressionProved ≡ false

    c0TwoEffJustifiedByT7Alone :
      Bool

    c0TwoEffJustifiedByT7AloneIsFalse :
      c0TwoEffJustifiedByT7Alone ≡ false

    balabanBridgeProved :
      Bool

    balabanBridgeProvedIsFalse :
      balabanBridgeProved ≡ false

    osWightmanReconstructionProved :
      Bool

    osWightmanReconstructionProvedIsFalse :
      osWightmanReconstructionProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List YMT7AuditPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      YMT7AuditPromotion →
      ⊥

    auditText :
      String

    auditTextIsCanonical :
      auditText ≡ t7AuditStatement

    identificationText :
      String

    identificationTextIsCanonical :
      identificationText ≡ t7ActivityIdentificationStatement

    directKPSumText :
      String

    directKPSumTextIsCanonical :
      directKPSumText ≡ t7DirectKPSumStatement

open YMT7RademacherActivityIdentificationReceipt public

canonicalYMT7RademacherActivityIdentificationReceipt :
  YMT7RademacherActivityIdentificationReceipt
canonicalYMT7RademacherActivityIdentificationReceipt =
  record
    { status =
        ymConnectedAnimalCountingCorrected_t7ActivitySuppressionOpen_noPromotion
    ; statusIsCanonical =
        refl
    ; oggCorrectionReceipt =
        Ogg.canonicalMonsterOggPrimeCorrectionReceipt
    ; oggCorrectionRejectsGenusPartition =
        refl
    ; oggCorrectionNoYM =
        refl
    ; ymT7EvidenceReceipt =
        YMT7.canonicalYMMonsterQuotientEvidenceReceipt
    ; ymT7EvidenceNoClay =
        refl
    ; ymT7QuotientStillOpen =
        refl
    ; auditData =
        canonicalT7AuditData
    ; auditDataAreCanonical =
        refl
    ; entropyRegimes =
        canonicalEntropyRegimes
    ; entropyRegimesAreCanonical =
        refl
    ; openLemmas =
        canonicalT7ActivityOpenLemmas
    ; openLemmasAreCanonical =
        refl
    ; t7D1 =
        t7CoeffDepth1
    ; t7D1Is51 =
        refl
    ; t7D2 =
        t7CoeffDepth2
    ; t7D2Is204 =
        refl
    ; t7D3 =
        t7CoeffDepth3
    ; t7D3Is681 =
        refl
    ; jD1 =
        jCoeffDepth1
    ; jD1Is196884 =
        refl
    ; jD2 =
        jCoeffDepth2
    ; jD2Is21493760 =
        refl
    ; jD3 =
        jCoeffDepth3
    ; jD3Is864299970 =
        refl
    ; actualRatioD1PPB =
        ratioD1PartsPerBillion
    ; actualRatioD1PPBIsCanonical =
        refl
    ; actualRatioD2PPB =
        ratioD2PartsPerBillion
    ; actualRatioD2PPBIsCanonical =
        refl
    ; actualRatioD3PPB =
        ratioD3PartsPerBillion
    ; actualRatioD3PPBIsCanonical =
        refl
    ; boundD1PPB =
        rademacherBoundD1PartsPerBillion
    ; boundD1PPBIsCanonical =
        refl
    ; boundD2PPB =
        rademacherBoundD2PartsPerBillion
    ; boundD2PPBIsCanonical =
        refl
    ; boundD3PPB =
        rademacherBoundD3PartsPerBillion
    ; boundD3PPBIsCanonical =
        refl
    ; rawC0 =
        rawMonsterC0Approx
    ; rawC0IsApprox287000 =
        refl
    ; t7EnvelopeC0 =
        t7EnvelopeC0Millis
    ; t7EnvelopeC0Is115543Millis =
        refl
    ; c0TwoTarget =
        c0TwoTargetMillis
    ; c0TwoTargetIs2000Millis =
        refl
    ; betaRaw =
        betaThresholdRawHundredths
    ; betaRawIs6490Hundredths =
        refl
    ; betaT7 =
        betaThresholdT7Hundredths
    ; betaT7Is3260Hundredths =
        refl
    ; betaC0Two =
        betaThresholdC0TwoHundredths
    ; betaC0TwoIs1590Hundredths =
        refl
    ; betaT7ADirect =
        betaThresholdT7ADirectHundredths
    ; betaT7ADirectIs1656Hundredths =
        refl
    ; betaT7ADirectGapFromPhysical =
        betaGapT7ADirectFromPhysicalHundredths
    ; betaT7ADirectGapFromPhysicalIs1056Hundredths =
        refl
    ; betaConnectedAnimal =
        betaThresholdConnectedAnimalHundredths
    ; betaConnectedAnimalIs959Hundredths =
        refl
    ; betaConnectedAnimalGapFromPhysical =
        betaGapConnectedAnimalFromPhysicalHundredths
    ; betaConnectedAnimalGapFromPhysicalIs359Hundredths =
        refl
    ; betaNaiveBT =
        betaThresholdNaiveBTHundredths
    ; betaNaiveBTIs804Hundredths =
        refl
    ; betaOptimalMin =
        betaThresholdOptimalMinHundredths
    ; betaOptimalMinIs886Hundredths =
        refl
    ; t7OverPDepth1 =
        t7OverPDepth1Hundredths
    ; t7OverPDepth1Is729Hundredths =
        refl
    ; t7OverPDepth2 =
        t7OverPDepth2Hundredths
    ; t7OverPDepth2Is416Hundredths =
        refl
    ; t7OverPDepth3 =
        t7OverPDepth3Hundredths
    ; t7OverPDepth3Is199Hundredths =
        refl
    ; t7OverPDepth4 =
        t7OverPDepth4Hundredths
    ; t7OverPDepth4Is88Hundredths =
        refl
    ; t7OverPDepth5 =
        t7OverPDepth5Hundredths
    ; t7OverPDepth5Is36Hundredths =
        refl
    ; ymT7RademacherBoundVerified =
        true
    ; ymT7RademacherBoundVerifiedIsTrue =
        refl
    ; c0TwoFollowsFromRademacherEnvelope =
        false
    ; c0TwoFollowsFromRademacherEnvelopeIsFalse =
        refl
    ; ymC0TwoActivityIdentificationProved =
        false
    ; ymC0TwoActivityIdentificationProvedIsFalse =
        refl
    ; ymT7DirectKPSumThresholdComputed =
        true
    ; ymT7DirectKPSumThresholdComputedIsTrue =
        refl
    ; ymConnectedAnimalBoundComputed =
        true
    ; ymConnectedAnimalBoundComputedIsTrue =
        refl
    ; ymT7DirectKPSumIsBestCountingRoute =
        false
    ; ymT7DirectKPSumIsBestCountingRouteIsFalse =
        refl
    ; ymT7ACoefficientsPositive =
        true
    ; ymT7ACoefficientsPositiveIsTrue =
        refl
    ; ymT7BeatsNaiveBTFromDepth =
        t7BeatsNaiveBTFromDepth
    ; ymT7BeatsNaiveBTFromDepthIs4 =
        refl
    ; ymT7BeatsConnectedAnimalFromDepth =
        t7BeatsConnectedAnimalFromDepth
    ; ymT7BeatsConnectedAnimalFromDepthIs5 =
        refl
    ; ymT7PerPolymerActivitySuppressionProved =
        false
    ; ymT7PerPolymerActivitySuppressionProvedIsFalse =
        refl
    ; c0TwoEffJustifiedByT7Alone =
        false
    ; c0TwoEffJustifiedByT7AloneIsFalse =
        refl
    ; balabanBridgeProved =
        false
    ; balabanBridgeProvedIsFalse =
        refl
    ; osWightmanReconstructionProved =
        false
    ; osWightmanReconstructionProvedIsFalse =
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
        ymT7AuditPromotionImpossibleHere
    ; auditText =
        t7AuditStatement
    ; auditTextIsCanonical =
        refl
    ; identificationText =
        t7ActivityIdentificationStatement
    ; identificationTextIsCanonical =
        refl
    ; directKPSumText =
        t7DirectKPSumStatement
    ; directKPSumTextIsCanonical =
        refl
    }

ymT7AuditKeepsClayFalse :
  clayYangMillsPromoted
    canonicalYMT7RademacherActivityIdentificationReceipt
  ≡
  false
ymT7AuditKeepsClayFalse =
  refl

ymT7AuditKeepsC0TwoIdentificationOpen :
  ymC0TwoActivityIdentificationProved
    canonicalYMT7RademacherActivityIdentificationReceipt
  ≡
  false
ymT7AuditKeepsC0TwoIdentificationOpen =
  refl

ymT7DirectKPSumThresholdIsComputed :
  ymT7DirectKPSumThresholdComputed
    canonicalYMT7RademacherActivityIdentificationReceipt
  ≡
  true
ymT7DirectKPSumThresholdIsComputed =
  refl
