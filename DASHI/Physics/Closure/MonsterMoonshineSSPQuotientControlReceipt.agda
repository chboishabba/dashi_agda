module DASHI.Physics.Closure.MonsterMoonshineSSPQuotientControlReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor as CTP
import DASHI.Physics.Closure.ClayBlockerAsymmetryReceipt as Asymmetry
import DASHI.Physics.Closure.Gate3DigitExpansionPAWOTGPartialResultReceipt
  as Gate3Digit
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as Gate3Target
import DASHI.Physics.Closure.MonsterMoonshineJDistributionSupportReceipt
  as JDist
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.NSThetaPressureMarginCorrectionReceipt as NS
import DASHI.Physics.Closure.YMBalabanPhysicalBetaBridgeTargetReceipt
  as YMBeta
import DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt as YMKP
import DASHI.Physics.Moonshine.MonsterOrderDepthBoundReceipt as Order
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge as SSPBridge
import MonsterOntos as MO
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- Monster / moonshine / 15SSP quotient-control receipt.
--
-- This receipt records the corrected interpretation of Monster q-expansion
-- growth for the Clay-facing entropy constants.  Raw Monster multiplicity is
-- representation multiplicity, not the physical KP/PAWOTG/NS entropy
-- multiplier.  The 15SSP / Hecke / moonshine carrier is the quotient surface
-- that should collapse many raw Monster states into the same SSP/Hecke orbit
-- class before any physical polymer/atom/tail pressure constant is read.
--
-- The actual quotient theorem remains open.  This receipt records the load-
-- bearing target and the domain fences; it does not prove C0_eff ~= 1, Gate 3,
-- YM, NS, Clay, or terminal closure.

data MonsterMoonshineSSPQuotientControlStatus : Set where
  monsterMoonshineSSPQuotientTargetRecorded_noPromotion :
    MonsterMoonshineSSPQuotientControlStatus

data MonsterMultiplicityDatum : Set where
  c1JCoefficient196884 :
    MonsterMultiplicityDatum

  c2JCoefficient21493760 :
    MonsterMultiplicityDatum

  rawRatioApprox109 :
    MonsterMultiplicityDatum

  sqrtRawRatioApprox1045Hundredths :
    MonsterMultiplicityDatum

  irrep2OverIrrep1Approx108 :
    MonsterMultiplicityDatum

  sqrtIrrep2OverIrrep1Approx1040Hundredths :
    MonsterMultiplicityDatum

  rawMultiplicityIsRepresentationGrowth :
    MonsterMultiplicityDatum

canonicalMonsterMultiplicityData :
  List MonsterMultiplicityDatum
canonicalMonsterMultiplicityData =
  c1JCoefficient196884
  ∷ c2JCoefficient21493760
  ∷ rawRatioApprox109
  ∷ sqrtRawRatioApprox1045Hundredths
  ∷ irrep2OverIrrep1Approx108
  ∷ sqrtIrrep2OverIrrep1Approx1040Hundredths
  ∷ rawMultiplicityIsRepresentationGrowth
  ∷ []

data SSPQuotientMechanism : Set where
  factorVecSSP15Carrier :
    SSPQuotientMechanism

  monsterPrimeLaneToSSPQuotient :
    SSPQuotientMechanism

  supersingularPrimeLaneSupport :
    SSPQuotientMechanism

  heckeOrbitCompatibilitySignatures :
    SSPQuotientMechanism

  moonshinePrimeSupportGrammar :
    SSPQuotientMechanism

canonicalSSPQuotientMechanisms :
  List SSPQuotientMechanism
canonicalSSPQuotientMechanisms =
  factorVecSSP15Carrier
  ∷ monsterPrimeLaneToSSPQuotient
  ∷ supersingularPrimeLaneSupport
  ∷ heckeOrbitCompatibilitySignatures
  ∷ moonshinePrimeSupportGrammar
  ∷ []

data QuotientEntropyConsequence : Set where
  ymC0MustBeEffectiveOrbitEntropyNotRawMonsterMultiplicity :
    QuotientEntropyConsequence

  gate3OverlapEntropyMustBeQuotientedNotRawMonsterMultiplicity :
    QuotientEntropyConsequence

  nsMonsterLowDepthGrowthMustBeFencedFromTailTheta :
    QuotientEntropyConsequence

  quotientFailureRaisesYMThresholdsAndTightensGate3 :
    QuotientEntropyConsequence

canonicalQuotientEntropyConsequences :
  List QuotientEntropyConsequence
canonicalQuotientEntropyConsequences =
  ymC0MustBeEffectiveOrbitEntropyNotRawMonsterMultiplicity
  ∷ gate3OverlapEntropyMustBeQuotientedNotRawMonsterMultiplicity
  ∷ nsMonsterLowDepthGrowthMustBeFencedFromTailTheta
  ∷ quotientFailureRaisesYMThresholdsAndTightensGate3
  ∷ []

data QuotientControlOpenObligation : Set where
  constructMonsterRepToSSPHeckeOrbitQuotientMap :
    QuotientControlOpenObligation

  proveEffectiveC0BoundedBySmallOrbitConstant :
    QuotientControlOpenObligation

  proveRawMultiplicityDoesNotLeakIntoYMPolymerEntropy :
    QuotientControlOpenObligation

  proveRawMultiplicityDoesNotLeakIntoGate3OverlapEntropy :
    QuotientControlOpenObligation

  proveRawMultiplicityDoesNotLeakIntoNSTailTheta :
    QuotientControlOpenObligation

canonicalQuotientControlOpenObligations :
  List QuotientControlOpenObligation
canonicalQuotientControlOpenObligations =
  constructMonsterRepToSSPHeckeOrbitQuotientMap
  ∷ proveEffectiveC0BoundedBySmallOrbitConstant
  ∷ proveRawMultiplicityDoesNotLeakIntoYMPolymerEntropy
  ∷ proveRawMultiplicityDoesNotLeakIntoGate3OverlapEntropy
  ∷ proveRawMultiplicityDoesNotLeakIntoNSTailTheta
  ∷ []

data MonsterQuotientPromotion : Set where

monsterQuotientPromotionImpossibleHere :
  MonsterQuotientPromotion →
  ⊥
monsterQuotientPromotionImpossibleHere ()

c1Monster :
  Nat
c1Monster =
  196884

c2Monster :
  Nat
c2Monster =
  21493760

irrep1Monster :
  Nat
irrep1Monster =
  196883

irrep2Monster :
  Nat
irrep2Monster =
  21296876

rawRatioApprox :
  Nat
rawRatioApprox =
  109

irrepRatioApprox :
  Nat
irrepRatioApprox =
  108

sqrtRawRatioApproxHundredths :
  Nat
sqrtRawRatioApproxHundredths =
  1045

sqrtIrrepRatioApproxHundredths :
  Nat
sqrtIrrepRatioApproxHundredths =
  1040

betaAbsC0OneHundredths :
  Nat
betaAbsC0OneHundredths =
  1297

betaAbsLogLeakHundredths :
  Nat
betaAbsLogLeakHundredths =
  1936

betaAbsSqrtIrrepLeakHundredths :
  Nat
betaAbsSqrtIrrepLeakHundredths =
  2265

betaAbsSqrtLeakHundredths :
  Nat
betaAbsSqrtLeakHundredths =
  2266

betaAbsIrrepLeakHundredths :
  Nat
betaAbsIrrepLeakHundredths =
  3231

betaAbsRawLeakHundredths :
  Nat
betaAbsRawLeakHundredths =
  3235

gate3SigmaBaselineTenThousandths :
  Nat
gate3SigmaBaselineTenThousandths =
  5052

gate3SigmaLogLeakTenThousandths :
  Nat
gate3SigmaLogLeakTenThousandths =
  3375

gate3SigmaSqrtIrrepLeakTenThousandths :
  Nat
gate3SigmaSqrtIrrepLeakTenThousandths =
  2961

gate3SigmaSqrtRawLeakTenThousandths :
  Nat
gate3SigmaSqrtRawLeakTenThousandths =
  2959

gate3SigmaIrrepLeakTenThousandths :
  Nat
gate3SigmaIrrepLeakTenThousandths =
  2284

gate3SigmaRawLeakTenThousandths :
  Nat
gate3SigmaRawLeakTenThousandths =
  2283

sspPrimeCount :
  Nat
sspPrimeCount =
  15

rawMultiplicityStatement :
  String
rawMultiplicityStatement =
  "Raw Monster q^2/q growth c2/c1 ~= 109 is representation multiplicity, not physical polymer entropy C0."

quotientStatement :
  String
quotientStatement =
  "The 15SSP / Hecke / moonshine carrier must be consumed as a quotient: Monster representation states collapse to SSP/Hecke orbit classes before YM C0, Gate3 overlap entropy, or NS tail theta is read."

thresholdSensitivityStatement :
  String
thresholdSensitivityStatement =
  "YM beta_abs(C0) stress model: C0_eff~=1 gives beta_abs~=12.97; log(c2/c1) leak gives ~=19.36; sqrt(irrep2/irrep1) leak gives ~=22.65; sqrt(c2/c1) leak gives ~=22.66; raw irrep/c leaks give ~=32.31/32.35."

gate3StressStatement :
  String
gate3StressStatement =
  "Gate3 p=3 sigma_crit stress model: baseline C0=1 gives sigma<0.5052; log(c2/c1) leak gives 0.3375; sqrt leak gives about 0.296; raw leak gives about 0.228.  This is an entropy stress test, not PAWOTG closure."

effectiveMultiplicityStatement :
  String
effectiveMultiplicityStatement =
  "The new shared blocker is effective multiplicity control: prove the carrier quotient keeps Monster q^2 / second-irrep growth out of YM C0, Gate3 PAWOTG overlap counts, and NS tail theta."

promotionBoundary :
  String
promotionBoundary =
  "This receipt records the quotient-control target only.  It does not prove the quotient entropy bound, PAWOTG, the physical beta bridge, NS theta preservation, Clay, or terminal promotion."

record MonsterMoonshineSSPQuotientControlReceipt : Setω where
  field
    status :
      MonsterMoonshineSSPQuotientControlStatus

    statusIsCanonical :
      status ≡ monsterMoonshineSSPQuotientTargetRecorded_noPromotion

    carrierType :
      Set

    carrierTypeIsFactorVec :
      carrierType ≡ GL.FactorVec

    sspType :
      Set

    sspTypeIsSSP :
      sspType ≡ MO.SSP

    monsterPrimeLaneReceipt :
      Lane.MoonshinePrimeLaneReceiptSurface

    monsterPrimeLaneIsCanonical :
      Lane.trackedPrimeLane monsterPrimeLaneReceipt
      ≡
      Lane.canonicalMonsterPrimeLane

    supersingularBridgeReceipt :
      SSPBridge.SupersingularPrimeLaneBridgeReceipt

    supersingularNatsAreCanonical :
      SSPBridge.supersingularPrimeNats supersingularBridgeReceipt
      ≡
      SSPBridge.canonicalSupersingularPrimeLaneNats

    monsterToSSPMapReceipt :
      CTP.PrimeBumpCovarianceSemanticsReceipt

    monsterToSSPMapIsCanonical :
      CTP.primeLaneInterpretation monsterToSSPMapReceipt
      ≡
      CTP.monsterPrimeLaneToSSP

    monsterOrderDepthReceipt :
      Order.MonsterOrderDepthBoundReceipt

    monsterOrderDepthNoPromotion :
      Order.depthBoundProved monsterOrderDepthReceipt ≡ false

    jDistributionReceipt :
      JDist.MonsterMoonshineJDistributionSupportReceipt

    jDistributionNotPAdicValuationUniform :
      JDist.jDistributionIsNotPAdicValuationUniform jDistributionReceipt
      ≡
      true

    jDistributionNoClay :
      JDist.clayPromoted jDistributionReceipt ≡ false

    ymKPReceipt :
      YMKP.YMKPThresholdCorrectionReceipt

    ymPhysicalBetaDivergent :
      YMKP.physicalBetaKPDivergent ymKPReceipt ≡ true

    ymBetaTargetReceipt :
      YMBeta.YMBalabanPhysicalBetaBridgeTargetReceipt

    ymBetaBridgeStillOpen :
      YMBeta.physicalBetaBridgeProvedHere ymBetaTargetReceipt ≡ false

    gate3DigitReceipt :
      Gate3Digit.Gate3DigitExpansionPAWOTGPartialResultReceipt

    gate3DigitNoGate3Promotion :
      Gate3Digit.gate3Promoted gate3DigitReceipt ≡ false

    gate3TargetReceipt :
      Gate3Target.Gate3PAWOTGUniformSeparationTargetReceipt

    gate3TargetInfANStillOpen :
      Gate3Target.infANPositiveProvedHere gate3TargetReceipt ≡ false

    nsThetaCorrectionReceipt :
      NS.NSThetaPressureMarginCorrectionReceipt

    nsThetaNoClay :
      NS.clayNavierStokesPromoted nsThetaCorrectionReceipt ≡ false

    clayAsymmetryReceipt :
      Asymmetry.ClayBlockerAsymmetryReceipt

    clayAsymmetryNoClay :
      Asymmetry.clayPromoted clayAsymmetryReceipt ≡ false

    multiplicityData :
      List MonsterMultiplicityDatum

    multiplicityDataAreCanonical :
      multiplicityData ≡ canonicalMonsterMultiplicityData

    quotientMechanisms :
      List SSPQuotientMechanism

    quotientMechanismsAreCanonical :
      quotientMechanisms ≡ canonicalSSPQuotientMechanisms

    entropyConsequences :
      List QuotientEntropyConsequence

    entropyConsequencesAreCanonical :
      entropyConsequences ≡ canonicalQuotientEntropyConsequences

    openObligations :
      List QuotientControlOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalQuotientControlOpenObligations

    c1 :
      Nat

    c1Is196884 :
      c1 ≡ c1Monster

    c2 :
      Nat

    c2Is21493760 :
      c2 ≡ c2Monster

    irrep1 :
      Nat

    irrep1Is196883 :
      irrep1 ≡ irrep1Monster

    irrep2 :
      Nat

    irrep2Is21296876 :
      irrep2 ≡ irrep2Monster

    rawRatio :
      Nat

    rawRatioIsApprox109 :
      rawRatio ≡ rawRatioApprox

    irrepRatio :
      Nat

    irrepRatioIsApprox108 :
      irrepRatio ≡ irrepRatioApprox

    sqrtRawRatio :
      Nat

    sqrtRawRatioIs1045Hundredths :
      sqrtRawRatio ≡ sqrtRawRatioApproxHundredths

    sqrtIrrepRatio :
      Nat

    sqrtIrrepRatioIs1040Hundredths :
      sqrtIrrepRatio ≡ sqrtIrrepRatioApproxHundredths

    sspCount :
      Nat

    sspCountIs15 :
      sspCount ≡ sspPrimeCount

    betaAbsC0One :
      Nat

    betaAbsC0OneIs1297 :
      betaAbsC0One ≡ betaAbsC0OneHundredths

    betaAbsLogLeak :
      Nat

    betaAbsLogLeakIs1936 :
      betaAbsLogLeak ≡ betaAbsLogLeakHundredths

    betaAbsSqrtIrrepLeak :
      Nat

    betaAbsSqrtIrrepLeakIs2265 :
      betaAbsSqrtIrrepLeak ≡ betaAbsSqrtIrrepLeakHundredths

    betaAbsSqrtLeak :
      Nat

    betaAbsSqrtLeakIs2266 :
      betaAbsSqrtLeak ≡ betaAbsSqrtLeakHundredths

    betaAbsIrrepLeak :
      Nat

    betaAbsIrrepLeakIs3231 :
      betaAbsIrrepLeak ≡ betaAbsIrrepLeakHundredths

    betaAbsRawLeak :
      Nat

    betaAbsRawLeakIs3235 :
      betaAbsRawLeak ≡ betaAbsRawLeakHundredths

    gate3SigmaBaseline :
      Nat

    gate3SigmaBaselineIs05052 :
      gate3SigmaBaseline ≡ gate3SigmaBaselineTenThousandths

    gate3SigmaLogLeak :
      Nat

    gate3SigmaLogLeakIs03375 :
      gate3SigmaLogLeak ≡ gate3SigmaLogLeakTenThousandths

    gate3SigmaSqrtIrrepLeak :
      Nat

    gate3SigmaSqrtIrrepLeakIs02961 :
      gate3SigmaSqrtIrrepLeak ≡
      gate3SigmaSqrtIrrepLeakTenThousandths

    gate3SigmaSqrtRawLeak :
      Nat

    gate3SigmaSqrtRawLeakIs02959 :
      gate3SigmaSqrtRawLeak ≡ gate3SigmaSqrtRawLeakTenThousandths

    gate3SigmaIrrepLeak :
      Nat

    gate3SigmaIrrepLeakIs02284 :
      gate3SigmaIrrepLeak ≡ gate3SigmaIrrepLeakTenThousandths

    gate3SigmaRawLeak :
      Nat

    gate3SigmaRawLeakIs02283 :
      gate3SigmaRawLeak ≡ gate3SigmaRawLeakTenThousandths

    rawMultiplicityIsPhysicalPolymerEntropy :
      Bool

    rawMultiplicityIsPhysicalPolymerEntropyIsFalse :
      rawMultiplicityIsPhysicalPolymerEntropy ≡ false

    moonshineSSPActsAsQuotient :
      Bool

    moonshineSSPActsAsQuotientIsTrue :
      moonshineSSPActsAsQuotient ≡ true

    quotientEntropyBoundProvedHere :
      Bool

    quotientEntropyBoundProvedHereIsFalse :
      quotientEntropyBoundProvedHere ≡ false

    ymC0QuotientProvedHere :
      Bool

    ymC0QuotientProvedHereIsFalse :
      ymC0QuotientProvedHere ≡ false

    gate3EntropyQuotientProvedHere :
      Bool

    gate3EntropyQuotientProvedHereIsFalse :
      gate3EntropyQuotientProvedHere ≡ false

    nsLowModeFenceProvedHere :
      Bool

    nsLowModeFenceProvedHereIsFalse :
      nsLowModeFenceProvedHere ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    ymClayPromoted :
      Bool

    ymClayPromotedIsFalse :
      ymClayPromoted ≡ false

    nsClayPromoted :
      Bool

    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    promotions :
      List MonsterQuotientPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      MonsterQuotientPromotion →
      ⊥

    rawMultiplicityText :
      String

    rawMultiplicityTextIsCanonical :
      rawMultiplicityText ≡ rawMultiplicityStatement

    quotientText :
      String

    quotientTextIsCanonical :
      quotientText ≡ quotientStatement

    thresholdSensitivityText :
      String

    thresholdSensitivityTextIsCanonical :
      thresholdSensitivityText ≡ thresholdSensitivityStatement

    gate3StressText :
      String

    gate3StressTextIsCanonical :
      gate3StressText ≡ gate3StressStatement

    effectiveMultiplicityText :
      String

    effectiveMultiplicityTextIsCanonical :
      effectiveMultiplicityText ≡ effectiveMultiplicityStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open MonsterMoonshineSSPQuotientControlReceipt public

canonicalMonsterMoonshineSSPQuotientControlReceipt :
  MonsterMoonshineSSPQuotientControlReceipt
canonicalMonsterMoonshineSSPQuotientControlReceipt =
  record
    { status =
        monsterMoonshineSSPQuotientTargetRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; carrierType =
        GL.FactorVec
    ; carrierTypeIsFactorVec =
        refl
    ; sspType =
        MO.SSP
    ; sspTypeIsSSP =
        refl
    ; monsterPrimeLaneReceipt =
        Lane.canonicalMoonshinePrimeLaneReceiptSurface
    ; monsterPrimeLaneIsCanonical =
        refl
    ; supersingularBridgeReceipt =
        SSPBridge.canonicalSupersingularPrimeLaneBridgeReceipt
    ; supersingularNatsAreCanonical =
        refl
    ; monsterToSSPMapReceipt =
        CTP.canonicalPrimeBumpCovarianceSemanticsReceipt
    ; monsterToSSPMapIsCanonical =
        refl
    ; monsterOrderDepthReceipt =
        Order.canonicalMonsterOrderDepthBoundReceipt
    ; monsterOrderDepthNoPromotion =
        refl
    ; jDistributionReceipt =
        JDist.canonicalMonsterMoonshineJDistributionSupportReceipt
    ; jDistributionNotPAdicValuationUniform =
        refl
    ; jDistributionNoClay =
        refl
    ; ymKPReceipt =
        YMKP.canonicalYMKPThresholdCorrectionReceipt
    ; ymPhysicalBetaDivergent =
        refl
    ; ymBetaTargetReceipt =
        YMBeta.canonicalYMBalabanPhysicalBetaBridgeTargetReceipt
    ; ymBetaBridgeStillOpen =
        refl
    ; gate3DigitReceipt =
        Gate3Digit.canonicalGate3DigitExpansionPAWOTGPartialResultReceipt
    ; gate3DigitNoGate3Promotion =
        refl
    ; gate3TargetReceipt =
        Gate3Target.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; gate3TargetInfANStillOpen =
        refl
    ; nsThetaCorrectionReceipt =
        NS.canonicalNSThetaPressureMarginCorrectionReceipt
    ; nsThetaNoClay =
        refl
    ; clayAsymmetryReceipt =
        Asymmetry.canonicalClayBlockerAsymmetryReceipt
    ; clayAsymmetryNoClay =
        refl
    ; multiplicityData =
        canonicalMonsterMultiplicityData
    ; multiplicityDataAreCanonical =
        refl
    ; quotientMechanisms =
        canonicalSSPQuotientMechanisms
    ; quotientMechanismsAreCanonical =
        refl
    ; entropyConsequences =
        canonicalQuotientEntropyConsequences
    ; entropyConsequencesAreCanonical =
        refl
    ; openObligations =
        canonicalQuotientControlOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; c1 =
        c1Monster
    ; c1Is196884 =
        refl
    ; c2 =
        c2Monster
    ; c2Is21493760 =
        refl
    ; irrep1 =
        irrep1Monster
    ; irrep1Is196883 =
        refl
    ; irrep2 =
        irrep2Monster
    ; irrep2Is21296876 =
        refl
    ; rawRatio =
        rawRatioApprox
    ; rawRatioIsApprox109 =
        refl
    ; irrepRatio =
        irrepRatioApprox
    ; irrepRatioIsApprox108 =
        refl
    ; sqrtRawRatio =
        sqrtRawRatioApproxHundredths
    ; sqrtRawRatioIs1045Hundredths =
        refl
    ; sqrtIrrepRatio =
        sqrtIrrepRatioApproxHundredths
    ; sqrtIrrepRatioIs1040Hundredths =
        refl
    ; sspCount =
        sspPrimeCount
    ; sspCountIs15 =
        refl
    ; betaAbsC0One =
        betaAbsC0OneHundredths
    ; betaAbsC0OneIs1297 =
        refl
    ; betaAbsLogLeak =
        betaAbsLogLeakHundredths
    ; betaAbsLogLeakIs1936 =
        refl
    ; betaAbsSqrtIrrepLeak =
        betaAbsSqrtIrrepLeakHundredths
    ; betaAbsSqrtIrrepLeakIs2265 =
        refl
    ; betaAbsSqrtLeak =
        betaAbsSqrtLeakHundredths
    ; betaAbsSqrtLeakIs2266 =
        refl
    ; betaAbsIrrepLeak =
        betaAbsIrrepLeakHundredths
    ; betaAbsIrrepLeakIs3231 =
        refl
    ; betaAbsRawLeak =
        betaAbsRawLeakHundredths
    ; betaAbsRawLeakIs3235 =
        refl
    ; gate3SigmaBaseline =
        gate3SigmaBaselineTenThousandths
    ; gate3SigmaBaselineIs05052 =
        refl
    ; gate3SigmaLogLeak =
        gate3SigmaLogLeakTenThousandths
    ; gate3SigmaLogLeakIs03375 =
        refl
    ; gate3SigmaSqrtIrrepLeak =
        gate3SigmaSqrtIrrepLeakTenThousandths
    ; gate3SigmaSqrtIrrepLeakIs02961 =
        refl
    ; gate3SigmaSqrtRawLeak =
        gate3SigmaSqrtRawLeakTenThousandths
    ; gate3SigmaSqrtRawLeakIs02959 =
        refl
    ; gate3SigmaIrrepLeak =
        gate3SigmaIrrepLeakTenThousandths
    ; gate3SigmaIrrepLeakIs02284 =
        refl
    ; gate3SigmaRawLeak =
        gate3SigmaRawLeakTenThousandths
    ; gate3SigmaRawLeakIs02283 =
        refl
    ; rawMultiplicityIsPhysicalPolymerEntropy =
        false
    ; rawMultiplicityIsPhysicalPolymerEntropyIsFalse =
        refl
    ; moonshineSSPActsAsQuotient =
        true
    ; moonshineSSPActsAsQuotientIsTrue =
        refl
    ; quotientEntropyBoundProvedHere =
        false
    ; quotientEntropyBoundProvedHereIsFalse =
        refl
    ; ymC0QuotientProvedHere =
        false
    ; ymC0QuotientProvedHereIsFalse =
        refl
    ; gate3EntropyQuotientProvedHere =
        false
    ; gate3EntropyQuotientProvedHereIsFalse =
        refl
    ; nsLowModeFenceProvedHere =
        false
    ; nsLowModeFenceProvedHereIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; ymClayPromoted =
        false
    ; ymClayPromotedIsFalse =
        refl
    ; nsClayPromoted =
        false
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        monsterQuotientPromotionImpossibleHere
    ; rawMultiplicityText =
        rawMultiplicityStatement
    ; rawMultiplicityTextIsCanonical =
        refl
    ; quotientText =
        quotientStatement
    ; quotientTextIsCanonical =
        refl
    ; thresholdSensitivityText =
        thresholdSensitivityStatement
    ; thresholdSensitivityTextIsCanonical =
        refl
    ; gate3StressText =
        gate3StressStatement
    ; gate3StressTextIsCanonical =
        refl
    ; effectiveMultiplicityText =
        effectiveMultiplicityStatement
    ; effectiveMultiplicityTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalMonsterQuotientRawMultiplicityNotC0 :
  rawMultiplicityIsPhysicalPolymerEntropy
    canonicalMonsterMoonshineSSPQuotientControlReceipt
  ≡
  false
canonicalMonsterQuotientRawMultiplicityNotC0 =
  refl

canonicalMonsterQuotientStillOpen :
  quotientEntropyBoundProvedHere
    canonicalMonsterMoonshineSSPQuotientControlReceipt
  ≡
  false
canonicalMonsterQuotientStillOpen =
  refl

canonicalMonsterQuotientNoPromotion :
  terminalPromoted canonicalMonsterMoonshineSSPQuotientControlReceipt
  ≡
  false
canonicalMonsterQuotientNoPromotion =
  refl
