module DASHI.Physics.Closure.MonsterMoonshineJDistributionSupportReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Monster Moonshine j-distribution support receipt.
--
-- This receipt records the Monster order prime-support exponents, the
-- q-expansion density grammar for the j coefficients, and the corrected
-- low-n observation boundary.  The j-coefficient growth is recorded as
-- q-expansion representation growth; it is not p-adic valuation uniformity
-- and it does not promote a Clay or Monster-theorem lemma.

data MonsterMoonshineJDistributionSupportStatus : Set where
  jDistributionSupportGrammarRecordedNoClayPromotion :
    MonsterMoonshineJDistributionSupportStatus

data JDistributionInterpretation : Set where
  qExpansionRepresentationGrowth :
    JDistributionInterpretation

data JDistributionNonInterpretation : Set where
  notPAdicValuationUniformity :
    JDistributionNonInterpretation

  notClayLemma :
    JDistributionNonInterpretation

data LowNCarrierActivityClaim : Set where
  depth1Depth2PolymersDominateFirstEnumeration :
    LowNCarrierActivityClaim

data MonsterMoonshineJDistributionPromotion : Set where

monsterMoonshineJDistributionPromotionImpossibleHere :
  MonsterMoonshineJDistributionPromotion →
  ⊥
monsterMoonshineJDistributionPromotionImpossibleHere ()

record MonsterOrderPrimePowerSupport : Set where
  field
    primeLane :
      Lane.MonsterPrimeLane

    prime :
      Nat

    primeIsLaneNat :
      prime ≡ Lane.monsterPrimeLaneToNat primeLane

    exponent :
      Nat

open MonsterOrderPrimePowerSupport public

canonicalMonsterOrderPrimePowerSupport :
  List MonsterOrderPrimePowerSupport
canonicalMonsterOrderPrimePowerSupport =
  record
    { primeLane =
        Lane.p2
    ; prime =
        2
    ; primeIsLaneNat =
        refl
    ; exponent =
        46
    }
  ∷ record
    { primeLane =
        Lane.p3
    ; prime =
        3
    ; primeIsLaneNat =
        refl
    ; exponent =
        20
    }
  ∷ record
    { primeLane =
        Lane.p5
    ; prime =
        5
    ; primeIsLaneNat =
        refl
    ; exponent =
        9
    }
  ∷ record
    { primeLane =
        Lane.p7
    ; prime =
        7
    ; primeIsLaneNat =
        refl
    ; exponent =
        6
    }
  ∷ record
    { primeLane =
        Lane.p11
    ; prime =
        11
    ; primeIsLaneNat =
        refl
    ; exponent =
        2
    }
  ∷ record
    { primeLane =
        Lane.p13
    ; prime =
        13
    ; primeIsLaneNat =
        refl
    ; exponent =
        3
    }
  ∷ record
    { primeLane =
        Lane.p17
    ; prime =
        17
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p19
    ; prime =
        19
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p23
    ; prime =
        23
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p29
    ; prime =
        29
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p31
    ; prime =
        31
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p41
    ; prime =
        41
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p47
    ; prime =
        47
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p59
    ; prime =
        59
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ record
    { primeLane =
        Lane.p71
    ; prime =
        71
    ; primeIsLaneNat =
        refl
    ; exponent =
        1
    }
  ∷ []

canonicalMonsterOrderPrimeSupportFormula : String
canonicalMonsterOrderPrimeSupportFormula =
  "2^46*3^20*5^9*7^6*11^2*13^3*17*19*23*29*31*41*47*59*71"

jExpansionDensityAsymptoticGrammar : String
jExpansionDensityAsymptoticGrammar =
  "c(n) ~ exp(4*pi*sqrt n)/(sqrt 2*n^(3/4))"

correctedRatioObservation : String
correctedRatioObservation =
  "The ratios c(n)/c(n-1) decrease from about 265 to about 7 by n=10; this is q-expansion representation growth, not p-adic valuation uniformity."

lowNCoefficientDominanceStatement : String
lowNCoefficientDominanceStatement =
  "Low-n coefficients dominate short-polymer carrier activity: c1=196884 and c2=21493760, so depth-1 and depth-2 polymers dominate the first enumeration."

record LowNJCoefficientCarrierDominance : Set where
  field
    c1 :
      Nat

    c1Is196884 :
      c1 ≡ 196884

    c2 :
      Nat

    c2Is21493760 :
      c2 ≡ 21493760

    firstEnumerationDominance :
      LowNCarrierActivityClaim

    firstEnumerationDominanceIsDepth1Depth2 :
      firstEnumerationDominance
      ≡
      depth1Depth2PolymersDominateFirstEnumeration

open LowNJCoefficientCarrierDominance public

canonicalLowNJCoefficientCarrierDominance :
  LowNJCoefficientCarrierDominance
canonicalLowNJCoefficientCarrierDominance =
  record
    { c1 =
        196884
    ; c1Is196884 =
        refl
    ; c2 =
        21493760
    ; c2Is21493760 =
        refl
    ; firstEnumerationDominance =
        depth1Depth2PolymersDominateFirstEnumeration
    ; firstEnumerationDominanceIsDepth1Depth2 =
        refl
    }

record JCoefficientRatioObservation : Set where
  field
    interpretation :
      JDistributionInterpretation

    interpretationIsQExpansionRepresentationGrowth :
      interpretation ≡ qExpansionRepresentationGrowth

    nonInterpretation :
      JDistributionNonInterpretation

    nonInterpretationIsNotPAdicUniformity :
      nonInterpretation ≡ notPAdicValuationUniformity

    firstRatioApprox :
      Nat

    firstRatioApproxIs265 :
      firstRatioApprox ≡ 265

    ratioByN10Approx :
      Nat

    ratioByN10ApproxIs7 :
      ratioByN10Approx ≡ 7

    ratioIndexBound :
      Nat

    ratioIndexBoundIs10 :
      ratioIndexBound ≡ 10

    ratiosDecreaseThroughN10 :
      Bool

    ratiosDecreaseThroughN10IsTrue :
      ratiosDecreaseThroughN10 ≡ true

open JCoefficientRatioObservation public

canonicalJCoefficientRatioObservation :
  JCoefficientRatioObservation
canonicalJCoefficientRatioObservation =
  record
    { interpretation =
        qExpansionRepresentationGrowth
    ; interpretationIsQExpansionRepresentationGrowth =
        refl
    ; nonInterpretation =
        notPAdicValuationUniformity
    ; nonInterpretationIsNotPAdicUniformity =
        refl
    ; firstRatioApprox =
        265
    ; firstRatioApproxIs265 =
        refl
    ; ratioByN10Approx =
        7
    ; ratioByN10ApproxIs7 =
        refl
    ; ratioIndexBound =
        10
    ; ratioIndexBoundIs10 =
        refl
    ; ratiosDecreaseThroughN10 =
        true
    ; ratiosDecreaseThroughN10IsTrue =
        refl
    }

record MonsterMoonshineJDistributionSupportReceipt : Setω where
  field
    status :
      MonsterMoonshineJDistributionSupportStatus

    statusIsCanonical :
      status ≡ jDistributionSupportGrammarRecordedNoClayPromotion

    monsterOrderPrimePowerSupport :
      List MonsterOrderPrimePowerSupport

    monsterOrderPrimePowerSupportIsCanonical :
      monsterOrderPrimePowerSupport
      ≡
      canonicalMonsterOrderPrimePowerSupport

    monsterOrderPrimeSupport :
      List Lane.MonsterPrimeLane

    monsterOrderPrimeSupportIsCanonical :
      monsterOrderPrimeSupport ≡ Lane.canonicalMonsterPrimeLane

    monsterOrderPrimeSupportFormula :
      String

    monsterOrderPrimeSupportFormulaIsCanonical :
      monsterOrderPrimeSupportFormula
      ≡
      canonicalMonsterOrderPrimeSupportFormula

    jExpansionDensityAsymptotic :
      String

    jExpansionDensityAsymptoticIsCanonical :
      jExpansionDensityAsymptotic ≡ jExpansionDensityAsymptoticGrammar

    ratioObservation :
      JCoefficientRatioObservation

    ratioObservationIsCanonical :
      ratioObservation ≡ canonicalJCoefficientRatioObservation

    lowNCoefficientDominance :
      LowNJCoefficientCarrierDominance

    lowNCoefficientDominanceIsCanonical :
      lowNCoefficientDominance ≡ canonicalLowNJCoefficientCarrierDominance

    moonshineIsCarrierSupportGrammar :
      Bool

    moonshineIsCarrierSupportGrammarIsTrue :
      moonshineIsCarrierSupportGrammar ≡ true

    monsterTheoremIsNotClayLemma :
      Bool

    monsterTheoremIsNotClayLemmaIsTrue :
      monsterTheoremIsNotClayLemma ≡ true

    jDistributionIsNotPAdicValuationUniform :
      Bool

    jDistributionIsNotPAdicValuationUniformIsTrue :
      jDistributionIsNotPAdicValuationUniform ≡ true

    lowNCoeffsDominateHighN :
      Bool

    lowNCoeffsDominateHighNIsTrue :
      lowNCoeffsDominateHighN ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    noPromotionWithoutAuthority :
      MonsterMoonshineJDistributionPromotion → ⊥

    correctedRatioStatement :
      String

    correctedRatioStatementIsCanonical :
      correctedRatioStatement ≡ correctedRatioObservation

    lowNStatement :
      String

    lowNStatementIsCanonical :
      lowNStatement ≡ lowNCoefficientDominanceStatement

    receiptBoundary :
      List String

open MonsterMoonshineJDistributionSupportReceipt public

canonicalMonsterMoonshineJDistributionSupportReceipt :
  MonsterMoonshineJDistributionSupportReceipt
canonicalMonsterMoonshineJDistributionSupportReceipt =
  record
    { status =
        jDistributionSupportGrammarRecordedNoClayPromotion
    ; statusIsCanonical =
        refl
    ; monsterOrderPrimePowerSupport =
        canonicalMonsterOrderPrimePowerSupport
    ; monsterOrderPrimePowerSupportIsCanonical =
        refl
    ; monsterOrderPrimeSupport =
        Lane.canonicalMonsterPrimeLane
    ; monsterOrderPrimeSupportIsCanonical =
        refl
    ; monsterOrderPrimeSupportFormula =
        canonicalMonsterOrderPrimeSupportFormula
    ; monsterOrderPrimeSupportFormulaIsCanonical =
        refl
    ; jExpansionDensityAsymptotic =
        jExpansionDensityAsymptoticGrammar
    ; jExpansionDensityAsymptoticIsCanonical =
        refl
    ; ratioObservation =
        canonicalJCoefficientRatioObservation
    ; ratioObservationIsCanonical =
        refl
    ; lowNCoefficientDominance =
        canonicalLowNJCoefficientCarrierDominance
    ; lowNCoefficientDominanceIsCanonical =
        refl
    ; moonshineIsCarrierSupportGrammar =
        true
    ; moonshineIsCarrierSupportGrammarIsTrue =
        refl
    ; monsterTheoremIsNotClayLemma =
        true
    ; monsterTheoremIsNotClayLemmaIsTrue =
        refl
    ; jDistributionIsNotPAdicValuationUniform =
        true
    ; jDistributionIsNotPAdicValuationUniformIsTrue =
        refl
    ; lowNCoeffsDominateHighN =
        true
    ; lowNCoeffsDominateHighNIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        monsterMoonshineJDistributionPromotionImpossibleHere
    ; correctedRatioStatement =
        correctedRatioObservation
    ; correctedRatioStatementIsCanonical =
        refl
    ; lowNStatement =
        lowNCoefficientDominanceStatement
    ; lowNStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Records Monster order prime support for SSP15 with exponents 2^46, 3^20, 5^9, 7^6, 11^2, 13^3, and exponent 1 for 17,19,23,29,31,41,47,59,71"
        ∷ "Records j-expansion density asymptotic grammar c(n) ~ exp(4*pi*sqrt n)/(sqrt 2*n^(3/4))"
        ∷ "Corrects the 10x observation: ratios decrease from about 265 to about 7 by n=10"
        ∷ "The corrected ratio observation is q-expansion representation growth, not p-adic valuation uniformity"
        ∷ "Records low-n coefficient dominance with c1=196884 and c2=21493760"
        ∷ "Depth-1 and depth-2 polymers dominate the first enumeration"
        ∷ "Flags: moonshineIsCarrierSupportGrammar=true; monsterTheoremIsNotClayLemma=true; jDistributionIsNotPAdicValuationUniform=true; lowNCoeffsDominateHighN=true; clayPromoted=false"
        ∷ []
    }

moonshineJDistributionRecordsCarrierSupportGrammar :
  moonshineIsCarrierSupportGrammar
    canonicalMonsterMoonshineJDistributionSupportReceipt
  ≡
  true
moonshineJDistributionRecordsCarrierSupportGrammar =
  refl

moonshineJDistributionNotPAdicValuationUniform :
  jDistributionIsNotPAdicValuationUniform
    canonicalMonsterMoonshineJDistributionSupportReceipt
  ≡
  true
moonshineJDistributionNotPAdicValuationUniform =
  refl

moonshineJDistributionLowNCoeffsDominateHighN :
  lowNCoeffsDominateHighN
    canonicalMonsterMoonshineJDistributionSupportReceipt
  ≡
  true
moonshineJDistributionLowNCoeffsDominateHighN =
  refl

moonshineJDistributionClayNotPromoted :
  clayPromoted canonicalMonsterMoonshineJDistributionSupportReceipt ≡ false
moonshineJDistributionClayNotPromoted =
  refl
