module DASHI.Physics.Closure.FractranPrimeLaneValuationReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Combinatorics.FractranCOL as FractranCOL
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine

------------------------------------------------------------------------
-- Monster prime valuations as a FRACDASH / FRACTRAN-style exponent vector.
--
-- The Monster order valuation vector is naturally a prime-register state:
-- each supersingular prime is a lane and v_p(|M|) is the exponent stored in
-- that lane.  This is useful executable evidence for FRACDASH, but it is not
-- a DHR endomorphism computation and it does not derive the Standard Model
-- gauge group.

data FractranPrimeLaneValuationStatus : Set where
  fractranValuationBridgeRecordedNoGaugePromotion :
    FractranPrimeLaneValuationStatus

data FractranPrimeLaneOpenObligation : Set where
  missingFifteenLaneFractranCOL :
    FractranPrimeLaneOpenObligation

  missingSignedExponentVectorBridge :
    FractranPrimeLaneOpenObligation

  missingFRACDASHExecutableWitnessImport :
    FractranPrimeLaneOpenObligation

  missingProjectionPreservationProof :
    FractranPrimeLaneOpenObligation

  missingDHRInterpretationOfProjectedRegisters :
    FractranPrimeLaneOpenObligation

  missingMatterLaneCardinalityReconciliation :
    FractranPrimeLaneOpenObligation

canonicalFractranPrimeLaneOpenObligations :
  List FractranPrimeLaneOpenObligation
canonicalFractranPrimeLaneOpenObligations =
  missingFifteenLaneFractranCOL
  ∷ missingSignedExponentVectorBridge
  ∷ missingFRACDASHExecutableWitnessImport
  ∷ missingProjectionPreservationProof
  ∷ missingDHRInterpretationOfProjectedRegisters
  ∷ missingMatterLaneCardinalityReconciliation
  ∷ []

monsterOrderValuation :
  Moonshine.MonsterPrimeLane →
  Nat
monsterOrderValuation Moonshine.p2 =
  46
monsterOrderValuation Moonshine.p3 =
  20
monsterOrderValuation Moonshine.p5 =
  9
monsterOrderValuation Moonshine.p7 =
  6
monsterOrderValuation Moonshine.p11 =
  2
monsterOrderValuation Moonshine.p13 =
  2
monsterOrderValuation Moonshine.p17 =
  2
monsterOrderValuation Moonshine.p19 =
  2
monsterOrderValuation Moonshine.p23 =
  2
monsterOrderValuation Moonshine.p29 =
  1
monsterOrderValuation Moonshine.p31 =
  1
monsterOrderValuation Moonshine.p41 =
  1
monsterOrderValuation Moonshine.p47 =
  1
monsterOrderValuation Moonshine.p59 =
  1
monsterOrderValuation Moonshine.p71 =
  1

monsterOrderExponentVector15 :
  List Nat
monsterOrderExponentVector15 =
  46
  ∷ 20
  ∷ 9
  ∷ 6
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ []

minNat :
  Nat →
  Nat →
  Nat
minNat zero _ =
  zero
minNat (suc _) zero =
  zero
minNat (suc m) (suc n) =
  suc (minNat m n)

valuationCappedAt3 :
  Moonshine.MonsterPrimeLane →
  Nat
valuationCappedAt3 p =
  minNat (monsterOrderValuation p) 3

monsterOrderProjectionMinVp3Vector15 :
  List Nat
monsterOrderProjectionMinVp3Vector15 =
  3
  ∷ 3
  ∷ 3
  ∷ 3
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ []

canonicalOverproducedSU3LikePrimeLanes :
  List Moonshine.MonsterPrimeLane
canonicalOverproducedSU3LikePrimeLanes =
  Moonshine.p2
  ∷ Moonshine.p3
  ∷ Moonshine.p5
  ∷ Moonshine.p7
  ∷ []

overproducedSU3LikeLaneCount :
  Nat
overproducedSU3LikeLaneCount =
  4

capAt3P2Is3 :
  valuationCappedAt3 Moonshine.p2 ≡ 3
capAt3P2Is3 =
  refl

capAt3P3Is3 :
  valuationCappedAt3 Moonshine.p3 ≡ 3
capAt3P3Is3 =
  refl

capAt3P5Is3 :
  valuationCappedAt3 Moonshine.p5 ≡ 3
capAt3P5Is3 =
  refl

capAt3P7Is3 :
  valuationCappedAt3 Moonshine.p7 ≡ 3
capAt3P7Is3 =
  refl

data CappedValuationInterpretation : Set where
  exponentVectorProjection :
    CappedValuationInterpretation

  notDHRLaneDimensionComputation :
    CappedValuationInterpretation

  overproducesSU3LikeLanes :
    CappedValuationInterpretation

canonicalCappedValuationInterpretation :
  List CappedValuationInterpretation
canonicalCappedValuationInterpretation =
  exponentVectorProjection
  ∷ notDHRLaneDimensionComputation
  ∷ overproducesSU3LikeLanes
  ∷ []

data HighEnergyPatiSalamLaneAssignment : Set where
  assignedU1 :
    HighEnergyPatiSalamLaneAssignment

  assignedSU2L :
    HighEnergyPatiSalamLaneAssignment

  assignedSU3c :
    HighEnergyPatiSalamLaneAssignment

  assignedSU2RBrokenAtSeesaw :
    HighEnergyPatiSalamLaneAssignment

  inactiveOrMatterLane :
    HighEnergyPatiSalamLaneAssignment

data MonsterPrimeLaneAtLeast11 : Moonshine.MonsterPrimeLane → Set where
  p11AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p11

  p13AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p13

  p17AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p17

  p19AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p19

  p23AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p23

  p29AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p29

  p31AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p31

  p41AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p41

  p47AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p47

  p59AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p59

  p71AtLeast11 :
    MonsterPrimeLaneAtLeast11 Moonshine.p71

canonicalPatiSalamGaugePrimeLanes :
  List Moonshine.MonsterPrimeLane
canonicalPatiSalamGaugePrimeLanes =
  Moonshine.p2
  ∷ Moonshine.p3
  ∷ Moonshine.p5
  ∷ Moonshine.p7
  ∷ []

canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge :
  List Moonshine.MonsterPrimeLane
canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge =
  Moonshine.p11
  ∷ Moonshine.p13
  ∷ Moonshine.p17
  ∷ Moonshine.p19
  ∷ Moonshine.p23
  ∷ Moonshine.p29
  ∷ Moonshine.p31
  ∷ Moonshine.p41
  ∷ Moonshine.p47
  ∷ Moonshine.p59
  ∷ Moonshine.p71
  ∷ []

expectedMatterLaneCountAfterFourGaugeLanes :
  Nat
expectedMatterLaneCountAfterFourGaugeLanes =
  12

actualMatterLaneCountAfterFourGaugeLanes :
  Nat
actualMatterLaneCountAfterFourGaugeLanes =
  11

data MatterLaneCardinalityMismatchStatus : Set where
  expectedTwelveActualElevenOpenObligation :
    MatterLaneCardinalityMismatchStatus

record MatterLaneCardinalityMismatch : Setω where
  field
    status :
      MatterLaneCardinalityMismatchStatus

    gaugeLanes :
      List Moonshine.MonsterPrimeLane

    gaugeLanesAreCanonical :
      gaugeLanes
      ≡
      canonicalPatiSalamGaugePrimeLanes

    nonGaugeMatterLanes :
      List Moonshine.MonsterPrimeLane

    nonGaugeMatterLanesAreCanonical :
      nonGaugeMatterLanes
      ≡
      canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge

    expectedMatterLaneCount :
      Nat

    expectedMatterLaneCountIs12 :
      expectedMatterLaneCount
      ≡
      expectedMatterLaneCountAfterFourGaugeLanes

    actualMatterLaneCount :
      Nat

    actualMatterLaneCountIs11 :
      actualMatterLaneCount
      ≡
      actualMatterLaneCountAfterFourGaugeLanes

    mismatchRecorded :
      Bool

    mismatchRecordedIsTrue :
      mismatchRecorded ≡ true

    matterAssignmentPromoted :
      Bool

    matterAssignmentPromotedIsFalse :
      matterAssignmentPromoted ≡ false

    boundary :
      List String

open MatterLaneCardinalityMismatch public

canonicalMatterLaneCardinalityMismatch :
  MatterLaneCardinalityMismatch
canonicalMatterLaneCardinalityMismatch =
  record
    { status =
        expectedTwelveActualElevenOpenObligation
    ; gaugeLanes =
        canonicalPatiSalamGaugePrimeLanes
    ; gaugeLanesAreCanonical =
        refl
    ; nonGaugeMatterLanes =
        canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge
    ; nonGaugeMatterLanesAreCanonical =
        refl
    ; expectedMatterLaneCount =
        expectedMatterLaneCountAfterFourGaugeLanes
    ; expectedMatterLaneCountIs12 =
        refl
    ; actualMatterLaneCount =
        actualMatterLaneCountAfterFourGaugeLanes
    ; actualMatterLaneCountIs11 =
        refl
    ; mismatchRecorded =
        true
    ; mismatchRecordedIsTrue =
        refl
    ; matterAssignmentPromoted =
        false
    ; matterAssignmentPromotedIsFalse =
        refl
    ; boundary =
        "After gauge lanes {2,3,5,7}, the listed non-gauge lane set is {11,13,17,19,23,29,31,41,47,59,71}"
        ∷ "That set has actual count 11, while the tranche text asks for twelve remaining matter primes"
        ∷ "The mismatch is recorded as an open obligation rather than silently padding or reusing a lane"
        ∷ []
    }

data ShiftedFNChargeFromMonsterValuation : Set where
  gaugeLaneChargeNeedsHiggsNormalisation :
    ShiftedFNChargeFromMonsterValuation

  fnChargeZeroFromValuationTwo :
    ShiftedFNChargeFromMonsterValuation

  fnChargeMinusOneFromValuationOne :
    ShiftedFNChargeFromMonsterValuation

monsterValuationMinus2FNChargeTarget :
  Moonshine.MonsterPrimeLane →
  ShiftedFNChargeFromMonsterValuation
monsterValuationMinus2FNChargeTarget Moonshine.p2 =
  gaugeLaneChargeNeedsHiggsNormalisation
monsterValuationMinus2FNChargeTarget Moonshine.p3 =
  gaugeLaneChargeNeedsHiggsNormalisation
monsterValuationMinus2FNChargeTarget Moonshine.p5 =
  gaugeLaneChargeNeedsHiggsNormalisation
monsterValuationMinus2FNChargeTarget Moonshine.p7 =
  gaugeLaneChargeNeedsHiggsNormalisation
monsterValuationMinus2FNChargeTarget Moonshine.p11 =
  fnChargeZeroFromValuationTwo
monsterValuationMinus2FNChargeTarget Moonshine.p13 =
  fnChargeZeroFromValuationTwo
monsterValuationMinus2FNChargeTarget Moonshine.p17 =
  fnChargeZeroFromValuationTwo
monsterValuationMinus2FNChargeTarget Moonshine.p19 =
  fnChargeZeroFromValuationTwo
monsterValuationMinus2FNChargeTarget Moonshine.p23 =
  fnChargeZeroFromValuationTwo
monsterValuationMinus2FNChargeTarget Moonshine.p29 =
  fnChargeMinusOneFromValuationOne
monsterValuationMinus2FNChargeTarget Moonshine.p31 =
  fnChargeMinusOneFromValuationOne
monsterValuationMinus2FNChargeTarget Moonshine.p41 =
  fnChargeMinusOneFromValuationOne
monsterValuationMinus2FNChargeTarget Moonshine.p47 =
  fnChargeMinusOneFromValuationOne
monsterValuationMinus2FNChargeTarget Moonshine.p59 =
  fnChargeMinusOneFromValuationOne
monsterValuationMinus2FNChargeTarget Moonshine.p71 =
  fnChargeMinusOneFromValuationOne

matterLaneFNChargeP11IsZero :
  monsterValuationMinus2FNChargeTarget Moonshine.p11
  ≡
  fnChargeZeroFromValuationTwo
matterLaneFNChargeP11IsZero =
  refl

matterLaneFNChargeP23IsZero :
  monsterValuationMinus2FNChargeTarget Moonshine.p23
  ≡
  fnChargeZeroFromValuationTwo
matterLaneFNChargeP23IsZero =
  refl

matterLaneFNChargeP29IsMinusOne :
  monsterValuationMinus2FNChargeTarget Moonshine.p29
  ≡
  fnChargeMinusOneFromValuationOne
matterLaneFNChargeP29IsMinusOne =
  refl

matterLaneFNChargeP71IsMinusOne :
  monsterValuationMinus2FNChargeTarget Moonshine.p71
  ≡
  fnChargeMinusOneFromValuationOne
matterLaneFNChargeP71IsMinusOne =
  refl

record FNChargeFromMonsterValuationReceipt : Setω where
  field
    matterLaneCardinalityMismatch :
      MatterLaneCardinalityMismatch

    chargeFunction :
      Moonshine.MonsterPrimeLane →
      ShiftedFNChargeFromMonsterValuation

    chargeFunctionIsVpMinusTwoTarget :
      chargeFunction
      ≡
      monsterValuationMinus2FNChargeTarget

    v2MatterLanesMapToZero :
      Bool

    v2MatterLanesMapToZeroIsTrue :
      v2MatterLanesMapToZero ≡ true

    v1MatterLanesMapToMinusOne :
      Bool

    v1MatterLanesMapToMinusOneIsTrue :
      v1MatterLanesMapToMinusOne ≡ true

    higgsChargeNormalisationRemainsAdapter4 :
      Bool

    higgsChargeNormalisationRemainsAdapter4IsTrue :
      higgsChargeNormalisationRemainsAdapter4 ≡ true

    exactTexturePromoted :
      Bool

    exactTexturePromotedIsFalse :
      exactTexturePromoted ≡ false

    boundary :
      List String

open FNChargeFromMonsterValuationReceipt public

canonicalFNChargeFromMonsterValuationReceipt :
  FNChargeFromMonsterValuationReceipt
canonicalFNChargeFromMonsterValuationReceipt =
  record
    { matterLaneCardinalityMismatch =
        canonicalMatterLaneCardinalityMismatch
    ; chargeFunction =
        monsterValuationMinus2FNChargeTarget
    ; chargeFunctionIsVpMinusTwoTarget =
        refl
    ; v2MatterLanesMapToZero =
        true
    ; v2MatterLanesMapToZeroIsTrue =
        refl
    ; v1MatterLanesMapToMinusOne =
        true
    ; v1MatterLanesMapToMinusOneIsTrue =
        refl
    ; higgsChargeNormalisationRemainsAdapter4 =
        true
    ; higgsChargeNormalisationRemainsAdapter4IsTrue =
        refl
    ; exactTexturePromoted =
        false
    ; exactTexturePromotedIsFalse =
        refl
    ; boundary =
        "FN charge target is q_p = v_p(|M|)-2, represented here by symbolic signed charge classes"
        ∷ "Valuation-two matter lanes p11,p13,p17,p19,p23 map to charge 0"
        ∷ "Valuation-one matter lanes p29,p31,p41,p47,p59,p71 map to charge -1"
        ∷ "Gauge-lane charges and Higgs FN charge normalisation are not fixed by this projection"
        ∷ "Exact Yukawa textures are therefore not promoted from Monster valuations alone"
        ∷ []
    }

patiSalamHighEnergyAssignment :
  Moonshine.MonsterPrimeLane →
  HighEnergyPatiSalamLaneAssignment
patiSalamHighEnergyAssignment Moonshine.p2 =
  assignedU1
patiSalamHighEnergyAssignment Moonshine.p3 =
  assignedSU2L
patiSalamHighEnergyAssignment Moonshine.p5 =
  assignedSU3c
patiSalamHighEnergyAssignment Moonshine.p7 =
  assignedSU2RBrokenAtSeesaw
patiSalamHighEnergyAssignment Moonshine.p11 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p13 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p17 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p19 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p23 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p29 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p31 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p41 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p47 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p59 =
  inactiveOrMatterLane
patiSalamHighEnergyAssignment Moonshine.p71 =
  inactiveOrMatterLane

patiSalamP2IsU1 :
  patiSalamHighEnergyAssignment Moonshine.p2 ≡ assignedU1
patiSalamP2IsU1 =
  refl

patiSalamP3IsSU2L :
  patiSalamHighEnergyAssignment Moonshine.p3 ≡ assignedSU2L
patiSalamP3IsSU2L =
  refl

patiSalamP5IsSU3c :
  patiSalamHighEnergyAssignment Moonshine.p5 ≡ assignedSU3c
patiSalamP5IsSU3c =
  refl

patiSalamP7IsSU2RBrokenAtSeesaw :
  patiSalamHighEnergyAssignment Moonshine.p7 ≡ assignedSU2RBrokenAtSeesaw
patiSalamP7IsSU2RBrokenAtSeesaw =
  refl

patiSalamAtLeast11IsInactiveOrMatter :
  (p : Moonshine.MonsterPrimeLane) →
  MonsterPrimeLaneAtLeast11 p →
  patiSalamHighEnergyAssignment p ≡ inactiveOrMatterLane
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p11 p11AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p13 p13AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p17 p17AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p19 p19AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p23 p23AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p29 p29AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p31 p31AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p41 p41AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p47 p47AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p59 p59AtLeast11 =
  refl
patiSalamAtLeast11IsInactiveOrMatter Moonshine.p71 p71AtLeast11 =
  refl

record MonsterValuationExponentVectorReceipt : Setω where
  field
    lanes :
      List Moonshine.MonsterPrimeLane

    lanesAreCanonical :
      lanes
      ≡
      Moonshine.canonicalMonsterPrimeLane

    exponentVectorDimension :
      Nat

    exponentVectorDimensionIs15 :
      exponentVectorDimension ≡ 15

    exactExponentVector :
      List Nat

    exactExponentVectorIsMonsterOrder :
      exactExponentVector
      ≡
      monsterOrderExponentVector15

    valuation :
      Moonshine.MonsterPrimeLane →
      Nat

    valuationIsMonsterOrderValuation :
      valuation
      ≡
      monsterOrderValuation

    projectedCapAt3 :
      Moonshine.MonsterPrimeLane →
      Nat

    projectedCapAt3IsCanonical :
      projectedCapAt3
      ≡
      valuationCappedAt3

    projectedCapAt3Vector :
      List Nat

    projectedCapAt3VectorIsMinVp3 :
      projectedCapAt3Vector
      ≡
      monsterOrderProjectionMinVp3Vector15

    overproducedSU3LikeLanes :
      List Moonshine.MonsterPrimeLane

    overproducedSU3LikeLanesAreCanonical :
      overproducedSU3LikeLanes
      ≡
      canonicalOverproducedSU3LikePrimeLanes

    overproducedSU3LikeLaneCountValue :
      Nat

    overproducedSU3LikeLaneCountIs4 :
      overproducedSU3LikeLaneCountValue
      ≡
      overproducedSU3LikeLaneCount

    highEnergyAssignmentBridge :
      Moonshine.MonsterPrimeLane →
      HighEnergyPatiSalamLaneAssignment

    highEnergyAssignmentBridgeIsCanonical :
      highEnergyAssignmentBridge
      ≡
      patiSalamHighEnergyAssignment

    capAt3Interpretation :
      List CappedValuationInterpretation

    capAt3InterpretationIsCanonical :
      capAt3Interpretation
      ≡
      canonicalCappedValuationInterpretation

open MonsterValuationExponentVectorReceipt public

canonicalMonsterValuationExponentVectorReceipt :
  MonsterValuationExponentVectorReceipt
canonicalMonsterValuationExponentVectorReceipt =
  record
    { lanes =
        Moonshine.canonicalMonsterPrimeLane
    ; lanesAreCanonical =
        refl
    ; exponentVectorDimension =
        15
    ; exponentVectorDimensionIs15 =
        refl
    ; exactExponentVector =
        monsterOrderExponentVector15
    ; exactExponentVectorIsMonsterOrder =
        refl
    ; valuation =
        monsterOrderValuation
    ; valuationIsMonsterOrderValuation =
        refl
    ; projectedCapAt3 =
        valuationCappedAt3
    ; projectedCapAt3IsCanonical =
        refl
    ; projectedCapAt3Vector =
        monsterOrderProjectionMinVp3Vector15
    ; projectedCapAt3VectorIsMinVp3 =
        refl
    ; overproducedSU3LikeLanes =
        canonicalOverproducedSU3LikePrimeLanes
    ; overproducedSU3LikeLanesAreCanonical =
        refl
    ; overproducedSU3LikeLaneCountValue =
        overproducedSU3LikeLaneCount
    ; overproducedSU3LikeLaneCountIs4 =
        refl
    ; highEnergyAssignmentBridge =
        patiSalamHighEnergyAssignment
    ; highEnergyAssignmentBridgeIsCanonical =
        refl
    ; capAt3Interpretation =
        canonicalCappedValuationInterpretation
    ; capAt3InterpretationIsCanonical =
        refl
    }

record FractranCOLLocalHook : Setω where
  field
    localToyStateCarrier :
      Set

    localToyStateCarrierIsEV5 :
      localToyStateCarrier
      ≡
      FractranCOL.EV5

    localToyRuleList :
      List FractranCOL.Rule

    localToyRuleListIsCanonical :
      localToyRuleList
      ≡
      (FractranCOL.r1122 ∷ FractranCOL.r53 ∷ FractranCOL.r17 ∷ [])

    localToyIsFiveLaneOnly :
      Bool

    localToyIsFiveLaneOnlyIsTrue :
      localToyIsFiveLaneOnly ≡ true

open FractranCOLLocalHook public

canonicalFractranCOLLocalHook :
  FractranCOLLocalHook
canonicalFractranCOLLocalHook =
  record
    { localToyStateCarrier =
        FractranCOL.EV5
    ; localToyStateCarrierIsEV5 =
        refl
    ; localToyRuleList =
        FractranCOL.r1122 ∷ FractranCOL.r53 ∷ FractranCOL.r17 ∷ []
    ; localToyRuleListIsCanonical =
        refl
    ; localToyIsFiveLaneOnly =
        true
    ; localToyIsFiveLaneOnlyIsTrue =
        refl
    }

record FRACDASHSiblingExecutableHook : Setω where
  field
    siblingRepoPath :
      String

    bridgeCorrectnessPath :
      String

    stateSpacePath :
      String

    executableSemanticShape :
      String

    executableSemanticShape-v :
      executableSemanticShape
      ≡
      "source-state-to-signed-exponent-vector-IR-to-FRACTRAN-paired-prime-realization"

    importedAsAgdaProofHere :
      Bool

    importedAsAgdaProofHereIsFalse :
      importedAsAgdaProofHere ≡ false

open FRACDASHSiblingExecutableHook public

canonicalFRACDASHSiblingExecutableHook :
  FRACDASHSiblingExecutableHook
canonicalFRACDASHSiblingExecutableHook =
  record
    { siblingRepoPath =
        "../FRACDASH"
    ; bridgeCorrectnessPath =
        "../FRACDASH/BRIDGE_CORRECTNESS.md"
    ; stateSpacePath =
        "../FRACDASH/DASHI_STATE.md"
    ; executableSemanticShape =
        "source-state-to-signed-exponent-vector-IR-to-FRACTRAN-paired-prime-realization"
    ; executableSemanticShape-v =
        refl
    ; importedAsAgdaProofHere =
        false
    ; importedAsAgdaProofHereIsFalse =
        refl
    }

record FractranPrimeLaneValuationReceiptSurface : Setω where
  field
    status :
      FractranPrimeLaneValuationStatus

    monsterValuationVector :
      MonsterValuationExponentVectorReceipt

    localFractranCOLHook :
      FractranCOLLocalHook

    siblingExecutableHook :
      FRACDASHSiblingExecutableHook

    matterLaneCardinalityMismatch :
      MatterLaneCardinalityMismatch

    fnChargeFromMonsterValuation :
      FNChargeFromMonsterValuationReceipt

    openObligations :
      List FractranPrimeLaneOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalFractranPrimeLaneOpenObligations

    valuationIsRegisterExponentEvidence :
      Bool

    valuationIsRegisterExponentEvidenceIsTrue :
      valuationIsRegisterExponentEvidence ≡ true

    capAt3IsProjectionNotGaugeDerivation :
      Bool

    capAt3IsProjectionNotGaugeDerivationIsTrue :
      capAt3IsProjectionNotGaugeDerivation ≡ true

    highEnergyAssignmentIsConjecturalBridge :
      Bool

    highEnergyAssignmentIsConjecturalBridgeIsTrue :
      highEnergyAssignmentIsConjecturalBridge ≡ true

    laneDimensionComputedHere :
      Bool

    laneDimensionComputedHereIsFalse :
      laneDimensionComputedHere ≡ false

    boundary :
      List String

open FractranPrimeLaneValuationReceiptSurface public

canonicalFractranPrimeLaneValuationReceiptSurface :
  FractranPrimeLaneValuationReceiptSurface
canonicalFractranPrimeLaneValuationReceiptSurface =
  record
    { status =
        fractranValuationBridgeRecordedNoGaugePromotion
    ; monsterValuationVector =
        canonicalMonsterValuationExponentVectorReceipt
    ; localFractranCOLHook =
        canonicalFractranCOLLocalHook
    ; siblingExecutableHook =
        canonicalFRACDASHSiblingExecutableHook
    ; matterLaneCardinalityMismatch =
        canonicalMatterLaneCardinalityMismatch
    ; fnChargeFromMonsterValuation =
        canonicalFNChargeFromMonsterValuationReceipt
    ; openObligations =
        canonicalFractranPrimeLaneOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; valuationIsRegisterExponentEvidence =
        true
    ; valuationIsRegisterExponentEvidenceIsTrue =
        refl
    ; capAt3IsProjectionNotGaugeDerivation =
        true
    ; capAt3IsProjectionNotGaugeDerivationIsTrue =
        refl
    ; highEnergyAssignmentIsConjecturalBridge =
        true
    ; highEnergyAssignmentIsConjecturalBridgeIsTrue =
        refl
    ; laneDimensionComputedHere =
        false
    ; laneDimensionComputedHereIsFalse =
        refl
    ; boundary =
        "Monster-order p-adic valuations are recorded as the exact 15-entry exponent vector [46,20,9,6,2,2,2,2,2,1,1,1,1,1,1]"
        ∷ "The bounded projection is min(v_p(|M|),3) = [3,3,3,3,2,2,2,2,2,1,1,1,1,1,1] and overproduces four SU3-like cap-3 lanes at p2,p3,p5,p7"
        ∷ "The Pati-Salam high-energy bridge assigns p2->U1, p3->SU2L, p5->SU3c, p7->SU2R-broken-at-seesaw, and p>=11 to inactive/matter lanes"
        ∷ "The listed post-gauge matter lanes have count 11, not 12; this is an explicit MatterLaneCardinalityMismatch open obligation"
        ∷ "The FN charge target q_p = v_p(|M|)-2 maps valuation-two matter lanes to 0 and valuation-one matter lanes to -1, but Higgs normalisation remains Adapter 4"
        ∷ "The Pati-Salam bridge is conjectural high-energy assignment metadata, not a computed DHR laneDimension"
        ∷ "This receipt does not replace the DHR localized-endomorphism/statistics computation required for laneDimension"
        ∷ []
    }
