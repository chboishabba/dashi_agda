module DASHI.Physics.Closure.MatterRepresentationReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine
import DASHI.Physics.Closure.FractranPrimeLaneValuationReceiptSurface as FractranLane
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR

------------------------------------------------------------------------
-- Standard Model matter-representation receipt surface.
--
-- This module records target sockets for deriving or adapting Standard Model
-- matter representations.  It does not derive the Standard Model group,
-- hypercharge assignments, anomaly cancellation, generations, Yukawa
-- matrices, CKM/PMNS mixing, neutrino sector, or a GRQFT/TOE receipt.

data MatterRepresentationSurfaceStatus : Set where
  matterRepresentationTargetsOnlyNoPromotion :
    MatterRepresentationSurfaceStatus

data MatterRepresentationPromotionAuthorityToken : Set where

data MatterPrimeLaneTarget : Set where
  matterPrimeLaneDHRLocalizedEndomorphismTarget :
    MatterPrimeLaneTarget

  matterPrimeLaneTransportabilityTarget :
    MatterPrimeLaneTarget

  matterPrimeLaneSectorRepresentationTarget :
    MatterPrimeLaneTarget

  matterPrimeLaneDimensionConjectureTarget :
    MatterPrimeLaneTarget

canonicalMatterPrimeLaneTargets :
  List MatterPrimeLaneTarget
canonicalMatterPrimeLaneTargets =
  matterPrimeLaneDHRLocalizedEndomorphismTarget
  ∷ matterPrimeLaneTransportabilityTarget
  ∷ matterPrimeLaneSectorRepresentationTarget
  ∷ matterPrimeLaneDimensionConjectureTarget
  ∷ []

data StandardModelMatterSectorTarget : Set where
  leftQuarkDoubletTarget :
    StandardModelMatterSectorTarget

  rightUpQuarkTarget :
    StandardModelMatterSectorTarget

  rightDownQuarkTarget :
    StandardModelMatterSectorTarget

  leftLeptonDoubletTarget :
    StandardModelMatterSectorTarget

  rightChargedLeptonTarget :
    StandardModelMatterSectorTarget

  higgsDoubletTarget :
    StandardModelMatterSectorTarget

canonicalStandardModelMatterSectorTargets :
  List StandardModelMatterSectorTarget
canonicalStandardModelMatterSectorTargets =
  leftQuarkDoubletTarget
  ∷ rightUpQuarkTarget
  ∷ rightDownQuarkTarget
  ∷ leftLeptonDoubletTarget
  ∷ rightChargedLeptonTarget
  ∷ higgsDoubletTarget
  ∷ []

data HyperchargeAnomalyConditionLabel : Set where
  su3SquaredU1YAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  su2SquaredU1YAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  u1YCubedAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  gravitationalSquaredU1YAnomalyCancellation :
    HyperchargeAnomalyConditionLabel

  globalSU2WittenAnomalyEvenDoublets :
    HyperchargeAnomalyConditionLabel

canonicalHyperchargeAnomalyConditionLabels :
  List HyperchargeAnomalyConditionLabel
canonicalHyperchargeAnomalyConditionLabels =
  su3SquaredU1YAnomalyCancellation
  ∷ su2SquaredU1YAnomalyCancellation
  ∷ u1YCubedAnomalyCancellation
  ∷ gravitationalSquaredU1YAnomalyCancellation
  ∷ globalSU2WittenAnomalyEvenDoublets
  ∷ []

data MatterAdapterBoundary : Set where
  missingCompactGroupGlobalForm :
    MatterAdapterBoundary

  missingRepresentationCategory :
    MatterAdapterBoundary

  missingHyperchargeNormalization :
    MatterAdapterBoundary

  missingAnomalyCancellationProof :
    MatterAdapterBoundary

  missingThreeGenerationDerivation :
    MatterAdapterBoundary

  missingYukawaMatrixDerivation :
    MatterAdapterBoundary

  missingCKMMixingDerivation :
    MatterAdapterBoundary

  missingPMNSMixingDerivation :
    MatterAdapterBoundary

  missingNeutrinoMassAdapter :
    MatterAdapterBoundary

  missingAbsoluteHiggsVEVAndFermionScaleAdapter4 :
    MatterAdapterBoundary

canonicalMatterAdapterBoundaries :
  List MatterAdapterBoundary
canonicalMatterAdapterBoundaries =
  missingCompactGroupGlobalForm
  ∷ missingRepresentationCategory
  ∷ missingHyperchargeNormalization
  ∷ missingAnomalyCancellationProof
  ∷ missingThreeGenerationDerivation
  ∷ missingYukawaMatrixDerivation
  ∷ missingCKMMixingDerivation
  ∷ missingPMNSMixingDerivation
  ∷ missingNeutrinoMassAdapter
  ∷ missingAbsoluteHiggsVEVAndFermionScaleAdapter4
  ∷ []

data YukawaRatioPromotionTarget : Set where
  ratioFormYukawaEigenvalueHierarchyTarget :
    YukawaRatioPromotionTarget

  georgiJarlskogSU5FortyFiveHiggsTarget :
    YukawaRatioPromotionTarget

  froggattNielsenChargeTextureTarget :
    YukawaRatioPromotionTarget

  ckmWolfensteinCabibboFromFNChargeDifferencesTarget :
    YukawaRatioPromotionTarget

  frobeniusPhaseCPSourceTarget :
    YukawaRatioPromotionTarget

  pmnsDemocraticMajoranaFromP7SU2RTarget :
    YukawaRatioPromotionTarget

  seesawScaleReceiptTarget :
    YukawaRatioPromotionTarget

  adapter4AbsoluteHiggsVEVFermionScaleBoundaryTarget :
    YukawaRatioPromotionTarget

canonicalYukawaRatioPromotionTargets :
  List YukawaRatioPromotionTarget
canonicalYukawaRatioPromotionTargets =
  ratioFormYukawaEigenvalueHierarchyTarget
  ∷ georgiJarlskogSU5FortyFiveHiggsTarget
  ∷ froggattNielsenChargeTextureTarget
  ∷ ckmWolfensteinCabibboFromFNChargeDifferencesTarget
  ∷ frobeniusPhaseCPSourceTarget
  ∷ pmnsDemocraticMajoranaFromP7SU2RTarget
  ∷ seesawScaleReceiptTarget
  ∷ adapter4AbsoluteHiggsVEVFermionScaleBoundaryTarget
  ∷ []

data GeorgiJarlskogRelationLabel : Set where
  su5FortyFiveBottomTauRatioOneTarget :
    GeorgiJarlskogRelationLabel

  su5FortyFiveMuonStrangeClebschThreeTarget :
    GeorgiJarlskogRelationLabel

  su5FortyFiveElectronDownClebschOneThirdTarget :
    GeorgiJarlskogRelationLabel

canonicalGeorgiJarlskogRelationLabels :
  List GeorgiJarlskogRelationLabel
canonicalGeorgiJarlskogRelationLabels =
  su5FortyFiveBottomTauRatioOneTarget
  ∷ su5FortyFiveMuonStrangeClebschThreeTarget
  ∷ su5FortyFiveElectronDownClebschOneThirdTarget
  ∷ []

data FroggattNielsenChargeSlot : Set where
  leftQuarkDoubletFNCharge :
    FroggattNielsenChargeSlot

  rightUpQuarkFNCharge :
    FroggattNielsenChargeSlot

  rightDownQuarkFNCharge :
    FroggattNielsenChargeSlot

  leftLeptonDoubletFNCharge :
    FroggattNielsenChargeSlot

  rightChargedLeptonFNCharge :
    FroggattNielsenChargeSlot

  rightNeutrinoFNCharge :
    FroggattNielsenChargeSlot

  higgsFNCharge :
    FroggattNielsenChargeSlot

canonicalFroggattNielsenChargeSlots :
  List FroggattNielsenChargeSlot
canonicalFroggattNielsenChargeSlots =
  leftQuarkDoubletFNCharge
  ∷ rightUpQuarkFNCharge
  ∷ rightDownQuarkFNCharge
  ∷ leftLeptonDoubletFNCharge
  ∷ rightChargedLeptonFNCharge
  ∷ rightNeutrinoFNCharge
  ∷ higgsFNCharge
  ∷ []

data CKMWolfensteinFNRelationLabel : Set where
  cabibboAngleFromLeftQuarkFNChargeDifference12 :
    CKMWolfensteinFNRelationLabel

  vcbFromLeftQuarkFNChargeDifference23 :
    CKMWolfensteinFNRelationLabel

  vubFromLeftQuarkFNChargeDifference13 :
    CKMWolfensteinFNRelationLabel

  wolfensteinHierarchyFromFNChargeDifferences :
    CKMWolfensteinFNRelationLabel

canonicalCKMWolfensteinFNRelationLabels :
  List CKMWolfensteinFNRelationLabel
canonicalCKMWolfensteinFNRelationLabels =
  cabibboAngleFromLeftQuarkFNChargeDifference12
  ∷ vcbFromLeftQuarkFNChargeDifference23
  ∷ vubFromLeftQuarkFNChargeDifference13
  ∷ wolfensteinHierarchyFromFNChargeDifferences
  ∷ []

data FrobeniusPhaseCPSourceLabel : Set where
  crystallineFrobeniusEigenphaseCPSourceTarget :
    FrobeniusPhaseCPSourceLabel

  orderOneYukawaCoefficientPhaseSocket :
    FrobeniusPhaseCPSourceLabel

canonicalFrobeniusPhaseCPSourceLabels :
  List FrobeniusPhaseCPSourceLabel
canonicalFrobeniusPhaseCPSourceLabels =
  crystallineFrobeniusEigenphaseCPSourceTarget
  ∷ orderOneYukawaCoefficientPhaseSocket
  ∷ []

data PMNSMajoranaP7SU2RTarget : Set where
  p7SU2RRightHandedNeutrinoMajoranaTarget :
    PMNSMajoranaP7SU2RTarget

  democraticMajoranaMatrixTextureTarget :
    PMNSMajoranaP7SU2RTarget

  pmnsLargeMixingFromDemocraticMajoranaTarget :
    PMNSMajoranaP7SU2RTarget

canonicalPMNSMajoranaP7SU2RTargets :
  List PMNSMajoranaP7SU2RTarget
canonicalPMNSMajoranaP7SU2RTargets =
  p7SU2RRightHandedNeutrinoMajoranaTarget
  ∷ democraticMajoranaMatrixTextureTarget
  ∷ pmnsLargeMixingFromDemocraticMajoranaTarget
  ∷ []

data SeesawScaleReceiptLabel : Set where
  p7SU2RBreakingScaleReceiptTarget :
    SeesawScaleReceiptLabel

  rightHandedMajoranaMassScaleReceiptTarget :
    SeesawScaleReceiptLabel

  lightNeutrinoRatioFormSeesawReceiptTarget :
    SeesawScaleReceiptLabel

canonicalSeesawScaleReceiptLabels :
  List SeesawScaleReceiptLabel
canonicalSeesawScaleReceiptLabels =
  p7SU2RBreakingScaleReceiptTarget
  ∷ rightHandedMajoranaMassScaleReceiptTarget
  ∷ lightNeutrinoRatioFormSeesawReceiptTarget
  ∷ []

postulate
  CompactGaugeGroup :
    Set

  MatterRepresentation :
    Set

  HyperchargeAssignment :
    Set

  AnomalyClass :
    Set

  GenerationStructure :
    Set

  YukawaSector :
    Set

  MixingMatrix :
    Set

  NeutrinoSector :
    Set

  matterRepresentationAdapterTarget :
    CompactGaugeGroup →
    StandardModelMatterSectorTarget →
    MatterRepresentation

  hyperchargeAssignmentTarget :
    StandardModelMatterSectorTarget →
    HyperchargeAssignment

  anomalyClassTarget :
    HyperchargeAssignment →
    AnomalyClass

  abstractMatterPrimeLaneDHREndoTarget :
    Moonshine.MonsterPrimeLane →
    DHR.LocalisedEndomorphism →
    Set

  abstractMatterPrimeLaneTransportTarget :
    (p : Moonshine.MonsterPrimeLane) →
    (ρ : DHR.LocalisedEndomorphism) →
    DHR.Transportable ρ →
    Set

  abstractMatterPrimeLaneSectorTarget :
    Moonshine.MonsterPrimeLane →
    StandardModelMatterSectorTarget →
    MatterRepresentation →
    Set

  SerreTateDefSpaceAtPrimeLane :
    Moonshine.MonsterPrimeLane →
    Set

  HiggsFNChargeAdapter :
    Set

  YukawaTextureTarget :
    Set

  FrobeniusPhaseReceipt :
    Set

  CKMCPConditionalTarget :
    Set

  matterPrimeLaneYukawaTextureTarget :
    (p : Moonshine.MonsterPrimeLane) →
    FractranLane.MonsterPrimeLaneAtLeast11 p →
    SerreTateDefSpaceAtPrimeLane p →
    HiggsFNChargeAdapter →
    YukawaTextureTarget

  ckmCPFromFrobeniusConditionalTarget :
    FrobeniusPhaseReceipt →
    CKMCPConditionalTarget

data Tranche2MatterOpenObligation : Set where
  matterLaneCardinalityMismatchOpen :
    Tranche2MatterOpenObligation

  missingSerreTateDefSpaceForEachMatterLane :
    Tranche2MatterOpenObligation

  missingHiggsFNChargeNormalisationAdapter :
    Tranche2MatterOpenObligation

  missingExactFNYukawaTextureProof :
    Tranche2MatterOpenObligation

  missingFrobeniusPhaseToCKMCPNumerics :
    Tranche2MatterOpenObligation

  absoluteHiggsVEVRemainsAdapter4 :
    Tranche2MatterOpenObligation

canonicalTranche2MatterOpenObligations :
  List Tranche2MatterOpenObligation
canonicalTranche2MatterOpenObligations =
  matterLaneCardinalityMismatchOpen
  ∷ missingSerreTateDefSpaceForEachMatterLane
  ∷ missingHiggsFNChargeNormalisationAdapter
  ∷ missingExactFNYukawaTextureProof
  ∷ missingFrobeniusPhaseToCKMCPNumerics
  ∷ absoluteHiggsVEVRemainsAdapter4
  ∷ []

data PatiSalamMatterRepresentationTarget : Set where
  leftGenerationFourTwoOneTarget :
    PatiSalamMatterRepresentationTarget

  rightGenerationBarFourOneTwoTarget :
    PatiSalamMatterRepresentationTarget

  psFourBranchesToColourTripletBMinusLThirdTarget :
    PatiSalamMatterRepresentationTarget

  psFourBranchesToLeptonSingletBMinusLOneTarget :
    PatiSalamMatterRepresentationTarget

  threeGenerationGroupingTarget :
    PatiSalamMatterRepresentationTarget

canonicalPatiSalamMatterRepresentationTargets :
  List PatiSalamMatterRepresentationTarget
canonicalPatiSalamMatterRepresentationTargets =
  leftGenerationFourTwoOneTarget
  ∷ rightGenerationBarFourOneTwoTarget
  ∷ psFourBranchesToColourTripletBMinusLThirdTarget
  ∷ psFourBranchesToLeptonSingletBMinusLOneTarget
  ∷ threeGenerationGroupingTarget
  ∷ []

record Tranche2MatterLaneInventoryReceipt : Setω where
  field
    gaugeLanes :
      List Moonshine.MonsterPrimeLane

    gaugeLanesAreCanonical :
      gaugeLanes
      ≡
      FractranLane.canonicalPatiSalamGaugePrimeLanes

    nonGaugeMatterLanes :
      List Moonshine.MonsterPrimeLane

    nonGaugeMatterLanesAreCanonical :
      nonGaugeMatterLanes
      ≡
      FractranLane.canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge

    matterLaneCardinalityMismatch :
      FractranLane.MatterLaneCardinalityMismatch

    expectedMatterLaneCount :
      Nat

    expectedMatterLaneCountIs12 :
      expectedMatterLaneCount
      ≡
      FractranLane.expectedMatterLaneCountAfterFourGaugeLanes

    actualMatterLaneCount :
      Nat

    actualMatterLaneCountIs11 :
      actualMatterLaneCount
      ≡
      FractranLane.actualMatterLaneCountAfterFourGaugeLanes

    mismatchBlocksMatterPromotion :
      Bool

    mismatchBlocksMatterPromotionIsTrue :
      mismatchBlocksMatterPromotion ≡ true

    boundary :
      List String

open Tranche2MatterLaneInventoryReceipt public

canonicalTranche2MatterLaneInventoryReceipt :
  Tranche2MatterLaneInventoryReceipt
canonicalTranche2MatterLaneInventoryReceipt =
  record
    { gaugeLanes =
        FractranLane.canonicalPatiSalamGaugePrimeLanes
    ; gaugeLanesAreCanonical =
        refl
    ; nonGaugeMatterLanes =
        FractranLane.canonicalNonGaugeMatterPrimeLanesAfterPatiSalamGauge
    ; nonGaugeMatterLanesAreCanonical =
        refl
    ; matterLaneCardinalityMismatch =
        FractranLane.canonicalMatterLaneCardinalityMismatch
    ; expectedMatterLaneCount =
        FractranLane.expectedMatterLaneCountAfterFourGaugeLanes
    ; expectedMatterLaneCountIs12 =
        refl
    ; actualMatterLaneCount =
        FractranLane.actualMatterLaneCountAfterFourGaugeLanes
    ; actualMatterLaneCountIs11 =
        refl
    ; mismatchBlocksMatterPromotion =
        true
    ; mismatchBlocksMatterPromotionIsTrue =
        refl
    ; boundary =
        "Gauge lanes are {2,3,5,7}; listed matter lanes are {11,13,17,19,23,29,31,41,47,59,71}"
        ∷ "The listed matter lane set has 11 entries while the tranche asks for 12 remaining primes"
        ∷ "Matter generation assignment is therefore recorded as open, not silently completed"
        ∷ []
    }

record PatiSalamMatterPerGenerationReceipt : Setω where
  field
    representationTargets :
      List PatiSalamMatterRepresentationTarget

    representationTargetsAreCanonical :
      representationTargets
      ≡
      canonicalPatiSalamMatterRepresentationTargets

    leftMatterRepLabel :
      String

    leftMatterRepLabel-v :
      leftMatterRepLabel
      ≡
      "(4,2,1)"

    rightMatterRepLabel :
      String

    rightMatterRepLabel-v :
      rightMatterRepLabel
      ≡
      "(bar4,1,2)"

    psFourBranchingTarget :
      String

    psFourBranchingTarget-v :
      psFourBranchingTarget
      ≡
      "4 -> 3_{1/3} + 1_{-1}"

    branchingPromoted :
      Bool

    branchingPromotedIsFalse :
      branchingPromoted ≡ false

    boundary :
      List String

open PatiSalamMatterPerGenerationReceipt public

canonicalPatiSalamMatterPerGenerationReceipt :
  PatiSalamMatterPerGenerationReceipt
canonicalPatiSalamMatterPerGenerationReceipt =
  record
    { representationTargets =
        canonicalPatiSalamMatterRepresentationTargets
    ; representationTargetsAreCanonical =
        refl
    ; leftMatterRepLabel =
        "(4,2,1)"
    ; leftMatterRepLabel-v =
        refl
    ; rightMatterRepLabel =
        "(bar4,1,2)"
    ; rightMatterRepLabel-v =
        refl
    ; psFourBranchingTarget =
        "4 -> 3_{1/3} + 1_{-1}"
    ; psFourBranchingTarget-v =
        refl
    ; branchingPromoted =
        false
    ; branchingPromotedIsFalse =
        refl
    ; boundary =
        "Pati-Salam matter target per generation is (4,2,1) plus (bar4,1,2)"
        ∷ "The SU(4) Pati-Salam branching target is 4 -> 3_{1/3} + 1_{-1}"
        ∷ "This receipt records representation targets; it does not prove generation assignment from the available matter lanes"
        ∷ []
    }

record MatterPrimeLaneYukawaFNReceipt : Setω where
  field
    laneInventory :
      Tranche2MatterLaneInventoryReceipt

    patiSalamMatterPerGeneration :
      PatiSalamMatterPerGenerationReceipt

    fnChargeFromMonsterValuation :
      FractranLane.FNChargeFromMonsterValuationReceipt

    serreTateDefSpace :
      Moonshine.MonsterPrimeLane →
      Set

    serreTateDefSpaceIsCanonical :
      serreTateDefSpace
      ≡
      SerreTateDefSpaceAtPrimeLane

    higgsFNChargeAdapterCarrier :
      Set

    higgsFNChargeAdapterCarrierIsCanonical :
      higgsFNChargeAdapterCarrier
      ≡
      HiggsFNChargeAdapter

    yukawaTextureCarrier :
      Set

    yukawaTextureCarrierIsCanonical :
      yukawaTextureCarrier
      ≡
      YukawaTextureTarget

    conditionalMatterLaneYukawaTexture :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      serreTateDefSpace p →
      higgsFNChargeAdapterCarrier →
      yukawaTextureCarrier

    ckmCPConditionalCarrier :
      Set

    ckmCPConditionalCarrierIsCanonical :
      ckmCPConditionalCarrier
      ≡
      CKMCPConditionalTarget

    ckmCPConditionalFromFrobenius :
      FrobeniusPhaseReceipt →
      ckmCPConditionalCarrier

    openObligations :
      List Tranche2MatterOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalTranche2MatterOpenObligations

    fnValuationTargetRecorded :
      Bool

    fnValuationTargetRecordedIsTrue :
      fnValuationTargetRecorded ≡ true

    higgsChargeNormalisationAdapter4 :
      Bool

    higgsChargeNormalisationAdapter4IsTrue :
      higgsChargeNormalisationAdapter4 ≡ true

    ckmAndCPRemainConditional :
      Bool

    ckmAndCPRemainConditionalIsTrue :
      ckmAndCPRemainConditional ≡ true

    absoluteHiggsVEVRemainsAdapter4Flag :
      Bool

    absoluteHiggsVEVRemainsAdapter4FlagIsTrue :
      absoluteHiggsVEVRemainsAdapter4Flag ≡ true

    exactTexturePromoted :
      Bool

    exactTexturePromotedIsFalse :
      exactTexturePromoted ≡ false

    matterPrimeLaneReceiptPromoted :
      Bool

    matterPrimeLaneReceiptPromotedIsFalse :
      matterPrimeLaneReceiptPromoted ≡ false

    boundary :
      List String

open MatterPrimeLaneYukawaFNReceipt public

canonicalMatterPrimeLaneYukawaFNReceipt :
  MatterPrimeLaneYukawaFNReceipt
canonicalMatterPrimeLaneYukawaFNReceipt =
  record
    { laneInventory =
        canonicalTranche2MatterLaneInventoryReceipt
    ; patiSalamMatterPerGeneration =
        canonicalPatiSalamMatterPerGenerationReceipt
    ; fnChargeFromMonsterValuation =
        FractranLane.canonicalFNChargeFromMonsterValuationReceipt
    ; serreTateDefSpace =
        SerreTateDefSpaceAtPrimeLane
    ; serreTateDefSpaceIsCanonical =
        refl
    ; higgsFNChargeAdapterCarrier =
        HiggsFNChargeAdapter
    ; higgsFNChargeAdapterCarrierIsCanonical =
        refl
    ; yukawaTextureCarrier =
        YukawaTextureTarget
    ; yukawaTextureCarrierIsCanonical =
        refl
    ; conditionalMatterLaneYukawaTexture =
        matterPrimeLaneYukawaTextureTarget
    ; ckmCPConditionalCarrier =
        CKMCPConditionalTarget
    ; ckmCPConditionalCarrierIsCanonical =
        refl
    ; ckmCPConditionalFromFrobenius =
        ckmCPFromFrobeniusConditionalTarget
    ; openObligations =
        canonicalTranche2MatterOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; fnValuationTargetRecorded =
        true
    ; fnValuationTargetRecordedIsTrue =
        refl
    ; higgsChargeNormalisationAdapter4 =
        true
    ; higgsChargeNormalisationAdapter4IsTrue =
        refl
    ; ckmAndCPRemainConditional =
        true
    ; ckmAndCPRemainConditionalIsTrue =
        refl
    ; absoluteHiggsVEVRemainsAdapter4Flag =
        true
    ; absoluteHiggsVEVRemainsAdapter4FlagIsTrue =
        refl
    ; exactTexturePromoted =
        false
    ; exactTexturePromotedIsFalse =
        refl
    ; matterPrimeLaneReceiptPromoted =
        false
    ; matterPrimeLaneReceiptPromotedIsFalse =
        refl
    ; boundary =
        "MatterPrimeLaneReceipt is conditional on Serre-Tate deformation data for p>=11 and a Higgs FN charge adapter q_H"
        ∷ "Pati-Salam per-generation targets are (4,2,1) plus (bar4,1,2), with 4 -> 3_{1/3} + 1_{-1} as a branching target"
        ∷ "FN charge target q_p = v_p(|M|)-2 is recorded: valuation 2 -> 0, valuation 1 -> -1"
        ∷ "The available post-gauge list contains 11 matter primes, so the requested twelve-prime matter assignment is an open obligation"
        ∷ "CKM/CP/Frobenius phase and exact Yukawa textures remain conditional; absolute Higgs vev remains Adapter 4"
        ∷ []
    }

record YukawaSectorRatioFormPromotionReceipt : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    ratioPromotionTargets :
      List YukawaRatioPromotionTarget

    ratioPromotionTargetsAreCanonical :
      ratioPromotionTargets
      ≡
      canonicalYukawaRatioPromotionTargets

    georgiJarlskogRelations :
      List GeorgiJarlskogRelationLabel

    georgiJarlskogRelationsAreCanonical :
      georgiJarlskogRelations
      ≡
      canonicalGeorgiJarlskogRelationLabels

    froggattNielsenChargeSlots :
      List FroggattNielsenChargeSlot

    froggattNielsenChargeSlotsAreCanonical :
      froggattNielsenChargeSlots
      ≡
      canonicalFroggattNielsenChargeSlots

    ckmWolfensteinFNRelations :
      List CKMWolfensteinFNRelationLabel

    ckmWolfensteinFNRelationsAreCanonical :
      ckmWolfensteinFNRelations
      ≡
      canonicalCKMWolfensteinFNRelationLabels

    frobeniusPhaseCPSources :
      List FrobeniusPhaseCPSourceLabel

    frobeniusPhaseCPSourcesAreCanonical :
      frobeniusPhaseCPSources
      ≡
      canonicalFrobeniusPhaseCPSourceLabels

    pmnsMajoranaP7SU2RTargets :
      List PMNSMajoranaP7SU2RTarget

    pmnsMajoranaP7SU2RTargetsAreCanonical :
      pmnsMajoranaP7SU2RTargets
      ≡
      canonicalPMNSMajoranaP7SU2RTargets

    seesawScaleReceipts :
      List SeesawScaleReceiptLabel

    seesawScaleReceiptsAreCanonical :
      seesawScaleReceipts
      ≡
      canonicalSeesawScaleReceiptLabels

    p7SeesawLane :
      Moonshine.MonsterPrimeLane

    p7SeesawLaneIsCanonical :
      p7SeesawLane ≡ Moonshine.p7

    p7HighEnergyAssignment :
      FractranLane.HighEnergyPatiSalamLaneAssignment

    p7HighEnergyAssignmentIsSU2RBrokenAtSeesaw :
      p7HighEnergyAssignment
      ≡
      FractranLane.assignedSU2RBrokenAtSeesaw

    ratioFormPromotionTargetRecorded :
      Bool

    ratioFormPromotionTargetRecordedIsTrue :
      ratioFormPromotionTargetRecorded ≡ true

    georgiJarlskogSU5FortyFiveRecorded :
      Bool

    georgiJarlskogSU5FortyFiveRecordedIsTrue :
      georgiJarlskogSU5FortyFiveRecorded ≡ true

    froggattNielsenTextureRecorded :
      Bool

    froggattNielsenTextureRecordedIsTrue :
      froggattNielsenTextureRecorded ≡ true

    ckmWolfensteinCabibboFromFNRecorded :
      Bool

    ckmWolfensteinCabibboFromFNRecordedIsTrue :
      ckmWolfensteinCabibboFromFNRecorded ≡ true

    frobeniusPhaseCPSourceRecorded :
      Bool

    frobeniusPhaseCPSourceRecordedIsTrue :
      frobeniusPhaseCPSourceRecorded ≡ true

    pmnsDemocraticMajoranaP7SU2RRecorded :
      Bool

    pmnsDemocraticMajoranaP7SU2RRecordedIsTrue :
      pmnsDemocraticMajoranaP7SU2RRecorded ≡ true

    seesawScaleReceiptRecorded :
      Bool

    seesawScaleReceiptRecordedIsTrue :
      seesawScaleReceiptRecorded ≡ true

    exactMatrixNumericsPromoted :
      Bool

    exactMatrixNumericsPromotedIsFalse :
      exactMatrixNumericsPromoted ≡ false

    absoluteHiggsVEVOrFermionScaleDerived :
      Bool

    absoluteHiggsVEVOrFermionScaleDerivedIsFalse :
      absoluteHiggsVEVOrFermionScaleDerived ≡ false

    adapter4AbsoluteScaleBoundary :
      String

    ratioPromotionPromoted :
      Bool

    ratioPromotionPromotedIsFalse :
      ratioPromotionPromoted ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open YukawaSectorRatioFormPromotionReceipt public

canonicalYukawaSectorRatioFormPromotionReceipt :
  YukawaSectorRatioFormPromotionReceipt
canonicalYukawaSectorRatioFormPromotionReceipt =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; ratioPromotionTargets =
        canonicalYukawaRatioPromotionTargets
    ; ratioPromotionTargetsAreCanonical =
        refl
    ; georgiJarlskogRelations =
        canonicalGeorgiJarlskogRelationLabels
    ; georgiJarlskogRelationsAreCanonical =
        refl
    ; froggattNielsenChargeSlots =
        canonicalFroggattNielsenChargeSlots
    ; froggattNielsenChargeSlotsAreCanonical =
        refl
    ; ckmWolfensteinFNRelations =
        canonicalCKMWolfensteinFNRelationLabels
    ; ckmWolfensteinFNRelationsAreCanonical =
        refl
    ; frobeniusPhaseCPSources =
        canonicalFrobeniusPhaseCPSourceLabels
    ; frobeniusPhaseCPSourcesAreCanonical =
        refl
    ; pmnsMajoranaP7SU2RTargets =
        canonicalPMNSMajoranaP7SU2RTargets
    ; pmnsMajoranaP7SU2RTargetsAreCanonical =
        refl
    ; seesawScaleReceipts =
        canonicalSeesawScaleReceiptLabels
    ; seesawScaleReceiptsAreCanonical =
        refl
    ; p7SeesawLane =
        Moonshine.p7
    ; p7SeesawLaneIsCanonical =
        refl
    ; p7HighEnergyAssignment =
        FractranLane.assignedSU2RBrokenAtSeesaw
    ; p7HighEnergyAssignmentIsSU2RBrokenAtSeesaw =
        refl
    ; ratioFormPromotionTargetRecorded =
        true
    ; ratioFormPromotionTargetRecordedIsTrue =
        refl
    ; georgiJarlskogSU5FortyFiveRecorded =
        true
    ; georgiJarlskogSU5FortyFiveRecordedIsTrue =
        refl
    ; froggattNielsenTextureRecorded =
        true
    ; froggattNielsenTextureRecordedIsTrue =
        refl
    ; ckmWolfensteinCabibboFromFNRecorded =
        true
    ; ckmWolfensteinCabibboFromFNRecordedIsTrue =
        refl
    ; frobeniusPhaseCPSourceRecorded =
        true
    ; frobeniusPhaseCPSourceRecordedIsTrue =
        refl
    ; pmnsDemocraticMajoranaP7SU2RRecorded =
        true
    ; pmnsDemocraticMajoranaP7SU2RRecordedIsTrue =
        refl
    ; seesawScaleReceiptRecorded =
        true
    ; seesawScaleReceiptRecordedIsTrue =
        refl
    ; exactMatrixNumericsPromoted =
        false
    ; exactMatrixNumericsPromotedIsFalse =
        refl
    ; absoluteHiggsVEVOrFermionScaleDerived =
        false
    ; absoluteHiggsVEVOrFermionScaleDerivedIsFalse =
        refl
    ; adapter4AbsoluteScaleBoundary =
        "absolute Higgs vev, running fermion masses, thresholds, and physical mass scale remain Adapter 4 authority inputs"
    ; ratioPromotionPromoted =
        false
    ; ratioPromotionPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "Yukawa sector is recorded as ratio-form promotion target data, not absolute mass numerics"
        ∷ "Georgi-Jarlskog relations are symbolic SU(5)+45-Higgs Clebsch relation labels"
        ∷ "Froggatt-Nielsen textures are symbolic charge-slot and lambda-power targets"
        ∷ "CKM Wolfenstein/Cabibbo hierarchy is recorded as arising from FN left-quark charge differences"
        ∷ "CP violation has a Frobenius-phase source socket without a promoted numeric phase"
        ∷ "PMNS target uses a democratic Majorana texture sourced by p7 SU2R broken at seesaw"
        ∷ "Seesaw scale is a receipt target; exact matrices and absolute Higgs vev/fermion scales remain Adapter 4"
        ∷ []
    }

record MatterPrimeLaneReceiptTargetSurface : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    matterPrimeLaneTargets :
      List MatterPrimeLaneTarget

    matterPrimeLaneTargetsAreCanonical :
      matterPrimeLaneTargets
      ≡
      canonicalMatterPrimeLaneTargets

    trackedPrimeLane :
      List Moonshine.MonsterPrimeLane

    trackedPrimeLaneAreCanonical :
      trackedPrimeLane
      ≡
      Moonshine.canonicalMonsterPrimeLane

    dhrGaugeReceiptSurface :
      DHR.DHRGaugeReceiptSurface

    dhrEndomorphismTarget :
      Moonshine.MonsterPrimeLane →
      DHR.LocalisedEndomorphism →
      Set

    dhrTransportTarget :
      (p : Moonshine.MonsterPrimeLane) →
      (ρ : DHR.LocalisedEndomorphism) →
      DHR.Transportable ρ →
      Set

    matterSectorTarget :
      Moonshine.MonsterPrimeLane →
      StandardModelMatterSectorTarget →
      MatterRepresentation →
      Set

    conjecturalLaneDimension :
      Moonshine.MonsterPrimeLane →
      Nat

    laneDimension2Is1 :
      conjecturalLaneDimension Moonshine.p2 ≡ 1

    laneDimension3Is2 :
      conjecturalLaneDimension Moonshine.p3 ≡ 2

    laneDimension5Is3 :
      conjecturalLaneDimension Moonshine.p5 ≡ 3

    laneDimensionAtLeast7Is0 :
      (p : Moonshine.MonsterPrimeLane) →
      Moonshine.MonsterPrimeLaneAtLeast7 p →
      conjecturalLaneDimension p ≡ 0

    highEnergyPatiSalamAssignmentBridge :
      Moonshine.MonsterPrimeLane →
      FractranLane.HighEnergyPatiSalamLaneAssignment

    highEnergyPatiSalamAssignmentBridgeIsCanonical :
      highEnergyPatiSalamAssignmentBridge
      ≡
      FractranLane.patiSalamHighEnergyAssignment

    highEnergyPatiSalamP2IsU1 :
      highEnergyPatiSalamAssignmentBridge Moonshine.p2
      ≡
      FractranLane.assignedU1

    highEnergyPatiSalamP3IsSU2L :
      highEnergyPatiSalamAssignmentBridge Moonshine.p3
      ≡
      FractranLane.assignedSU2L

    highEnergyPatiSalamP5IsSU3c :
      highEnergyPatiSalamAssignmentBridge Moonshine.p5
      ≡
      FractranLane.assignedSU3c

    highEnergyPatiSalamP7IsSU2RBrokenAtSeesaw :
      highEnergyPatiSalamAssignmentBridge Moonshine.p7
      ≡
      FractranLane.assignedSU2RBrokenAtSeesaw

    highEnergyPatiSalamAtLeast11InactiveOrMatter :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      highEnergyPatiSalamAssignmentBridge p
      ≡
      FractranLane.inactiveOrMatterLane

    laneDimensionConjecturalOpen :
      Bool

    laneDimensionConjecturalOpenIsTrue :
      laneDimensionConjecturalOpen ≡ true

    matterPrimeLaneDerived :
      Bool

    matterPrimeLaneDerivedIsFalse :
      matterPrimeLaneDerived ≡ false

    highEnergyBridgeDerivesMatterRepresentations :
      Bool

    highEnergyBridgeDerivesMatterRepresentationsIsFalse :
      highEnergyBridgeDerivesMatterRepresentations ≡ false

    highEnergyBridgeIsDHRLaneDimension :
      Bool

    highEnergyBridgeIsDHRLaneDimensionIsFalse :
      highEnergyBridgeIsDHRLaneDimension ≡ false

    receiptBoundary :
      List String

open MatterPrimeLaneReceiptTargetSurface public

canonicalMatterPrimeLaneReceiptTargetSurface :
  MatterPrimeLaneReceiptTargetSurface
canonicalMatterPrimeLaneReceiptTargetSurface =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; matterPrimeLaneTargets =
        canonicalMatterPrimeLaneTargets
    ; matterPrimeLaneTargetsAreCanonical =
        refl
    ; trackedPrimeLane =
        Moonshine.canonicalMonsterPrimeLane
    ; trackedPrimeLaneAreCanonical =
        refl
    ; dhrGaugeReceiptSurface =
        DHR.canonicalDHRGaugeReceiptSurface
    ; dhrEndomorphismTarget =
        abstractMatterPrimeLaneDHREndoTarget
    ; dhrTransportTarget =
        abstractMatterPrimeLaneTransportTarget
    ; matterSectorTarget =
        abstractMatterPrimeLaneSectorTarget
    ; conjecturalLaneDimension =
        Moonshine.monsterPrimeLaneConjecturalDHRDimension
    ; laneDimension2Is1 =
        refl
    ; laneDimension3Is2 =
        refl
    ; laneDimension5Is3 =
        refl
    ; laneDimensionAtLeast7Is0 =
        Moonshine.monsterPrimeLaneDHRDimensionAtLeast7Is0
    ; highEnergyPatiSalamAssignmentBridge =
        FractranLane.patiSalamHighEnergyAssignment
    ; highEnergyPatiSalamAssignmentBridgeIsCanonical =
        refl
    ; highEnergyPatiSalamP2IsU1 =
        refl
    ; highEnergyPatiSalamP3IsSU2L =
        refl
    ; highEnergyPatiSalamP5IsSU3c =
        refl
    ; highEnergyPatiSalamP7IsSU2RBrokenAtSeesaw =
        refl
    ; highEnergyPatiSalamAtLeast11InactiveOrMatter =
        FractranLane.patiSalamAtLeast11IsInactiveOrMatter
    ; laneDimensionConjecturalOpen =
        true
    ; laneDimensionConjecturalOpenIsTrue =
        refl
    ; matterPrimeLaneDerived =
        false
    ; matterPrimeLaneDerivedIsFalse =
        refl
    ; highEnergyBridgeDerivesMatterRepresentations =
        false
    ; highEnergyBridgeDerivesMatterRepresentationsIsFalse =
        refl
    ; highEnergyBridgeIsDHRLaneDimension =
        false
    ; highEnergyBridgeIsDHRLaneDimensionIsFalse =
        refl
    ; receiptBoundary =
        "Matter prime-lane receipt target binds DHR localized endomorphism targets to SM matter-sector representation targets"
        ∷ "The DHR lane dimension assignment is explicitly conjectural/open: 2->1, 3->2, 5->3, primes >=7 -> 0"
        ∷ "A separate conjectural high-energy Pati-Salam bridge records p2->U1, p3->SU2L, p5->SU3c, p7->SU2R-broken-at-seesaw, and p>=11 inactive/matter"
        ∷ "The high-energy bridge does not compute DHR laneDimension and does not derive matter representations"
        ∷ "No matter representation, hypercharge assignment, anomaly proof, or gauge-group equality is derived here"
        ∷ []
    }

record MatterPrimeLaneReceipt : Setω where
  field
    targetSurface :
      MatterPrimeLaneReceiptTargetSurface

    targetSurfaceIsCanonical :
      Bool

    targetSurfaceIsCanonicalIsTrue :
      targetSurfaceIsCanonical ≡ true

open MatterPrimeLaneReceipt public

canonicalMatterPrimeLaneReceipt :
  MatterPrimeLaneReceipt
canonicalMatterPrimeLaneReceipt =
  record
    { targetSurface =
        canonicalMatterPrimeLaneReceiptTargetSurface
    ; targetSurfaceIsCanonical =
        true
    ; targetSurfaceIsCanonicalIsTrue =
        refl
    }

record MatterRepresentationBoundaryReceipt : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    matterSectorTargets :
      List StandardModelMatterSectorTarget

    matterSectorTargetsAreCanonical :
      matterSectorTargets
      ≡
      canonicalStandardModelMatterSectorTargets

    adapterBoundaries :
      List MatterAdapterBoundary

    adapterBoundariesAreCanonical :
      adapterBoundaries
      ≡
      canonicalMatterAdapterBoundaries

    compactGroupBoundary :
      String

    representationCategoryBoundary :
      String

    hyperchargeAnomalyBoundary :
      String

    generationYukawaMixingBoundary :
      String

    yukawaRatioFormPromotionReceipt :
      YukawaSectorRatioFormPromotionReceipt

    standardModelDerived :
      Bool

    standardModelDerivedIsFalse :
      standardModelDerived ≡ false

    yukawaSectorDerived :
      Bool

    yukawaSectorDerivedIsFalse :
      yukawaSectorDerived ≡ false

    boundaryPromoted :
      Bool

    boundaryPromotedIsFalse :
      boundaryPromoted ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open MatterRepresentationBoundaryReceipt public

canonicalMatterRepresentationBoundaryReceipt :
  MatterRepresentationBoundaryReceipt
canonicalMatterRepresentationBoundaryReceipt =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; matterSectorTargets =
        canonicalStandardModelMatterSectorTargets
    ; matterSectorTargetsAreCanonical =
        refl
    ; adapterBoundaries =
        canonicalMatterAdapterBoundaries
    ; adapterBoundariesAreCanonical =
        refl
    ; compactGroupBoundary =
        "compact gauge group and global form must be supplied before matter representations are promoted"
    ; representationCategoryBoundary =
        "representation category and chirality/conjugation conventions are target data, not derived here"
    ; hyperchargeAnomalyBoundary =
        "hypercharge normalization and anomaly-cancellation equations are named obligations, not solved equations here"
    ; generationYukawaMixingBoundary =
        "three generations, Yukawa matrices, CKM, PMNS, and neutrino masses remain adapter boundaries"
    ; yukawaRatioFormPromotionReceipt =
        canonicalYukawaSectorRatioFormPromotionReceipt
    ; standardModelDerived =
        false
    ; standardModelDerivedIsFalse =
        refl
    ; yukawaSectorDerived =
        false
    ; yukawaSectorDerivedIsFalse =
        refl
    ; boundaryPromoted =
        false
    ; boundaryPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "MatterRepresentationBoundaryReceipt is a non-promoting receipt for SM matter-representation sockets"
        ∷ "it does not derive the Standard Model group, hypercharges, generations, Yukawa sector, CKM, PMNS, or neutrino sector"
        ∷ "Yukawa ratio-form target data may be recorded symbolically, but absolute Higgs vev and fermion scales remain Adapter 4"
        ∷ "it may be cited only as an explicit adapter-boundary receipt"
        ∷ []
    }

record MatterRepresentationReceiptSurface : Setω where
  field
    status :
      MatterRepresentationSurfaceStatus

    matterBoundaryReceipt :
      MatterRepresentationBoundaryReceipt

    matterPrimeLaneReceiptTarget :
      MatterPrimeLaneReceiptTargetSurface

    matterPrimeLaneYukawaFNReceipt :
      MatterPrimeLaneYukawaFNReceipt

    matterSectorTargets :
      List StandardModelMatterSectorTarget

    matterSectorTargetsAreCanonical :
      matterSectorTargets
      ≡
      canonicalStandardModelMatterSectorTargets

    hyperchargeAnomalyConditions :
      List HyperchargeAnomalyConditionLabel

    hyperchargeAnomalyConditionsAreCanonical :
      hyperchargeAnomalyConditions
      ≡
      canonicalHyperchargeAnomalyConditionLabels

    adapterBoundaries :
      List MatterAdapterBoundary

    adapterBoundariesAreCanonical :
      adapterBoundaries
      ≡
      canonicalMatterAdapterBoundaries

    compactGaugeGroupTarget :
      Set

    matterRepresentationTarget :
      Set

    hyperchargeAssignmentTargetCarrier :
      Set

    anomalyClassTargetCarrier :
      Set

    generationStructureTarget :
      Set

    yukawaSectorTarget :
      Set

    ckmMatrixTarget :
      Set

    pmnsMatrixTarget :
      Set

    neutrinoSectorTarget :
      Set

    yukawaRatioFormPromotionReceipt :
      YukawaSectorRatioFormPromotionReceipt

    representationAdapter :
      compactGaugeGroupTarget →
      StandardModelMatterSectorTarget →
      matterRepresentationTarget

    hyperchargeAdapter :
      StandardModelMatterSectorTarget →
      hyperchargeAssignmentTargetCarrier

    anomalyClassAdapter :
      hyperchargeAssignmentTargetCarrier →
      anomalyClassTargetCarrier

    anomalyEquationLabels :
      List String

    threeGenerationBoundary :
      String

    yukawaCKMPMNSNeutrinoBoundary :
      String

    adapter4AbsoluteHiggsVEVFermionScaleBoundary :
      String

    matterRepresentationsDerived :
      Bool

    matterRepresentationsDerivedIsFalse :
      matterRepresentationsDerived ≡ false

    noPromotionWithoutAuthority :
      MatterRepresentationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open MatterRepresentationReceiptSurface public

canonicalMatterRepresentationReceiptSurface :
  MatterRepresentationReceiptSurface
canonicalMatterRepresentationReceiptSurface =
  record
    { status =
        matterRepresentationTargetsOnlyNoPromotion
    ; matterBoundaryReceipt =
        canonicalMatterRepresentationBoundaryReceipt
    ; matterPrimeLaneReceiptTarget =
        canonicalMatterPrimeLaneReceiptTargetSurface
    ; matterPrimeLaneYukawaFNReceipt =
        canonicalMatterPrimeLaneYukawaFNReceipt
    ; matterSectorTargets =
        canonicalStandardModelMatterSectorTargets
    ; matterSectorTargetsAreCanonical =
        refl
    ; hyperchargeAnomalyConditions =
        canonicalHyperchargeAnomalyConditionLabels
    ; hyperchargeAnomalyConditionsAreCanonical =
        refl
    ; adapterBoundaries =
        canonicalMatterAdapterBoundaries
    ; adapterBoundariesAreCanonical =
        refl
    ; compactGaugeGroupTarget =
        CompactGaugeGroup
    ; matterRepresentationTarget =
        MatterRepresentation
    ; hyperchargeAssignmentTargetCarrier =
        HyperchargeAssignment
    ; anomalyClassTargetCarrier =
        AnomalyClass
    ; generationStructureTarget =
        GenerationStructure
    ; yukawaSectorTarget =
        YukawaSector
    ; ckmMatrixTarget =
        MixingMatrix
    ; pmnsMatrixTarget =
        MixingMatrix
    ; neutrinoSectorTarget =
        NeutrinoSector
    ; yukawaRatioFormPromotionReceipt =
        canonicalYukawaSectorRatioFormPromotionReceipt
    ; representationAdapter =
        matterRepresentationAdapterTarget
    ; hyperchargeAdapter =
        hyperchargeAssignmentTarget
    ; anomalyClassAdapter =
        anomalyClassTarget
    ; anomalyEquationLabels =
        "SU(3)^2-U(1)_Y anomaly cancellation"
        ∷ "SU(2)^2-U(1)_Y anomaly cancellation"
        ∷ "U(1)_Y^3 anomaly cancellation"
        ∷ "gravity^2-U(1)_Y anomaly cancellation"
        ∷ "global SU(2) Witten anomaly even-doublet condition"
        ∷ []
    ; threeGenerationBoundary =
        "three-generation structure is a conjectural/empirical adapter boundary, not derived here"
    ; yukawaCKMPMNSNeutrinoBoundary =
        "Yukawa ratio textures, CKM, PMNS, and neutrino masses/mixings are symbolic receipt targets, not promoted matrix numerics"
    ; adapter4AbsoluteHiggsVEVFermionScaleBoundary =
        "absolute Higgs vev and fermion mass scale remain Adapter 4 authority inputs"
    ; matterRepresentationsDerived =
        false
    ; matterRepresentationsDerivedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "SM matter representations are target/adaptation sockets only"
        ∷ "matter prime-lane DHR receipt target is present but conjectural/open and non-promoting"
        ∷ "Tranche 2 matter-lane/Yukawa FN receipt records gauge lanes {2,3,5,7}, eleven listed p>=11 matter lanes, and the expected-12/actual-11 mismatch as open"
        ∷ "hypercharge and anomaly equations are labels for future proofs, not solved equations here"
        ∷ "Yukawa ratio-form target records SU(5)+45 Georgi-Jarlskog, FN texture, CKM Wolfenstein/Cabibbo, Frobenius CP, p7 SU2R PMNS, and seesaw-scale sockets"
        ∷ "MatterPrimeLaneReceipt remains conditional on Serre-Tate p>=11 deformation data and Higgs FN charge normalisation q_H"
        ∷ "three generations, exact Yukawa matrices, CKM/PMNS numerics, neutrino masses, Higgs vev, and fermion scale remain irreducible adapter boundaries"
        ∷ "no Standard Model, GRQFT, or TOE claim is promoted"
        ∷ []
    }
