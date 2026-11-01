module DASHI.Physics.Closure.LeptonQuarkSeparationFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.LeptonQuarkSeparationReceipt as Base
import DASHI.Physics.Closure.D8LeptonLaneReceipt as D8
import DASHI.Physics.Closure.HeegnerSequenceQuarkLeptonReceipt as Seq
import DASHI.Physics.Closure.CKMHierarchyFromHeegnerPositionReceipt as Gap
import DASHI.Physics.Closure.QuarkLeptonGeometricSplitReceipt as Split
import DASHI.Physics.Closure.Disc11ExceptionReceipt as D11
import DASHI.Physics.Closure.LeptonYukawaFromLevelOverlapReceipt as Overlap
import DASHI.Physics.Closure.MuonNeutrinoIsolationReceipt as Muon
import DASHI.Physics.Closure.TauLeptonGen3OverlapReceipt as Tau
import DASHI.Physics.QFT.D11D12LeptonLanesReceipt as D11D12
import DASHI.Physics.QFT.ConductorVsDiscriminantReceipt as Cond

------------------------------------------------------------------------
-- Final lepton/quark separation aggregator.
--
-- This receipt consumes the existing first-layer separation receipt and the
-- five validated Manager-A companion receipts for the geometric split, D=-11
-- exception, D=-8 overlap, D=-11 isolation, and D=-12 overlap.
--
-- The old unit-group-only criterion is retired.  The replacement diagnostic
-- criterion is geometric level data: conductor-level coprimality/isolation
-- together with positional exhaustion of the first six Heegner discriminants.
-- This still does not derive Standard-Model charges or a physical lepton
-- sector; every promotion flag remains false.

data LeptonQuarkFinalStatus : Set where
  leptonQuarkFinalDiagnosticAggregated :
    LeptonQuarkFinalStatus

data GeometricLevelCriterion : Set where
  conductorLevelCoprimalityPlusPositionalExhaustion :
    GeometricLevelCriterion

data LeptonQuarkFinalBlocker : Set where
  unitGroupCriterionRetired :
    LeptonQuarkFinalBlocker

  d8AndD12HaveLevelOverlaps :
    LeptonQuarkFinalBlocker

  d11IsolationIsDiagnosticNotMechanism :
    LeptonQuarkFinalBlocker

  positionalExhaustionNotPhysicalDerivation :
    LeptonQuarkFinalBlocker

  noSMChargeOrLeptonSectorPromotion :
    LeptonQuarkFinalBlocker

canonicalLeptonQuarkFinalBlockers :
  List LeptonQuarkFinalBlocker
canonicalLeptonQuarkFinalBlockers =
  unitGroupCriterionRetired
  ∷ d8AndD12HaveLevelOverlaps
  ∷ d11IsolationIsDiagnosticNotMechanism
  ∷ positionalExhaustionNotPhysicalDerivation
  ∷ noSMChargeOrLeptonSectorPromotion
  ∷ []

data LeptonQuarkFinalPromotion : Set where

leptonQuarkFinalPromotionImpossibleHere :
  LeptonQuarkFinalPromotion →
  ⊥
leptonQuarkFinalPromotionImpossibleHere ()

geometricCriterionLabel : String
geometricCriterionLabel =
  "geometric level criterion = conductor-level coprimality/isolation plus positional exhaustion of |D|=3,4,7,8,11,12"

unitGroupRetirementLabel : String
unitGroupRetirementLabel =
  "unit-group order alone is retired: Z4/Z2=2 and shared Z2 lepton/quark candidates do not yield SM charge ratios"

d8OverlapLabel : String
d8OverlapLabel =
  "D=-8 has level 8 and overlaps the p2 level-4 geometry by factor 4"

d11IsolationLabel : String
d11IsolationLabel =
  "D=-11 has level 11 and is coprime to the active quark levels 3,4,7"

d12OverlapLabel : String
d12OverlapLabel =
  "D=-12 has level 12 and overlaps the p3 level-3 geometry by factor 3"

record LeptonQuarkSeparationFinalReceipt : Setω where
  field
    status :
      LeptonQuarkFinalStatus

    baseSeparationReceipt :
      Base.LeptonQuarkSeparationReceipt

    baseSeparationReceiptIsCanonical :
      baseSeparationReceipt ≡ Base.canonicalLeptonQuarkSeparationReceipt

    d8LeptonLaneReceipt :
      D8.D8LeptonLaneReceipt

    d8LeptonLaneReceiptIsCanonical :
      d8LeptonLaneReceipt ≡ D8.canonicalD8LeptonLaneReceipt

    geometricSplitReceipt :
      Split.QuarkLeptonGeometricSplitReceipt

    geometricSplitReceiptIsCanonical :
      geometricSplitReceipt
      ≡
      Split.canonicalQuarkLeptonGeometricSplitReceipt

    disc11ExceptionReceipt :
      D11.Disc11ExceptionReceipt

    disc11ExceptionReceiptIsCanonical :
      disc11ExceptionReceipt ≡ D11.canonicalDisc11ExceptionReceipt

    genOneOverlapReceiptConsumed :
      Bool

    genOneOverlapReceiptConsumedIsTrue :
      genOneOverlapReceiptConsumed ≡ true

    muonIsolationReceiptConsumed :
      Bool

    muonIsolationReceiptConsumedIsTrue :
      muonIsolationReceiptConsumed ≡ true

    tauOverlapReceiptConsumed :
      Bool

    tauOverlapReceiptConsumedIsTrue :
      tauOverlapReceiptConsumed ≡ true

    heegnerSequenceReceiptConsumed :
      Bool

    heegnerSequenceReceiptConsumedIsTrue :
      heegnerSequenceReceiptConsumed ≡ true

    ckmGapReceiptConsumed :
      Bool

    ckmGapReceiptConsumedIsTrue :
      ckmGapReceiptConsumed ≡ true

    d11d12LeptonLanesReceiptConsumed :
      Bool

    d11d12LeptonLanesReceiptConsumedIsTrue :
      d11d12LeptonLanesReceiptConsumed ≡ true

    conductorVsDiscriminantReceipt :
      Cond.ConductorVsDiscriminantReceipt

    conductorVsDiscriminantReceiptIsCanonical :
      conductorVsDiscriminantReceipt ≡ Cond.canonicalConductorVsDiscriminantReceipt

    unitGroupCriterionRetiredLabel :
      String

    unitGroupCriterionRetiredLabelIsCanonical :
      unitGroupCriterionRetiredLabel ≡ unitGroupRetirementLabel

    unitGroupCriterionRetiredFlag :
      Bool

    unitGroupCriterionRetiredFlagIsTrue :
      unitGroupCriterionRetiredFlag ≡ true

    baseUnitGroupCriterionFails :
      Base.unitGroupRatioGivesSMChargeRatio baseSeparationReceipt ≡ false

    geometricLevelCriterion :
      GeometricLevelCriterion

    geometricLevelCriterionLabel :
      String

    geometricLevelCriterionLabelIsCanonical :
      geometricLevelCriterionLabel ≡ geometricCriterionLabel

    conductorLevelCoprimalityRecorded :
      Bool

    conductorLevelCoprimalityRecordedIsTrue :
      conductorLevelCoprimalityRecorded ≡ true

    positionalExhaustionRecorded :
      Bool

    positionalExhaustionRecordedIsTrue :
      positionalExhaustionRecorded ≡ true

    positionalRuleStillHypothesis :
      Seq.positionalRuleDerived
        Seq.canonicalHeegnerSequenceQuarkLeptonReceipt
      ≡
      false

    d8Level :
      Nat

    d8LevelIsEight :
      d8Level ≡ 8

    d8OverlapFactorWithP2 :
      Nat

    d8OverlapFactorWithP2IsFour :
      d8OverlapFactorWithP2 ≡ 4

    d8YukawaRatioNumerator :
      Nat

    d8YukawaRatioNumeratorIsOne :
      d8YukawaRatioNumerator ≡ 1

    d8YukawaRatioDenominator :
      Nat

    d8YukawaRatioDenominatorIsTwo :
      d8YukawaRatioDenominator ≡ 2

    d8OverlapFactorLabel :
      String

    d8OverlapFactorLabelIsCanonical :
      d8OverlapFactorLabel ≡ d8OverlapLabel

    d11Level :
      Nat

    d11LevelIsEleven :
      d11Level ≡ 11

    d11IsolationFromQuarkLevels :
      Bool

    d11IsolationFromQuarkLevelsIsTrue :
      d11IsolationFromQuarkLevels ≡ true

    d11LevelOverlapClassificationFalse :
      D11.levelOverlapClassifiesDisc11AsLepton
        disc11ExceptionReceipt
      ≡
      false

    d11LeadingOrderYukawaZero :
      Muon.leadingOrderDirectYukawaZero
        Muon.canonicalMuonNeutrinoIsolationReceipt
      ≡
      true

    d11IsolationLabelField :
      String

    d11IsolationLabelFieldIsCanonical :
      d11IsolationLabelField ≡ d11IsolationLabel

    d12Level :
      Nat

    d12LevelIsTwelve :
      d12Level ≡ 12

    d12OverlapFactorWithP3 :
      Nat

    d12OverlapFactorWithP3IsThree :
      d12OverlapFactorWithP3 ≡ 3

    d12TauToP3RatioDenominator :
      Nat

    d12TauToP3RatioDenominatorIsThree :
      d12TauToP3RatioDenominator ≡ 3

    d12TauToP2RatioDenominator :
      Nat

    d12TauToP2RatioDenominatorIsFour :
      d12TauToP2RatioDenominator ≡ 4

    d12OverlapFactorLabel :
      String

    d12OverlapFactorLabelIsCanonical :
      d12OverlapFactorLabel ≡ d12OverlapLabel

    d11d12LeptonSectorStillOpen :
      D11D12.leptonSectorConstructed
        D11D12.canonicalD11D12LeptonLanesReceipt
      ≡
      false

    positionalGapRouteNegative :
      Gap.negativeDiagnosticRecorded
        Gap.canonicalCKMHierarchyFromHeegnerPositionReceipt
      ≡
      true

    physicalLeptonQuarkSeparationPromoted :
      Bool

    physicalLeptonQuarkSeparationPromotedIsFalse :
      physicalLeptonQuarkSeparationPromoted ≡ false

    smChargeRatioDerived :
      Bool

    smChargeRatioDerivedIsFalse :
      smChargeRatioDerived ≡ false

    leptonSectorPromoted :
      Bool

    leptonSectorPromotedIsFalse :
      leptonSectorPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    blockers :
      List LeptonQuarkFinalBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonQuarkFinalBlockers

    promotionFlags :
      List LeptonQuarkFinalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open LeptonQuarkSeparationFinalReceipt public

canonicalLeptonQuarkSeparationFinalReceipt :
  LeptonQuarkSeparationFinalReceipt
canonicalLeptonQuarkSeparationFinalReceipt =
  record
    { status =
        leptonQuarkFinalDiagnosticAggregated
    ; baseSeparationReceipt =
        Base.canonicalLeptonQuarkSeparationReceipt
    ; baseSeparationReceiptIsCanonical =
        refl
    ; d8LeptonLaneReceipt =
        D8.canonicalD8LeptonLaneReceipt
    ; d8LeptonLaneReceiptIsCanonical =
        refl
    ; geometricSplitReceipt =
        Split.canonicalQuarkLeptonGeometricSplitReceipt
    ; geometricSplitReceiptIsCanonical =
        refl
    ; disc11ExceptionReceipt =
        D11.canonicalDisc11ExceptionReceipt
    ; disc11ExceptionReceiptIsCanonical =
        refl
    ; genOneOverlapReceiptConsumed =
        true
    ; genOneOverlapReceiptConsumedIsTrue =
        refl
    ; muonIsolationReceiptConsumed =
        true
    ; muonIsolationReceiptConsumedIsTrue =
        refl
    ; tauOverlapReceiptConsumed =
        true
    ; tauOverlapReceiptConsumedIsTrue =
        refl
    ; heegnerSequenceReceiptConsumed =
        true
    ; heegnerSequenceReceiptConsumedIsTrue =
        refl
    ; ckmGapReceiptConsumed =
        true
    ; ckmGapReceiptConsumedIsTrue =
        refl
    ; d11d12LeptonLanesReceiptConsumed =
        true
    ; d11d12LeptonLanesReceiptConsumedIsTrue =
        refl
    ; conductorVsDiscriminantReceipt =
        Cond.canonicalConductorVsDiscriminantReceipt
    ; conductorVsDiscriminantReceiptIsCanonical =
        refl
    ; unitGroupCriterionRetiredLabel =
        unitGroupRetirementLabel
    ; unitGroupCriterionRetiredLabelIsCanonical =
        refl
    ; unitGroupCriterionRetiredFlag =
        true
    ; unitGroupCriterionRetiredFlagIsTrue =
        refl
    ; baseUnitGroupCriterionFails =
        refl
    ; geometricLevelCriterion =
        conductorLevelCoprimalityPlusPositionalExhaustion
    ; geometricLevelCriterionLabel =
        geometricCriterionLabel
    ; geometricLevelCriterionLabelIsCanonical =
        refl
    ; conductorLevelCoprimalityRecorded =
        true
    ; conductorLevelCoprimalityRecordedIsTrue =
        refl
    ; positionalExhaustionRecorded =
        true
    ; positionalExhaustionRecordedIsTrue =
        refl
    ; positionalRuleStillHypothesis =
        refl
    ; d8Level =
        8
    ; d8LevelIsEight =
        refl
    ; d8OverlapFactorWithP2 =
        4
    ; d8OverlapFactorWithP2IsFour =
        refl
    ; d8YukawaRatioNumerator =
        1
    ; d8YukawaRatioNumeratorIsOne =
        refl
    ; d8YukawaRatioDenominator =
        2
    ; d8YukawaRatioDenominatorIsTwo =
        refl
    ; d8OverlapFactorLabel =
        d8OverlapLabel
    ; d8OverlapFactorLabelIsCanonical =
        refl
    ; d11Level =
        11
    ; d11LevelIsEleven =
        refl
    ; d11IsolationFromQuarkLevels =
        true
    ; d11IsolationFromQuarkLevelsIsTrue =
        refl
    ; d11LevelOverlapClassificationFalse =
        refl
    ; d11LeadingOrderYukawaZero =
        refl
    ; d11IsolationLabelField =
        d11IsolationLabel
    ; d11IsolationLabelFieldIsCanonical =
        refl
    ; d12Level =
        12
    ; d12LevelIsTwelve =
        refl
    ; d12OverlapFactorWithP3 =
        3
    ; d12OverlapFactorWithP3IsThree =
        refl
    ; d12TauToP3RatioDenominator =
        3
    ; d12TauToP3RatioDenominatorIsThree =
        refl
    ; d12TauToP2RatioDenominator =
        4
    ; d12TauToP2RatioDenominatorIsFour =
        refl
    ; d12OverlapFactorLabel =
        d12OverlapLabel
    ; d12OverlapFactorLabelIsCanonical =
        refl
    ; d11d12LeptonSectorStillOpen =
        refl
    ; positionalGapRouteNegative =
        refl
    ; physicalLeptonQuarkSeparationPromoted =
        false
    ; physicalLeptonQuarkSeparationPromotedIsFalse =
        refl
    ; smChargeRatioDerived =
        false
    ; smChargeRatioDerivedIsFalse =
        refl
    ; leptonSectorPromoted =
        false
    ; leptonSectorPromotedIsFalse =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; blockers =
        canonicalLeptonQuarkFinalBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Aggregates the base receipt plus five validated Manager-A geometric split companion receipts"
        ∷ "Retires the unit-group-only criterion as insufficient for SM charge ratios"
        ∷ "Records the geometric level criterion as conductor-level coprimality/isolation plus positional exhaustion"
        ∷ "D=-8 overlaps p2 level geometry by factor 4 and gives diagnostic ratio 1/2"
        ∷ "D=-12 overlaps p3 level geometry by factor 3 and records tau ratios 1/3 and 1/4"
        ∷ "D=-11 is level-11 isolated from active quark levels 3,4,7 with leading direct Yukawa zero"
        ∷ "All lepton/quark, charge, Standard Model, and G_DHR~=G_SM promotions remain false"
        ∷ []
    }

leptonQuarkFinalRetiresUnitGroupCriterion :
  unitGroupCriterionRetiredFlag canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  true
leptonQuarkFinalRetiresUnitGroupCriterion =
  refl

leptonQuarkFinalRecordsD8OverlapFactor :
  d8OverlapFactorWithP2 canonicalLeptonQuarkSeparationFinalReceipt ≡ 4
leptonQuarkFinalRecordsD8OverlapFactor =
  refl

leptonQuarkFinalRecordsD11Isolation :
  d11IsolationFromQuarkLevels canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  true
leptonQuarkFinalRecordsD11Isolation =
  refl

leptonQuarkFinalRecordsD12OverlapFactor :
  d12OverlapFactorWithP3 canonicalLeptonQuarkSeparationFinalReceipt ≡ 3
leptonQuarkFinalRecordsD12OverlapFactor =
  refl

leptonQuarkFinalNoPromotionFlags :
  promotionFlags canonicalLeptonQuarkSeparationFinalReceipt ≡ []
leptonQuarkFinalNoPromotionFlags =
  refl
