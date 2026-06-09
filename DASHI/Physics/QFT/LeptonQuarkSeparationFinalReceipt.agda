module DASHI.Physics.QFT.LeptonQuarkSeparationFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.HeegnerOrderingPrincipleReceipt as Heegner
import DASHI.Physics.QFT.LeptonSectorGapReceipt as Gap
import DASHI.Physics.QFT.MuonNeutrinoIsolationReceipt as Muon
import DASHI.Physics.QFT.QuarkLeptonCMUnitGroupReceipt as UnitGroup
import DASHI.Physics.QFT.TauLeptonGen3OverlapReceipt as Tau

------------------------------------------------------------------------
-- Final aggregate quark/lepton separation receipt.
--
-- This aggregate retires the CM unit-group order criterion and records the
-- replacement bookkeeping: conductor-level coprimality for D=-11/level 11,
-- overlap ratios for D=-12, and positional exhaustion of the first-six
-- Heegner candidate matter lanes.  It remains a receipt of structural
-- diagnostics only.  Exact lepton, quark, SM, G_DHR ~= G_SM, and terminal
-- promotions are all explicitly false.

data LeptonQuarkSeparationFinalStatus : Set where
  conductorCoprimalityAndPositionRecorded :
    LeptonQuarkSeparationFinalStatus

data SeparationCriterionStatus : Set where
  unitGroupCriterionRetired :
    SeparationCriterionStatus

data PositionalExhaustionStatus : Set where
  firstSixCandidateMatterPositionsExhausted :
    PositionalExhaustionStatus

data LeptonQuarkSeparationFinalBlocker : Set where
  unitGroupCriterionRetiredNoReplacementPromotion :
    LeptonQuarkSeparationFinalBlocker

  conductorCoprimalityDiagnosticOnly :
    LeptonQuarkSeparationFinalBlocker

  positionalExhaustionNotFourthGenerationProof :
    LeptonQuarkSeparationFinalBlocker

  exactLeptonSectorMissing :
    LeptonQuarkSeparationFinalBlocker

  exactQuarkSectorMissing :
    LeptonQuarkSeparationFinalBlocker

  exactDHRSMFunctorMissing :
    LeptonQuarkSeparationFinalBlocker

canonicalLeptonQuarkSeparationFinalBlockers :
  List LeptonQuarkSeparationFinalBlocker
canonicalLeptonQuarkSeparationFinalBlockers =
  unitGroupCriterionRetiredNoReplacementPromotion
  ∷ conductorCoprimalityDiagnosticOnly
  ∷ positionalExhaustionNotFourthGenerationProof
  ∷ exactLeptonSectorMissing
  ∷ exactQuarkSectorMissing
  ∷ exactDHRSMFunctorMissing
  ∷ []

data LeptonQuarkSeparationFinalPromotion : Set where

leptonQuarkSeparationFinalPromotionImpossibleHere :
  LeptonQuarkSeparationFinalPromotion →
  ⊥
leptonQuarkSeparationFinalPromotionImpossibleHere ()

unitGroupCriterionRetiredLabel : String
unitGroupCriterionRetiredLabel =
  "unit-group order criterion is retired because D=-7 and lepton candidates share Z/2"

conductorCoprimalityLabel : String
conductorCoprimalityLabel =
  "conductor-level coprimality records D=-11 level 11 against quark levels 3, 4, and 7"

positionalExhaustionLabel : String
positionalExhaustionLabel =
  "first-six Heegner candidate matter positions are exhausted as three quark-candidate plus three lepton-candidate positions"

receiptBoundaryLabel : String
receiptBoundaryLabel =
  "aggregate separation remains diagnostic; exact lepton/quark/SM/G_DHR/terminal promotions remain false"

record LeptonQuarkSeparationFinalReceipt : Setω where
  field
    leptonSectorGapReceipt :
      Gap.LeptonSectorGapReceipt

    heegnerOrderingReceipt :
      Heegner.HeegnerOrderingPrincipleReceipt

    unitGroupReceipt :
      UnitGroup.QuarkLeptonCMUnitGroupReceipt

    muonNeutrinoIsolationReceipt :
      Muon.MuonNeutrinoIsolationReceipt

    tauLeptonGen3OverlapReceipt :
      Tau.TauLeptonGen3OverlapReceipt

    status :
      LeptonQuarkSeparationFinalStatus

    statusIsConductorAndPositionRecorded :
      status ≡ conductorCoprimalityAndPositionRecorded

    retiredCriterionStatus :
      SeparationCriterionStatus

    retiredCriterionStatusIsUnitGroup :
      retiredCriterionStatus ≡ unitGroupCriterionRetired

    unitGroupCriterionRetiredStatement :
      String

    unitGroupCriterionRetiredStatementIsCanonical :
      unitGroupCriterionRetiredStatement ≡ unitGroupCriterionRetiredLabel

    unitGroupOrderAloneSeparatesQuarkLepton :
      Bool

    unitGroupOrderAloneSeparatesQuarkLeptonIsFalse :
      unitGroupOrderAloneSeparatesQuarkLepton ≡ false

    conductorCoprimalityStatement :
      String

    conductorCoprimalityStatementIsCanonical :
      conductorCoprimalityStatement ≡ conductorCoprimalityLabel

    dMinusElevenLevel :
      Nat

    dMinusElevenLevelIsEleven :
      dMinusElevenLevel ≡ 11

    gcdElevenWithThree :
      Nat

    gcdElevenWithThreeIsOne :
      gcdElevenWithThree ≡ 1

    gcdElevenWithFour :
      Nat

    gcdElevenWithFourIsOne :
      gcdElevenWithFour ≡ 1

    gcdElevenWithSeven :
      Nat

    gcdElevenWithSevenIsOne :
      gcdElevenWithSeven ≡ 1

    conductorLevelCoprimalityRecorded :
      Bool

    conductorLevelCoprimalityRecordedIsTrue :
      conductorLevelCoprimalityRecorded ≡ true

    leadingDirectQuarkLeptonYukawaPresent :
      Bool

    leadingDirectQuarkLeptonYukawaPresentIsFalse :
      leadingDirectQuarkLeptonYukawaPresent ≡ false

    tauToP3RatioNumerator :
      Nat

    tauToP3RatioNumeratorIsOne :
      tauToP3RatioNumerator ≡ 1

    tauToP3RatioDenominator :
      Nat

    tauToP3RatioDenominatorIsThree :
      tauToP3RatioDenominator ≡ 3

    tauToP2RatioNumerator :
      Nat

    tauToP2RatioNumeratorIsOne :
      tauToP2RatioNumerator ≡ 1

    tauToP2RatioDenominator :
      Nat

    tauToP2RatioDenominatorIsFour :
      tauToP2RatioDenominator ≡ 4

    positionalExhaustionStatus :
      PositionalExhaustionStatus

    positionalExhaustionStatusIsFirstSix :
      positionalExhaustionStatus
      ≡
      firstSixCandidateMatterPositionsExhausted

    positionalExhaustionStatement :
      String

    positionalExhaustionStatementIsCanonical :
      positionalExhaustionStatement ≡ positionalExhaustionLabel

    firstThreeQuarkCandidatePositions :
      List Nat

    firstThreeQuarkCandidatePositionsAreCanonical :
      firstThreeQuarkCandidatePositions
      ≡
      Heegner.canonicalFirstThreeQuarkDiscriminants

    nextThreeLeptonCandidatePositions :
      List Nat

    nextThreeLeptonCandidatePositionsAreCanonical :
      nextThreeLeptonCandidatePositions
      ≡
      Heegner.canonicalNextThreeLeptonDiscriminants

    firstSixMatterCandidatePositions :
      List Nat

    firstSixMatterCandidatePositionsAreCanonical :
      firstSixMatterCandidatePositions
      ≡
      Heegner.canonicalFirstSixMatterLaneDiscriminants

    firstSixCandidateMatterPositionsExhaustedFlag :
      Bool

    firstSixCandidateMatterPositionsExhaustedFlagIsTrue :
      firstSixCandidateMatterPositionsExhaustedFlag ≡ true

    fourthGenerationAbsencePromoted :
      Bool

    fourthGenerationAbsencePromotedIsFalse :
      fourthGenerationAbsencePromoted ≡ false

    exactLeptonPromotion :
      Bool

    exactLeptonPromotionIsFalse :
      exactLeptonPromotion ≡ false

    exactQuarkPromotion :
      Bool

    exactQuarkPromotionIsFalse :
      exactQuarkPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    blockers :
      List LeptonQuarkSeparationFinalBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonQuarkSeparationFinalBlockers

    promotionFlags :
      List LeptonQuarkSeparationFinalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryLabel

    auditTrail :
      List String

open LeptonQuarkSeparationFinalReceipt public

canonicalLeptonQuarkSeparationFinalReceipt :
  LeptonQuarkSeparationFinalReceipt
canonicalLeptonQuarkSeparationFinalReceipt =
  record
    { leptonSectorGapReceipt =
        Gap.canonicalLeptonSectorGapReceipt
    ; heegnerOrderingReceipt =
        Heegner.canonicalHeegnerOrderingPrincipleReceipt
    ; unitGroupReceipt =
        UnitGroup.canonicalQuarkLeptonCMUnitGroupReceipt
    ; muonNeutrinoIsolationReceipt =
        Muon.canonicalMuonNeutrinoIsolationReceipt
    ; tauLeptonGen3OverlapReceipt =
        Tau.canonicalTauLeptonGen3OverlapReceipt
    ; status =
        conductorCoprimalityAndPositionRecorded
    ; statusIsConductorAndPositionRecorded =
        refl
    ; retiredCriterionStatus =
        unitGroupCriterionRetired
    ; retiredCriterionStatusIsUnitGroup =
        refl
    ; unitGroupCriterionRetiredStatement =
        unitGroupCriterionRetiredLabel
    ; unitGroupCriterionRetiredStatementIsCanonical =
        refl
    ; unitGroupOrderAloneSeparatesQuarkLepton =
        false
    ; unitGroupOrderAloneSeparatesQuarkLeptonIsFalse =
        refl
    ; conductorCoprimalityStatement =
        conductorCoprimalityLabel
    ; conductorCoprimalityStatementIsCanonical =
        refl
    ; dMinusElevenLevel =
        11
    ; dMinusElevenLevelIsEleven =
        refl
    ; gcdElevenWithThree =
        Muon.gcdLevel11WithP3 Muon.canonicalMuonNeutrinoIsolationReceipt
    ; gcdElevenWithThreeIsOne =
        refl
    ; gcdElevenWithFour =
        Muon.gcdLevel11WithP2 Muon.canonicalMuonNeutrinoIsolationReceipt
    ; gcdElevenWithFourIsOne =
        refl
    ; gcdElevenWithSeven =
        Muon.gcdLevel11WithP5 Muon.canonicalMuonNeutrinoIsolationReceipt
    ; gcdElevenWithSevenIsOne =
        refl
    ; conductorLevelCoprimalityRecorded =
        true
    ; conductorLevelCoprimalityRecordedIsTrue =
        refl
    ; leadingDirectQuarkLeptonYukawaPresent =
        Muon.leadingDirectQuarkLeptonYukawaPresent
          Muon.canonicalMuonNeutrinoIsolationReceipt
    ; leadingDirectQuarkLeptonYukawaPresentIsFalse =
        refl
    ; tauToP3RatioNumerator =
        Tau.tauToP3RatioNumerator
          Tau.canonicalTauLeptonGen3OverlapReceipt
    ; tauToP3RatioNumeratorIsOne =
        refl
    ; tauToP3RatioDenominator =
        Tau.tauToP3RatioDenominator
          Tau.canonicalTauLeptonGen3OverlapReceipt
    ; tauToP3RatioDenominatorIsThree =
        refl
    ; tauToP2RatioNumerator =
        Tau.tauToP2RatioNumerator
          Tau.canonicalTauLeptonGen3OverlapReceipt
    ; tauToP2RatioNumeratorIsOne =
        refl
    ; tauToP2RatioDenominator =
        Tau.tauToP2RatioDenominator
          Tau.canonicalTauLeptonGen3OverlapReceipt
    ; tauToP2RatioDenominatorIsFour =
        refl
    ; positionalExhaustionStatus =
        firstSixCandidateMatterPositionsExhausted
    ; positionalExhaustionStatusIsFirstSix =
        refl
    ; positionalExhaustionStatement =
        positionalExhaustionLabel
    ; positionalExhaustionStatementIsCanonical =
        refl
    ; firstThreeQuarkCandidatePositions =
        Heegner.canonicalFirstThreeQuarkDiscriminants
    ; firstThreeQuarkCandidatePositionsAreCanonical =
        refl
    ; nextThreeLeptonCandidatePositions =
        Heegner.canonicalNextThreeLeptonDiscriminants
    ; nextThreeLeptonCandidatePositionsAreCanonical =
        refl
    ; firstSixMatterCandidatePositions =
        Heegner.canonicalFirstSixMatterLaneDiscriminants
    ; firstSixMatterCandidatePositionsAreCanonical =
        refl
    ; firstSixCandidateMatterPositionsExhaustedFlag =
        true
    ; firstSixCandidateMatterPositionsExhaustedFlagIsTrue =
        refl
    ; fourthGenerationAbsencePromoted =
        false
    ; fourthGenerationAbsencePromotedIsFalse =
        refl
    ; exactLeptonPromotion =
        false
    ; exactLeptonPromotionIsFalse =
        refl
    ; exactQuarkPromotion =
        false
    ; exactQuarkPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalLeptonQuarkSeparationFinalBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        receiptBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        unitGroupCriterionRetiredLabel
        ∷ conductorCoprimalityLabel
        ∷ "D=-11 supplies no leading direct quark-lepton Yukawa overlap"
        ∷ "D=-12 supplies tau-to-p3 ratio 1/3 and tau-to-p2 ratio 1/4"
        ∷ positionalExhaustionLabel
        ∷ receiptBoundaryLabel
        ∷ []
    }

leptonQuarkSeparationFinalRetiresUnitGroupCriterion :
  unitGroupOrderAloneSeparatesQuarkLepton
    canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  false
leptonQuarkSeparationFinalRetiresUnitGroupCriterion =
  refl

leptonQuarkSeparationFinalRecordsConductorCoprimality :
  conductorLevelCoprimalityRecorded
    canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  true
leptonQuarkSeparationFinalRecordsConductorCoprimality =
  refl

leptonQuarkSeparationFinalRecordsPositionalExhaustion :
  firstSixCandidateMatterPositionsExhaustedFlag
    canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  true
leptonQuarkSeparationFinalRecordsPositionalExhaustion =
  refl

leptonQuarkSeparationFinalNoSMPromotion :
  exactStandardModelPromotion canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  false
leptonQuarkSeparationFinalNoSMPromotion =
  refl

leptonQuarkSeparationFinalNoTerminalPromotion :
  terminalClaimPromoted canonicalLeptonQuarkSeparationFinalReceipt
  ≡
  false
leptonQuarkSeparationFinalNoTerminalPromotion =
  refl

leptonQuarkSeparationFinalNoPromotion :
  LeptonQuarkSeparationFinalPromotion →
  ⊥
leptonQuarkSeparationFinalNoPromotion =
  leptonQuarkSeparationFinalPromotionImpossibleHere
