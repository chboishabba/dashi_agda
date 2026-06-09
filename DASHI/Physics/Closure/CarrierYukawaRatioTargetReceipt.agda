module DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierMixingReceipt as CKMMix
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility as YDHR
import DASHI.Physics.Closure.YukawaFromCarrier as YFC

------------------------------------------------------------------------
-- Carrier-Yukawa ratio target receipt.
--
-- This file names the next computable ratio targets for the carrier-Yukawa
-- frontier.  It deliberately does not turn carrier entries into physical
-- fermion mass predictions: physical running masses, Higgs/VEV normalisation,
-- DHR sector representations, non-identity intertwiners, and absolute W4 scale
-- authority remain threaded from the existing receipts.

data CarrierYukawaRatioLane : Set where
  upCarrierYukawaRatioLane :
    CarrierYukawaRatioLane

  downCarrierYukawaRatioLane :
    CarrierYukawaRatioLane

  chargedLeptonCarrierYukawaRatioLane :
    CarrierYukawaRatioLane

canonicalCarrierYukawaRatioLanes :
  List CarrierYukawaRatioLane
canonicalCarrierYukawaRatioLanes =
  upCarrierYukawaRatioLane
  ∷ downCarrierYukawaRatioLane
  ∷ chargedLeptonCarrierYukawaRatioLane
  ∷ []

data CarrierYukawaRatioTarget : Set where
  upOverCharmCarrierTarget :
    CarrierYukawaRatioTarget

  upOverTopCarrierTarget :
    CarrierYukawaRatioTarget

  charmOverTopCarrierTarget :
    CarrierYukawaRatioTarget

  downOverBottomCarrierTarget :
    CarrierYukawaRatioTarget

  strangeOverBottomCarrierTarget :
    CarrierYukawaRatioTarget

  electronOverMuonCarrierTarget :
    CarrierYukawaRatioTarget

  muonOverTauCarrierTarget :
    CarrierYukawaRatioTarget

canonicalCarrierYukawaRatioTargets :
  List CarrierYukawaRatioTarget
canonicalCarrierYukawaRatioTargets =
  upOverCharmCarrierTarget
  ∷ upOverTopCarrierTarget
  ∷ charmOverTopCarrierTarget
  ∷ downOverBottomCarrierTarget
  ∷ strangeOverBottomCarrierTarget
  ∷ electronOverMuonCarrierTarget
  ∷ muonOverTauCarrierTarget
  ∷ []

data CarrierYukawaRatioReadiness : Set where
  carrierEntriesAvailablePhysicalPromotionBlocked :
    CarrierYukawaRatioReadiness

  chargedLeptonCarrierMissing :
    CarrierYukawaRatioReadiness

data CarrierYukawaRatioBlocker : Set where
  missingChargedLeptonYukawaCarrier :
    CarrierYukawaRatioBlocker

  missingPhysicalFermionMassReceiptForRatios :
    CarrierYukawaRatioBlocker

  missingRunningScaleAndThresholdConvention :
    CarrierYukawaRatioBlocker

  missingAbsoluteHiggsVEVW4CalibrationForRatios :
    CarrierYukawaRatioBlocker

  missingActualDHRSectorRepresentationsForRatios :
    CarrierYukawaRatioBlocker

  missingNonIdentityDHRIntertwinerForRatioPromotion :
    CarrierYukawaRatioBlocker

  missingAlphaTargetBoundForCarrierMassRatio :
    CarrierYukawaRatioBlocker

canonicalCarrierYukawaRatioBlockers :
  List CarrierYukawaRatioBlocker
canonicalCarrierYukawaRatioBlockers =
  missingChargedLeptonYukawaCarrier
  ∷ missingPhysicalFermionMassReceiptForRatios
  ∷ missingRunningScaleAndThresholdConvention
  ∷ missingAbsoluteHiggsVEVW4CalibrationForRatios
  ∷ missingActualDHRSectorRepresentationsForRatios
  ∷ missingNonIdentityDHRIntertwinerForRatioPromotion
  ∷ missingAlphaTargetBoundForCarrierMassRatio
  ∷ []

record ExistingCarrierYukawaRatioBinding : Setω where
  field
    target :
      CarrierYukawaRatioTarget

    lane :
      CarrierYukawaRatioLane

    readiness :
      CarrierYukawaRatioReadiness

    readinessIsCarrierAvailable :
      readiness ≡ carrierEntriesAvailablePhysicalPromotionBlocked

    numeratorEntry :
      Matter.MixingGaussianRationalDatum

    denominatorEntry :
      Matter.MixingGaussianRationalDatum

    numeratorFromFormulaSurface :
      Matter.MixingGaussianRationalDatum

    denominatorFromFormulaSurface :
      Matter.MixingGaussianRationalDatum

    numeratorEntryMatchesFormulaSurface :
      numeratorEntry ≡ numeratorFromFormulaSurface

    denominatorEntryMatchesFormulaSurface :
      denominatorEntry ≡ denominatorFromFormulaSurface

    numeratorEntryMatchesExactCarrier :
      Bool

    numeratorEntryMatchesExactCarrierIsTrue :
      numeratorEntryMatchesExactCarrier ≡ true

    denominatorEntryMatchesExactCarrier :
      Bool

    denominatorEntryMatchesExactCarrierIsTrue :
      denominatorEntryMatchesExactCarrier ≡ true

    physicalRatioPromoted :
      Bool

    physicalRatioPromotedIsFalse :
      physicalRatioPromoted ≡ false

    bindingBoundary :
      List String

open ExistingCarrierYukawaRatioBinding public

canonicalUpOverCharmCarrierRatioBinding :
  ExistingCarrierYukawaRatioBinding
canonicalUpOverCharmCarrierRatioBinding =
  record
    { target =
        upOverCharmCarrierTarget
    ; lane =
        upCarrierYukawaRatioLane
    ; readiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; readinessIsCarrierAvailable =
        refl
    ; numeratorEntry =
        Matter.v11 YFC.canonicalUpYukawaMatrix
    ; denominatorEntry =
        Matter.v22 YFC.canonicalUpYukawaMatrix
    ; numeratorFromFormulaSurface =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.firstGeneration
          YDHR.firstGeneration
    ; denominatorFromFormulaSurface =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.secondGeneration
          YDHR.secondGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; numeratorEntryMatchesExactCarrier =
        true
    ; numeratorEntryMatchesExactCarrierIsTrue =
        refl
    ; denominatorEntryMatchesExactCarrier =
        true
    ; denominatorEntryMatchesExactCarrierIsTrue =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; bindingBoundary =
        "m_u/m_c target is bound to the first and second diagonal entries of the canonical up carrier-Yukawa matrix"
        ∷ "The same entries are exposed through the carrier DHR formula surface"
        ∷ "No physical running-mass or Higgs-normalised m_u/m_c prediction is promoted"
        ∷ []
    }

canonicalUpOverTopCarrierRatioBinding :
  ExistingCarrierYukawaRatioBinding
canonicalUpOverTopCarrierRatioBinding =
  record
    { target =
        upOverTopCarrierTarget
    ; lane =
        upCarrierYukawaRatioLane
    ; readiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; readinessIsCarrierAvailable =
        refl
    ; numeratorEntry =
        Matter.v11 YFC.canonicalUpYukawaMatrix
    ; denominatorEntry =
        Matter.v33 YFC.canonicalUpYukawaMatrix
    ; numeratorFromFormulaSurface =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.firstGeneration
          YDHR.firstGeneration
    ; denominatorFromFormulaSurface =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.thirdGeneration
          YDHR.thirdGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; numeratorEntryMatchesExactCarrier =
        true
    ; numeratorEntryMatchesExactCarrierIsTrue =
        refl
    ; denominatorEntryMatchesExactCarrier =
        true
    ; denominatorEntryMatchesExactCarrierIsTrue =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; bindingBoundary =
        "u/t target is bound to the first and third diagonal entries of the canonical up carrier-Yukawa matrix"
        ∷ "The same entries are exposed through the carrier DHR formula surface"
        ∷ "No physical running-mass or Higgs-normalised u/t prediction is promoted"
        ∷ []
    }

canonicalCharmOverTopCarrierRatioBinding :
  ExistingCarrierYukawaRatioBinding
canonicalCharmOverTopCarrierRatioBinding =
  record
    { target =
        charmOverTopCarrierTarget
    ; lane =
        upCarrierYukawaRatioLane
    ; readiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; readinessIsCarrierAvailable =
        refl
    ; numeratorEntry =
        Matter.v22 YFC.canonicalUpYukawaMatrix
    ; denominatorEntry =
        Matter.v33 YFC.canonicalUpYukawaMatrix
    ; numeratorFromFormulaSurface =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.secondGeneration
          YDHR.secondGeneration
    ; denominatorFromFormulaSurface =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.thirdGeneration
          YDHR.thirdGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; numeratorEntryMatchesExactCarrier =
        true
    ; numeratorEntryMatchesExactCarrierIsTrue =
        refl
    ; denominatorEntryMatchesExactCarrier =
        true
    ; denominatorEntryMatchesExactCarrierIsTrue =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; bindingBoundary =
        "c/t target is bound to the second and third diagonal entries of the canonical up carrier-Yukawa matrix"
        ∷ "The same entries are exposed through the carrier DHR formula surface"
        ∷ "No physical running-mass or Higgs-normalised c/t prediction is promoted"
        ∷ []
    }

canonicalDownOverBottomCarrierRatioBinding :
  ExistingCarrierYukawaRatioBinding
canonicalDownOverBottomCarrierRatioBinding =
  record
    { target =
        downOverBottomCarrierTarget
    ; lane =
        downCarrierYukawaRatioLane
    ; readiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; readinessIsCarrierAvailable =
        refl
    ; numeratorEntry =
        Matter.v11 YFC.canonicalDownYukawaMatrix
    ; denominatorEntry =
        Matter.v33 YFC.canonicalDownYukawaMatrix
    ; numeratorFromFormulaSurface =
        YDHR.downFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.firstGeneration
          YDHR.firstGeneration
    ; denominatorFromFormulaSurface =
        YDHR.downFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.thirdGeneration
          YDHR.thirdGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; numeratorEntryMatchesExactCarrier =
        true
    ; numeratorEntryMatchesExactCarrierIsTrue =
        refl
    ; denominatorEntryMatchesExactCarrier =
        true
    ; denominatorEntryMatchesExactCarrierIsTrue =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; bindingBoundary =
        "d/b target is bound to the first and third diagonal entries of the canonical down carrier-Yukawa matrix"
        ∷ "The same entries are exposed through the carrier DHR formula surface"
        ∷ "No physical running-mass or Higgs-normalised d/b prediction is promoted"
        ∷ []
    }

canonicalStrangeOverBottomCarrierRatioBinding :
  ExistingCarrierYukawaRatioBinding
canonicalStrangeOverBottomCarrierRatioBinding =
  record
    { target =
        strangeOverBottomCarrierTarget
    ; lane =
        downCarrierYukawaRatioLane
    ; readiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; readinessIsCarrierAvailable =
        refl
    ; numeratorEntry =
        Matter.v22 YFC.canonicalDownYukawaMatrix
    ; denominatorEntry =
        Matter.v33 YFC.canonicalDownYukawaMatrix
    ; numeratorFromFormulaSurface =
        YDHR.downFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.secondGeneration
          YDHR.secondGeneration
    ; denominatorFromFormulaSurface =
        YDHR.downFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.thirdGeneration
          YDHR.thirdGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; numeratorEntryMatchesExactCarrier =
        true
    ; numeratorEntryMatchesExactCarrierIsTrue =
        refl
    ; denominatorEntryMatchesExactCarrier =
        true
    ; denominatorEntryMatchesExactCarrierIsTrue =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; bindingBoundary =
        "s/b target is bound to the second and third diagonal entries of the canonical down carrier-Yukawa matrix"
        ∷ "The same entries are exposed through the carrier DHR formula surface"
        ∷ "No physical running-mass or Higgs-normalised s/b prediction is promoted"
        ∷ []
    }

record CarrierDiagonalAlphaRatioTargetBinding : Setω where
  field
    ratioTarget :
      CarrierYukawaRatioTarget

    ratioLane :
      CarrierYukawaRatioLane

    ratioReadiness :
      CarrierYukawaRatioReadiness

    ratioReadinessIsCarrierAvailable :
      ratioReadiness ≡ carrierEntriesAvailablePhysicalPromotionBlocked

    ratioNumeratorMassLabel :
      String

    ratioDenominatorMassLabel :
      String

    numeratorCarrierDepthLabel :
      String

    denominatorCarrierDepthLabel :
      String

    numeratorCarrierDepthSlot :
      Nat

    denominatorCarrierDepthSlot :
      Nat

    carrierDepthSeparation :
      Nat

    carrierDepthSeparationRecorded :
      Bool

    carrierDepthSeparationRecordedIsTrue :
      carrierDepthSeparationRecorded ≡ true

    alphaExponentFormula :
      String

    alphaPowerFormula :
      String

    experimentalRatioApproximation :
      Matter.MixingSignedRationalDatum

    experimentalRatioApproximationIsOneFiveHundred :
      experimentalRatioApproximation
      ≡
      Matter.oneFiveHundredMixingSignedRationalDatum

    alphaEstimateLabel :
      String

    alphaEstimateDerivedFromFermionMasses :
      Bool

    alphaEstimateDerivedFromFermionMassesIsTrue :
      alphaEstimateDerivedFromFermionMasses ≡ true

    alphaTargetRequired :
      Bool

    alphaTargetRequiredIsTrue :
      alphaTargetRequired ≡ true

    alphaTargetValueSupplied :
      Bool

    alphaTargetValueSuppliedIsTrue :
      alphaTargetValueSupplied ≡ true

    alphaBoundRequired :
      Bool

    alphaBoundRequiredIsTrue :
      alphaBoundRequired ≡ true

    alphaBoundSupplied :
      Bool

    alphaBoundSuppliedIsFalse :
      alphaBoundSupplied ≡ false

    numeratorDiagonalEntry :
      Matter.MixingGaussianRationalDatum

    denominatorDiagonalEntry :
      Matter.MixingGaussianRationalDatum

    numeratorFormulaEntry :
      Matter.MixingGaussianRationalDatum

    denominatorFormulaEntry :
      Matter.MixingGaussianRationalDatum

    numeratorEntryMatchesFormulaSurface :
      numeratorDiagonalEntry ≡ numeratorFormulaEntry

    denominatorEntryMatchesFormulaSurface :
      denominatorDiagonalEntry ≡ denominatorFormulaEntry

    carrierDiagonalEntriesBound :
      Bool

    carrierDiagonalEntriesBoundIsTrue :
      carrierDiagonalEntriesBound ≡ true

    physicalValuePromotion :
      Bool

    physicalValuePromotionIsFalse :
      physicalValuePromotion ≡ false

    alphaRatioBoundary :
      List String

canonicalMuOverCharmAlphaRatioTargetBinding :
  CarrierDiagonalAlphaRatioTargetBinding
canonicalMuOverCharmAlphaRatioTargetBinding =
  record
    { ratioTarget =
        upOverCharmCarrierTarget
    ; ratioLane =
        upCarrierYukawaRatioLane
    ; ratioReadiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; ratioReadinessIsCarrierAvailable =
        refl
    ; ratioNumeratorMassLabel =
        "m_u"
    ; ratioDenominatorMassLabel =
        "m_c"
    ; numeratorCarrierDepthLabel =
        "d2"
    ; denominatorCarrierDepthLabel =
        "d3"
    ; numeratorCarrierDepthSlot =
        0
    ; denominatorCarrierDepthSlot =
        1
    ; carrierDepthSeparation =
        1
    ; carrierDepthSeparationRecorded =
        true
    ; carrierDepthSeparationRecordedIsTrue =
        refl
    ; alphaExponentFormula =
        "2(d3-d2)"
    ; alphaPowerFormula =
        "m_u/m_c = alpha^(2(d3-d2))"
    ; experimentalRatioApproximation =
        Matter.oneFiveHundredMixingSignedRationalDatum
    ; experimentalRatioApproximationIsOneFiveHundred =
        refl
    ; alphaEstimateLabel =
        "alpha ~= 0.041240 from sqrt(2.16MeV/1.27GeV)"
    ; alphaEstimateDerivedFromFermionMasses =
        true
    ; alphaEstimateDerivedFromFermionMassesIsTrue =
        refl
    ; alphaTargetRequired =
        true
    ; alphaTargetRequiredIsTrue =
        refl
    ; alphaTargetValueSupplied =
        true
    ; alphaTargetValueSuppliedIsTrue =
        refl
    ; alphaBoundRequired =
        true
    ; alphaBoundRequiredIsTrue =
        refl
    ; alphaBoundSupplied =
        false
    ; alphaBoundSuppliedIsFalse =
        refl
    ; numeratorDiagonalEntry =
        Matter.v11 YFC.canonicalUpYukawaMatrix
    ; denominatorDiagonalEntry =
        Matter.v22 YFC.canonicalUpYukawaMatrix
    ; numeratorFormulaEntry =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.firstGeneration
          YDHR.firstGeneration
    ; denominatorFormulaEntry =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.secondGeneration
          YDHR.secondGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; carrierDiagonalEntriesBound =
        true
    ; carrierDiagonalEntriesBoundIsTrue =
        refl
    ; physicalValuePromotion =
        false
    ; physicalValuePromotionIsFalse =
        refl
    ; alphaRatioBoundary =
        "The symbolic m_u/m_c carrier target is alpha^(2(d3-d2))"
        ∷ "The current carrier depth-slot separation for p2 to p3 is recorded as one"
        ∷ "Using m_u/m_c approximately 1/500 gives the alpha target estimate 45/1000"
        ∷ "The ratio is bound to the first and second diagonal entries of the canonical up carrier-Yukawa matrix"
        ∷ "The alpha estimate is supplied as a target value, but no accepted error bound or physical calibration is promoted"
        ∷ "Physical-value promotion is explicitly false"
        ∷ []
    }

canonicalCharmOverTopAlphaRatioTargetBinding :
  CarrierDiagonalAlphaRatioTargetBinding
canonicalCharmOverTopAlphaRatioTargetBinding =
  record
    { ratioTarget =
        charmOverTopCarrierTarget
    ; ratioLane =
        upCarrierYukawaRatioLane
    ; ratioReadiness =
        carrierEntriesAvailablePhysicalPromotionBlocked
    ; ratioReadinessIsCarrierAvailable =
        refl
    ; ratioNumeratorMassLabel =
        "m_c"
    ; ratioDenominatorMassLabel =
        "m_t"
    ; numeratorCarrierDepthLabel =
        "d3"
    ; denominatorCarrierDepthLabel =
        "d5"
    ; numeratorCarrierDepthSlot =
        1
    ; denominatorCarrierDepthSlot =
        3
    ; carrierDepthSeparation =
        1
    ; carrierDepthSeparationRecorded =
        true
    ; carrierDepthSeparationRecordedIsTrue =
        refl
    ; alphaExponentFormula =
        "2(d5-d3)"
    ; alphaPowerFormula =
        "m_c/m_t = alpha^(2(d5-d3))"
    ; experimentalRatioApproximation =
        Matter.oneFiveHundredMixingSignedRationalDatum
    ; experimentalRatioApproximationIsOneFiveHundred =
        refl
    ; alphaEstimateLabel =
        "alpha ~= 0.085720 from sqrt(1.27GeV/172.76GeV)"
    ; alphaEstimateDerivedFromFermionMasses =
        true
    ; alphaEstimateDerivedFromFermionMassesIsTrue =
        refl
    ; alphaTargetRequired =
        true
    ; alphaTargetRequiredIsTrue =
        refl
    ; alphaTargetValueSupplied =
        true
    ; alphaTargetValueSuppliedIsTrue =
        refl
    ; alphaBoundRequired =
        true
    ; alphaBoundRequiredIsTrue =
        refl
    ; alphaBoundSupplied =
        false
    ; alphaBoundSuppliedIsFalse =
        refl
    ; numeratorDiagonalEntry =
        Matter.v22 YFC.canonicalUpYukawaMatrix
    ; denominatorDiagonalEntry =
        Matter.v33 YFC.canonicalUpYukawaMatrix
    ; numeratorFormulaEntry =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.secondGeneration
          YDHR.secondGeneration
    ; denominatorFormulaEntry =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.thirdGeneration
          YDHR.thirdGeneration
    ; numeratorEntryMatchesFormulaSurface =
        refl
    ; denominatorEntryMatchesFormulaSurface =
        refl
    ; carrierDiagonalEntriesBound =
        true
    ; carrierDiagonalEntriesBoundIsTrue =
        refl
    ; physicalValuePromotion =
        false
    ; physicalValuePromotionIsFalse =
        refl
    ; alphaRatioBoundary =
        "The symbolic m_c/m_t carrier target uses the p3-p5 carrier-dimension separation 1"
        ∷ "The current finite DHR/SM ledger readback records p3 to p5 as separation one"
        ∷ "Using m_c/m_t approximately 1.27GeV/172.76GeV gives the diagnostic alpha estimate 0.085720"
        ∷ "The ratio is bound to the second and third diagonal entries of the canonical up carrier-Yukawa matrix"
        ∷ "The two adjacent-generation ratio targets do not yet pass a common-alpha consistency check under prime-depth readback"
        ∷ "No accepted alpha error bound or physical calibration is promoted"
        ∷ "Physical-value promotion is explicitly false"
        ∷ []
    }

record PrimeLaneDepthSeparationReceipt : Set where
  field
    p2Depth :
      Nat

    p2DepthIsOne :
      p2Depth ≡ 1

    p3Depth :
      Nat

    p3DepthIsTwo :
      p3Depth ≡ 2

    p5Depth :
      Nat

    p5DepthIsThree :
      p5Depth ≡ 3

    p2p3DepthSeparation :
      Nat

    p2p3DepthSeparationIsOne :
      p2p3DepthSeparation ≡ 1

    p3p5DepthSeparation :
      Nat

    p3p5DepthSeparationIsOne :
      p3p5DepthSeparation ≡ 1

    separationsArePrimeLaneDepths :
      Bool

    separationsArePrimeLaneDepthsIsTrue :
      separationsArePrimeLaneDepths ≡ true

    separationBoundary :
      List String

open PrimeLaneDepthSeparationReceipt public

canonicalPrimeLaneDepthSeparationReceipt :
  PrimeLaneDepthSeparationReceipt
canonicalPrimeLaneDepthSeparationReceipt =
  record
    { p2Depth =
        1
    ; p2DepthIsOne =
        refl
    ; p3Depth =
        2
    ; p3DepthIsTwo =
        refl
    ; p5Depth =
        3
    ; p5DepthIsThree =
        refl
    ; p2p3DepthSeparation =
        1
    ; p2p3DepthSeparationIsOne =
        refl
    ; p3p5DepthSeparation =
        1
    ; p3p5DepthSeparationIsOne =
        refl
    ; separationsArePrimeLaneDepths =
        true
    ; separationsArePrimeLaneDepthsIsTrue =
        refl
    ; separationBoundary =
        "p2, p3, and p5 are read back as finite DHR/SM carrier dimensions 1, 2, and 3"
        ∷ "The p2-p3 absolute depth separation is 1"
        ∷ "The p3-p5 absolute depth separation is 1"
        ∷ []
    }

record AlphaFromFermionMassRatioEstimateReceipt : Setω where
  field
    depthSeparations :
      PrimeLaneDepthSeparationReceipt

    p2p3Separation :
      Nat

    p2p3SeparationMatchesDepthReceipt :
      p2p3Separation
      ≡
      PrimeLaneDepthSeparationReceipt.p2p3DepthSeparation
        depthSeparations

    p3p5Separation :
      Nat

    p3p5SeparationMatchesDepthReceipt :
      p3p5Separation
      ≡
      PrimeLaneDepthSeparationReceipt.p3p5DepthSeparation
        depthSeparations

    upMassNumeratorMeVScaled :
      Nat

    upMassNumeratorMeVScaledIsCanonical :
      upMassNumeratorMeVScaled ≡ 216

    charmMassForUpRatioMeVScaled :
      Nat

    charmMassForUpRatioMeVScaledIsCanonical :
      charmMassForUpRatioMeVScaled ≡ 127000

    charmMassNumeratorMeVScaled :
      Nat

    charmMassNumeratorMeVScaledIsCanonical :
      charmMassNumeratorMeVScaled ≡ 1270

    topMassDenominatorMeVScaled :
      Nat

    topMassDenominatorMeVScaledIsCanonical :
      topMassDenominatorMeVScaled ≡ 172760

    upOverCharmRatioLabel :
      String

    upOverCharmRatioLabelIsCanonical :
      upOverCharmRatioLabel ≡ "m_u/m_c ~= 2.16MeV/1.27GeV"

    charmOverTopRatioLabel :
      String

    charmOverTopRatioLabelIsCanonical :
      charmOverTopRatioLabel ≡ "m_c/m_t ~= 1.27GeV/172.76GeV"

    alphaFromUpOverCharmPartsPerMillion :
      Nat

    alphaFromUpOverCharmPartsPerMillionIsCanonicalEstimate :
      alphaFromUpOverCharmPartsPerMillion ≡ 41240

    alphaFromCharmOverTopPartsPerMillion :
      Nat

    alphaFromCharmOverTopPartsPerMillionIsCanonicalEstimate :
      alphaFromCharmOverTopPartsPerMillion ≡ 85720

    upOverCharmAlphaFormula :
      String

    upOverCharmAlphaFormulaIsCanonical :
      upOverCharmAlphaFormula
      ≡
      "alpha ~= sqrt(m_u/m_c) from p2-p3 separation 1"

    charmOverTopAlphaFormula :
      String

    charmOverTopAlphaFormulaIsCanonical :
      charmOverTopAlphaFormula
      ≡
      "alpha ~= sqrt(m_c/m_t) from p3-p5 separation 1"

    derivedFromFermionMasses :
      Bool

    derivedFromFermionMassesIsTrue :
      derivedFromFermionMasses ≡ true

    alphaEstimatesAgree :
      Bool

    alphaEstimatesAgreeIsFalse :
      alphaEstimatesAgree ≡ false

    acceptedAlphaTargetPromoted :
      Bool

    acceptedAlphaTargetPromotedIsFalse :
      acceptedAlphaTargetPromoted ≡ false

    physicalPromotion :
      Bool

    physicalPromotionIsFalse :
      physicalPromotion ≡ false

    estimateBoundary :
      List String

open AlphaFromFermionMassRatioEstimateReceipt public

canonicalAlphaFromFermionMassRatioEstimateReceipt :
  AlphaFromFermionMassRatioEstimateReceipt
canonicalAlphaFromFermionMassRatioEstimateReceipt =
  record
    { depthSeparations =
        canonicalPrimeLaneDepthSeparationReceipt
    ; p2p3Separation =
        1
    ; p2p3SeparationMatchesDepthReceipt =
        refl
    ; p3p5Separation =
        1
    ; p3p5SeparationMatchesDepthReceipt =
        refl
    ; upMassNumeratorMeVScaled =
        216
    ; upMassNumeratorMeVScaledIsCanonical =
        refl
    ; charmMassForUpRatioMeVScaled =
        127000
    ; charmMassForUpRatioMeVScaledIsCanonical =
        refl
    ; charmMassNumeratorMeVScaled =
        1270
    ; charmMassNumeratorMeVScaledIsCanonical =
        refl
    ; topMassDenominatorMeVScaled =
        172760
    ; topMassDenominatorMeVScaledIsCanonical =
        refl
    ; upOverCharmRatioLabel =
        "m_u/m_c ~= 2.16MeV/1.27GeV"
    ; upOverCharmRatioLabelIsCanonical =
        refl
    ; charmOverTopRatioLabel =
        "m_c/m_t ~= 1.27GeV/172.76GeV"
    ; charmOverTopRatioLabelIsCanonical =
        refl
    ; alphaFromUpOverCharmPartsPerMillion =
        41240
    ; alphaFromUpOverCharmPartsPerMillionIsCanonicalEstimate =
        refl
    ; alphaFromCharmOverTopPartsPerMillion =
        85720
    ; alphaFromCharmOverTopPartsPerMillionIsCanonicalEstimate =
        refl
    ; upOverCharmAlphaFormula =
        "alpha ~= sqrt(m_u/m_c) from p2-p3 separation 1"
    ; upOverCharmAlphaFormulaIsCanonical =
        refl
    ; charmOverTopAlphaFormula =
        "alpha ~= sqrt(m_c/m_t) from p3-p5 separation 1"
    ; charmOverTopAlphaFormulaIsCanonical =
        refl
    ; derivedFromFermionMasses =
        true
    ; derivedFromFermionMassesIsTrue =
        refl
    ; alphaEstimatesAgree =
        false
    ; alphaEstimatesAgreeIsFalse =
        refl
    ; acceptedAlphaTargetPromoted =
        false
    ; acceptedAlphaTargetPromotedIsFalse =
        refl
    ; physicalPromotion =
        false
    ; physicalPromotionIsFalse =
        refl
    ; estimateBoundary =
        "The p2-p3 carrier-dimension separation is 1, so the m_u/m_c readback estimates alpha by a square root"
        ∷ "The p3-p5 carrier-dimension separation is 1, so the m_c/m_t readback estimates alpha by a square root"
        ∷ "The two finite readback estimates are recorded as 0.041240 and 0.085720, so they are evidence diagnostics rather than an accepted common alpha"
        ∷ "derivedFromFermionMasses is true for this readback receipt, while accepted-alpha and physical-promotion flags remain false"
        ∷ []
    }

record MissingCarrierYukawaRatioBinding : Set where
  field
    target :
      CarrierYukawaRatioTarget

    lane :
      CarrierYukawaRatioLane

    readiness :
      CarrierYukawaRatioReadiness

    readinessIsChargedLeptonMissing :
      readiness ≡ chargedLeptonCarrierMissing

    missingBlocker :
      CarrierYukawaRatioBlocker

    missingBlockerIsChargedLeptonYukawaCarrier :
      missingBlocker ≡ missingChargedLeptonYukawaCarrier

    chargedLeptonMatterRepresentationAvailable :
      Bool

    chargedLeptonMatterRepresentationAvailableIsTrue :
      chargedLeptonMatterRepresentationAvailable ≡ true

    chargedLeptonYukawaCarrierConstructed :
      Bool

    chargedLeptonYukawaCarrierConstructedIsFalse :
      chargedLeptonYukawaCarrierConstructed ≡ false

    physicalRatioPromoted :
      Bool

    physicalRatioPromotedIsFalse :
      physicalRatioPromoted ≡ false

    missingBoundary :
      List String

open MissingCarrierYukawaRatioBinding public

canonicalElectronOverMuonCarrierRatioTarget :
  MissingCarrierYukawaRatioBinding
canonicalElectronOverMuonCarrierRatioTarget =
  record
    { target =
        electronOverMuonCarrierTarget
    ; lane =
        chargedLeptonCarrierYukawaRatioLane
    ; readiness =
        chargedLeptonCarrierMissing
    ; readinessIsChargedLeptonMissing =
        refl
    ; missingBlocker =
        missingChargedLeptonYukawaCarrier
    ; missingBlockerIsChargedLeptonYukawaCarrier =
        refl
    ; chargedLeptonMatterRepresentationAvailable =
        true
    ; chargedLeptonMatterRepresentationAvailableIsTrue =
        refl
    ; chargedLeptonYukawaCarrierConstructed =
        false
    ; chargedLeptonYukawaCarrierConstructedIsFalse =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; missingBoundary =
        "e/mu is named as a charged-lepton carrier-Yukawa ratio target"
        ∷ "MatterRepresentationReceiptSurface supplies charged-lepton representation primitives, but no charged-lepton Yukawa carrier matrix exists here"
        ∷ "No electron/muon numeric ratio is inferred from quark carrier data"
        ∷ []
    }

canonicalMuonOverTauCarrierRatioTarget :
  MissingCarrierYukawaRatioBinding
canonicalMuonOverTauCarrierRatioTarget =
  record
    { target =
        muonOverTauCarrierTarget
    ; lane =
        chargedLeptonCarrierYukawaRatioLane
    ; readiness =
        chargedLeptonCarrierMissing
    ; readinessIsChargedLeptonMissing =
        refl
    ; missingBlocker =
        missingChargedLeptonYukawaCarrier
    ; missingBlockerIsChargedLeptonYukawaCarrier =
        refl
    ; chargedLeptonMatterRepresentationAvailable =
        true
    ; chargedLeptonMatterRepresentationAvailableIsTrue =
        refl
    ; chargedLeptonYukawaCarrierConstructed =
        false
    ; chargedLeptonYukawaCarrierConstructedIsFalse =
        refl
    ; physicalRatioPromoted =
        false
    ; physicalRatioPromotedIsFalse =
        refl
    ; missingBoundary =
        "mu/tau is named as a charged-lepton carrier-Yukawa ratio target"
        ∷ "MatterRepresentationReceiptSurface supplies charged-lepton representation primitives, but no charged-lepton Yukawa carrier matrix exists here"
        ∷ "No muon/tau numeric ratio is inferred from quark carrier data"
        ∷ []
    }

record CarrierYukawaRatioTargetReceipt : Setω where
  field
    yukawaFromCarrierReceipt :
      YFC.YukawaFromCarrierReceipt

    yukawaDHRIntertwinerCompatibilityReceipt :
      YDHR.YukawaDHRIntertwinerCompatibilityReceipt

    matterRatioFormReceipt :
      Matter.YukawaSectorRatioFormPromotionReceipt

    ckmCarrierMixingDependencies :
      List CKMMix.CKMCarrierMixingDependency

    ckmCarrierMixingDependenciesAreCanonical :
      ckmCarrierMixingDependencies
      ≡
      CKMMix.canonicalCKMCarrierMixingDependencies

    targetLanes :
      List CarrierYukawaRatioLane

    targetLanesAreCanonical :
      targetLanes ≡ canonicalCarrierYukawaRatioLanes

    ratioTargets :
      List CarrierYukawaRatioTarget

    ratioTargetsAreCanonical :
      ratioTargets ≡ canonicalCarrierYukawaRatioTargets

    upOverCharmBinding :
      ExistingCarrierYukawaRatioBinding

    upOverTopBinding :
      ExistingCarrierYukawaRatioBinding

    charmOverTopBinding :
      ExistingCarrierYukawaRatioBinding

    downOverBottomBinding :
      ExistingCarrierYukawaRatioBinding

    strangeOverBottomBinding :
      ExistingCarrierYukawaRatioBinding

    electronOverMuonTarget :
      MissingCarrierYukawaRatioBinding

    muonOverTauTarget :
      MissingCarrierYukawaRatioBinding

    muOverCharmAlphaRatioTarget :
      CarrierDiagonalAlphaRatioTargetBinding

    charmOverTopAlphaRatioTarget :
      CarrierDiagonalAlphaRatioTargetBinding

    primeLaneDepthSeparationReceipt :
      PrimeLaneDepthSeparationReceipt

    alphaFromFermionMassRatioEstimate :
      AlphaFromFermionMassRatioEstimateReceipt

    alphaEstimateDerivedFromFermionMasses :
      Bool

    alphaEstimateDerivedFromFermionMassesIsTrue :
      alphaEstimateDerivedFromFermionMasses ≡ true

    alphaEstimatePhysicalPromotion :
      Bool

    alphaEstimatePhysicalPromotionIsFalse :
      alphaEstimatePhysicalPromotion ≡ false

    alphaTargetRequiredForCarrierMassRatios :
      Bool

    alphaTargetRequiredForCarrierMassRatiosIsTrue :
      alphaTargetRequiredForCarrierMassRatios ≡ true

    alphaTargetValueSuppliedForCarrierMassRatios :
      Bool

    alphaTargetValueSuppliedForCarrierMassRatiosIsFalse :
      alphaTargetValueSuppliedForCarrierMassRatios ≡ false

    alphaBoundRequiredForCarrierMassRatios :
      Bool

    alphaBoundRequiredForCarrierMassRatiosIsTrue :
      alphaBoundRequiredForCarrierMassRatios ≡ true

    alphaBoundSuppliedForCarrierMassRatios :
      Bool

    alphaBoundSuppliedForCarrierMassRatiosIsFalse :
      alphaBoundSuppliedForCarrierMassRatios ≡ false

    physicalValuePromotionFromAlphaRatioTargets :
      Bool

    physicalValuePromotionFromAlphaRatioTargetsIsFalse :
      physicalValuePromotionFromAlphaRatioTargets ≡ false

    exactUpYukawa3x3 :
      Exact.DiagonalYukawa3x3

    exactUpYukawa3x3IsCanonical :
      exactUpYukawa3x3 ≡ Exact.canonicalUpYukawa3x3

    exactDownYukawa3x3 :
      Exact.DiagonalYukawa3x3

    exactDownYukawa3x3IsCanonical :
      exactDownYukawa3x3 ≡ Exact.canonicalDownYukawa3x3

    yukawaCarrierBlockers :
      List YFC.YukawaCarrierFailClosedBlocker

    yukawaCarrierBlockersAreThreaded :
      yukawaCarrierBlockers
      ≡
      YFC.failClosedBlockers yukawaFromCarrierReceipt

    yukawaDHRCompatibilityBlockers :
      List YDHR.YukawaDHRCompatibilityBlocker

    yukawaDHRCompatibilityBlockersAreThreaded :
      yukawaDHRCompatibilityBlockers
      ≡
      YDHR.compatibilityBlockers yukawaDHRIntertwinerCompatibilityReceipt

    ratioBlockers :
      List CarrierYukawaRatioBlocker

    ratioBlockersAreCanonical :
      ratioBlockers ≡ canonicalCarrierYukawaRatioBlockers

    physicalFermionMassReceiptsConstructed :
      Bool

    physicalFermionMassReceiptsConstructedMatchesDHR :
      physicalFermionMassReceiptsConstructed
      ≡
      YDHR.physicalFermionMassReceiptsConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    physicalFermionMassReceiptsConstructedIsFalse :
      physicalFermionMassReceiptsConstructed ≡ false

    absoluteHiggsScaleW4CalibrationConstructed :
      Bool

    absoluteHiggsScaleW4CalibrationConstructedMatchesDHR :
      absoluteHiggsScaleW4CalibrationConstructed
      ≡
      YDHR.absoluteHiggsScaleW4CalibrationConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    absoluteHiggsScaleW4CalibrationConstructedIsFalse :
      absoluteHiggsScaleW4CalibrationConstructed ≡ false

    actualDHRSectorRepresentationsConstructed :
      Bool

    actualDHRSectorRepresentationsConstructedMatchesDHR :
      actualDHRSectorRepresentationsConstructed
      ≡
      YDHR.actualDHRSectorRepresentationsConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    actualDHRSectorRepresentationsConstructedIsFalse :
      actualDHRSectorRepresentationsConstructed ≡ false

    physicalYukawaMatricesSupplied :
      Bool

    physicalYukawaMatricesSuppliedMatchesDHR :
      physicalYukawaMatricesSupplied
      ≡
      YDHR.physicalYukawaMatricesSupplied
        yukawaDHRIntertwinerCompatibilityReceipt

    physicalYukawaMatricesSuppliedIsFalse :
      physicalYukawaMatricesSupplied ≡ false

    physicalRatioPredictionsPromoted :
      Bool

    physicalRatioPredictionsPromotedIsFalse :
      physicalRatioPredictionsPromoted ≡ false

    receiptBoundary :
      List String

open CarrierYukawaRatioTargetReceipt public

canonicalCarrierYukawaRatioTargetReceipt :
  CarrierYukawaRatioTargetReceipt
canonicalCarrierYukawaRatioTargetReceipt =
  record
    { yukawaFromCarrierReceipt =
        YFC.canonicalYukawaFromCarrier
    ; yukawaDHRIntertwinerCompatibilityReceipt =
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; matterRatioFormReceipt =
        Matter.canonicalYukawaSectorRatioFormPromotionReceipt
    ; ckmCarrierMixingDependencies =
        CKMMix.canonicalCKMCarrierMixingDependencies
    ; ckmCarrierMixingDependenciesAreCanonical =
        refl
    ; targetLanes =
        canonicalCarrierYukawaRatioLanes
    ; targetLanesAreCanonical =
        refl
    ; ratioTargets =
        canonicalCarrierYukawaRatioTargets
    ; ratioTargetsAreCanonical =
        refl
    ; upOverCharmBinding =
        canonicalUpOverCharmCarrierRatioBinding
    ; upOverTopBinding =
        canonicalUpOverTopCarrierRatioBinding
    ; charmOverTopBinding =
        canonicalCharmOverTopCarrierRatioBinding
    ; downOverBottomBinding =
        canonicalDownOverBottomCarrierRatioBinding
    ; strangeOverBottomBinding =
        canonicalStrangeOverBottomCarrierRatioBinding
    ; electronOverMuonTarget =
        canonicalElectronOverMuonCarrierRatioTarget
    ; muonOverTauTarget =
        canonicalMuonOverTauCarrierRatioTarget
    ; muOverCharmAlphaRatioTarget =
        canonicalMuOverCharmAlphaRatioTargetBinding
    ; charmOverTopAlphaRatioTarget =
        canonicalCharmOverTopAlphaRatioTargetBinding
    ; primeLaneDepthSeparationReceipt =
        canonicalPrimeLaneDepthSeparationReceipt
    ; alphaFromFermionMassRatioEstimate =
        canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaEstimateDerivedFromFermionMasses =
        derivedFromFermionMasses
          canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaEstimateDerivedFromFermionMassesIsTrue =
        derivedFromFermionMassesIsTrue
          canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaEstimatePhysicalPromotion =
        physicalPromotion
          canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaEstimatePhysicalPromotionIsFalse =
        physicalPromotionIsFalse
          canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaTargetRequiredForCarrierMassRatios =
        true
    ; alphaTargetRequiredForCarrierMassRatiosIsTrue =
        refl
    ; alphaTargetValueSuppliedForCarrierMassRatios =
        false
    ; alphaTargetValueSuppliedForCarrierMassRatiosIsFalse =
        refl
    ; alphaBoundRequiredForCarrierMassRatios =
        true
    ; alphaBoundRequiredForCarrierMassRatiosIsTrue =
        refl
    ; alphaBoundSuppliedForCarrierMassRatios =
        false
    ; alphaBoundSuppliedForCarrierMassRatiosIsFalse =
        refl
    ; physicalValuePromotionFromAlphaRatioTargets =
        false
    ; physicalValuePromotionFromAlphaRatioTargetsIsFalse =
        refl
    ; exactUpYukawa3x3 =
        Exact.canonicalUpYukawa3x3
    ; exactUpYukawa3x3IsCanonical =
        refl
    ; exactDownYukawa3x3 =
        Exact.canonicalDownYukawa3x3
    ; exactDownYukawa3x3IsCanonical =
        refl
    ; yukawaCarrierBlockers =
        YFC.failClosedBlockers YFC.canonicalYukawaFromCarrier
    ; yukawaCarrierBlockersAreThreaded =
        refl
    ; yukawaDHRCompatibilityBlockers =
        YDHR.compatibilityBlockers
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; yukawaDHRCompatibilityBlockersAreThreaded =
        refl
    ; ratioBlockers =
        canonicalCarrierYukawaRatioBlockers
    ; ratioBlockersAreCanonical =
        refl
    ; physicalFermionMassReceiptsConstructed =
        YDHR.physicalFermionMassReceiptsConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; physicalFermionMassReceiptsConstructedMatchesDHR =
        refl
    ; physicalFermionMassReceiptsConstructedIsFalse =
        refl
    ; absoluteHiggsScaleW4CalibrationConstructed =
        YDHR.absoluteHiggsScaleW4CalibrationConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; absoluteHiggsScaleW4CalibrationConstructedMatchesDHR =
        refl
    ; absoluteHiggsScaleW4CalibrationConstructedIsFalse =
        refl
    ; actualDHRSectorRepresentationsConstructed =
        YDHR.actualDHRSectorRepresentationsConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; actualDHRSectorRepresentationsConstructedMatchesDHR =
        refl
    ; actualDHRSectorRepresentationsConstructedIsFalse =
        refl
    ; physicalYukawaMatricesSupplied =
        YDHR.physicalYukawaMatricesSupplied
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; physicalYukawaMatricesSuppliedMatchesDHR =
        refl
    ; physicalYukawaMatricesSuppliedIsFalse =
        refl
    ; physicalRatioPredictionsPromoted =
        false
    ; physicalRatioPredictionsPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Named carrier-Yukawa ratio targets are u/c, u/t, c/t, d/b, s/b, e/mu, and mu/tau"
        ∷ "The up/down targets are bound to existing canonical carrier-Yukawa diagonal entries and the DHR formula surface entries"
        ∷ "The alpha ratio targets are m_u/m_c = alpha^(2(d3-d2)) and m_c/m_t = alpha^(2(d5-d3))"
        ∷ "The alpha-from-fermion-mass readback records finite DHR/SM carrier-dimension separations p2-p3=1 and p3-p5=1, with diagnostic alpha estimates 0.041240 and 0.085720"
        ∷ "That readback has derivedFromFermionMasses=true but still keeps accepted-alpha and physical-promotion flags false"
        ∷ "Alpha target value and accepted alpha bound are required but absent, so alpha-ratio physical-value promotion is false"
        ∷ "The charged-lepton targets are named but blocked until a charged-lepton Yukawa carrier matrix exists"
        ∷ "The receipt threads YukawaFromCarrier, YukawaDHRIntertwinerCompatibility, MatterRepresentationReceiptSurface ratio-form targets, and CKM carrier-mixing dependencies"
        ∷ "Physical fermion mass receipts, running-scale and threshold convention, absolute Higgs/VEV/W4 calibration, actual DHR sector representations, and non-identity DHR intertwiners remain blockers"
        ∷ "No numeric physical mass-ratio prediction is promoted from the carrier entries"
        ∷ []
    }

canonicalCarrierYukawaRatioTargetsKeepPhysicalPromotionClosed :
  physicalRatioPredictionsPromoted canonicalCarrierYukawaRatioTargetReceipt
  ≡
  false
canonicalCarrierYukawaRatioTargetsKeepPhysicalPromotionClosed =
  refl

canonicalCarrierYukawaRatioTargetsThreadDHRMassBlocker :
  physicalFermionMassReceiptsConstructed canonicalCarrierYukawaRatioTargetReceipt
  ≡
  false
canonicalCarrierYukawaRatioTargetsThreadDHRMassBlocker =
  refl

canonicalElectronOverMuonCarrierStillMissing :
  chargedLeptonYukawaCarrierConstructed
    (electronOverMuonTarget canonicalCarrierYukawaRatioTargetReceipt)
  ≡
  false
canonicalElectronOverMuonCarrierStillMissing =
  refl

canonicalCarrierYukawaAlphaRatioTargetBoundStillMissing :
  alphaBoundSuppliedForCarrierMassRatios
    canonicalCarrierYukawaRatioTargetReceipt
  ≡
  false
canonicalCarrierYukawaAlphaRatioTargetBoundStillMissing =
  refl

canonicalCarrierYukawaAlphaRatioPhysicalPromotionClosed :
  physicalValuePromotionFromAlphaRatioTargets
    canonicalCarrierYukawaRatioTargetReceipt
  ≡
  false
canonicalCarrierYukawaAlphaRatioPhysicalPromotionClosed =
  refl
