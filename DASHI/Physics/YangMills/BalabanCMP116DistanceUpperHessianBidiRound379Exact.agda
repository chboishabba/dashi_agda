{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DistanceUpperHessianBidiRound379Exact where

------------------------------------------------------------------------
-- ROUND379 / DO NOT PROMOTE A HISTORICAL MARK TO A CONSUMER REQUIREMENT
--
-- R375's coefficient consumer does not inspect the semantic provenance of the
-- scalar named `markedInput`; it uses only:
--
--   0 <= U
--   selectedBoundaryDistance(s) <= U
--
-- to derive
--
--   ||Delta H_coeff|| <= L_Hessian * U.
--
-- Therefore the historical R351/R378 marked-input calibration is a valid
-- compatibility producer, but it is not mandatory for this consumer.  This
-- owner renames the actual least-privilege coordinate to `distanceUpper` and
-- compiles it into R375.  No equality with CMP99/CMP116 historical marks is
-- asserted or required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116HessianBidiBridgeRound375Exact as R375

record CMP116DistanceUpperHessianBidiData : Set₁ where
  field
    joint : R373.JointBoundaryHessianPaymentData

    distanceUpper : ℝ
    distanceUpperNonnegative : 0ℝ ≤ℝ distanceUpper

    selectedBoundaryDistanceNonnegative :
      ∀ s → 0ℝ ≤ℝ R373.selectedBoundarySubstitutionDistance joint s

    selectedLipschitzNonnegative :
      0ℝ ≤ℝ R373.selectedLipschitz joint

    selectedBoundaryDistanceBelowUpper :
      ∀ s →
      R373.selectedBoundarySubstitutionDistance joint s ≤ℝ distanceUpper

open CMP116DistanceUpperHessianBidiData public

asRound375 :
  CMP116DistanceUpperHessianBidiData →
  R375.CMP116HessianBidiBridgeData
asRound375 dataSet = record
  { joint = joint dataSet
  ; markedInput = distanceUpper dataSet
  ; selectedLipschitzNonnegative = selectedLipschitzNonnegative dataSet
  ; selectedBoundaryDistanceNonnegative =
      selectedBoundaryDistanceNonnegative dataSet
  ; markedInputNonnegative = distanceUpperNonnegative dataSet
  ; selectedBoundaryDistanceBelowMarkedInput =
      selectedBoundaryDistanceBelowUpper dataSet
  }

selectedCoefficientDifferenceBelowDistanceUpper :
  (dataSet : CMP116DistanceUpperHessianBidiData) →
  Cauchy.normValue
    (Decoupled.cauchy (R373.decoupled (joint dataSet)))
    (Cauchy._-Value_
      (Decoupled.cauchy (R373.decoupled (joint dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R373.decoupled (joint dataSet))
        (R373.leftDomain (joint dataSet))
        (R373.component (joint dataSet))
        (R373.leftVariation (joint dataSet))
        (R373.rightVariation (joint dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R373.decoupled (joint dataSet))
        (R373.rightDomain (joint dataSet))
        (R373.component (joint dataSet))
        (R373.leftVariation (joint dataSet))
        (R373.rightVariation (joint dataSet))))
  ≤ℝ
  R373.selectedLipschitz (joint dataSet) *ℝ distanceUpper dataSet
selectedCoefficientDifferenceBelowDistanceUpper dataSet =
  R375.selectedCoefficientDifferenceBound (asRound375 dataSet)

------------------------------------------------------------------------
-- Pareto / WrongType boundary.
------------------------------------------------------------------------

round379DistanceUpperCompilerLevel : ProofLevel
round379DistanceUpperCompilerLevel = machineChecked

historicalMarkedInputCalibrationMandatoryForCoefficientConsumer : Bool
historicalMarkedInputCalibrationMandatoryForCoefficientConsumer = false

historicalMarkedInputCalibrationMandatoryForCoefficientConsumerIsFalse :
  historicalMarkedInputCalibrationMandatoryForCoefficientConsumer ≡ false
historicalMarkedInputCalibrationMandatoryForCoefficientConsumerIsFalse = refl

proofBearingDistanceUpperStillRequired : Bool
proofBearingDistanceUpperStillRequired = true

proofBearingDistanceUpperStillRequiredIsTrue :
  proofBearingDistanceUpperStillRequired ≡ true
proofBearingDistanceUpperStillRequiredIsTrue = refl

historicalMarkIdentityManufacturedByRound379 : Bool
historicalMarkIdentityManufacturedByRound379 = false

historicalMarkIdentityManufacturedByRound379IsFalse :
  historicalMarkIdentityManufacturedByRound379 ≡ false
historicalMarkIdentityManufacturedByRound379IsFalse = refl

record Round379Boundary : Set where
  constructor round379-boundary
  field
    coefficientConsumerNeedsOnlyDistanceUpper : Bool
    coefficientConsumerNeedsOnlyDistanceUpperIsTrue :
      coefficientConsumerNeedsOnlyDistanceUpper ≡ true

    r378HistoricalMarkedCalibrationStillValidProducer : Bool
    r378HistoricalMarkedCalibrationStillValidProducerIsTrue :
      r378HistoricalMarkedCalibrationStillValidProducer ≡ true

    r378HistoricalMarkedCalibrationMandatoryHere : Bool
    r378HistoricalMarkedCalibrationMandatoryHereIsFalse :
      r378HistoricalMarkedCalibrationMandatoryHere ≡ false

    sameObjectSelectedDistanceAttachmentStillRequired : Bool
    sameObjectSelectedDistanceAttachmentStillRequiredIsTrue :
      sameObjectSelectedDistanceAttachmentStillRequired ≡ true

canonicalRound379Boundary : Round379Boundary
canonicalRound379Boundary =
  round379-boundary true refl true refl false refl true refl

round379FrontierRefinementLevel : ProofLevel
round379FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
