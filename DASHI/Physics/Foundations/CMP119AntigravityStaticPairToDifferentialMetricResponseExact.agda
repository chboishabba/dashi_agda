{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityStaticPairToDifferentialMetricResponseExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)

import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Static
import DASHI.Physics.Foundations.CMP119AntigravityDifferentialMetricResponseFirewallExact as Differential

------------------------------------------------------------------------
-- TWO STATIC PROMOTIONS + ONE COMMON AFFINE CALIBRATION -> DIFFERENTIAL
--
-- Two endpoint static receipts alone do not identify Delta-Lambda.  The extra
-- physical payment is one SHARED calibration/convention for the pair:
--
--   Lambda_off = a V_off + c
--   Lambda_on  = a V_on  + c.
--
-- Once that shared affine relation and common cosmological renormalization
-- convention are paid, the differential compiler derives
--
--   Delta Lambda = a (V_on - V_off)
--
-- and no second independent Delta-object theorem is needed.
------------------------------------------------------------------------

record CommonRenormalizedVacuumPair : Set₁ where
  field
    sourceOff : ℚ
    sourceOn : ℚ

    off : Static.VacuumNormalizationToGravityReceipt sourceOff
    on : Static.VacuumNormalizationToGravityReceipt sourceOn

    normalizationToGravityScale : ℚ
    commonAdditiveGravityRenormalization : ℚ

    offAmplitudeUsesCommonAffineCalibration :
      Static.renormalizedGravitationalAmplitude off
      ≡ normalizationToGravityScale * sourceOff
        + commonAdditiveGravityRenormalization

    onAmplitudeUsesCommonAffineCalibration :
      Static.renormalizedGravitationalAmplitude on
      ≡ normalizationToGravityScale * sourceOn
        + commonAdditiveGravityRenormalization

    CommonRenormalizationConvention : Set
    commonRenormalizationConvention : CommonRenormalizationConvention

    OffUsesCommonRenormalizationConvention : Set
    offUsesCommonRenormalizationConvention :
      OffUsesCommonRenormalizationConvention

    OnUsesCommonRenormalizationConvention : Set
    onUsesCommonRenormalizationConvention :
      OnUsesCommonRenormalizationConvention

open CommonRenormalizedVacuumPair public

staticPairToDifferentialMetricResponse :
  CommonRenormalizedVacuumPair →
  Differential.DifferentialMetricResponseReceipt
staticPairToDifferentialMetricResponse pair = record
  { Differential.DifferentialMetricResponseReceipt.normalizationOff = sourceOff pair
  ; Differential.DifferentialMetricResponseReceipt.normalizationOn = sourceOn pair
  ; Differential.DifferentialMetricResponseReceipt.normalizationToGravityScale =
      normalizationToGravityScale pair
  ; Differential.DifferentialMetricResponseReceipt.commonAdditiveGravityRenormalization =
      commonAdditiveGravityRenormalization pair
  ; Differential.DifferentialMetricResponseReceipt.physicalLambdaOff =
      Static.renormalizedGravitationalAmplitude (off pair)
  ; Differential.DifferentialMetricResponseReceipt.physicalLambdaOn =
      Static.renormalizedGravitationalAmplitude (on pair)
  ; Differential.DifferentialMetricResponseReceipt.offAffineCalibration =
      offAmplitudeUsesCommonAffineCalibration pair
  ; Differential.DifferentialMetricResponseReceipt.onAffineCalibration =
      onAmplitudeUsesCommonAffineCalibration pair
  ; Differential.DifferentialMetricResponseReceipt.OffMetricResponseSameStateReceipt =
      Static.SameStateMetricVolumeReceipt (off pair)
  ; Differential.DifferentialMetricResponseReceipt.offMetricResponseSameStateReceipt =
      Static.sameStateMetricVolumeReceipt (off pair)
  ; Differential.DifferentialMetricResponseReceipt.OnMetricResponseSameStateReceipt =
      Static.SameStateMetricVolumeReceipt (on pair)
  ; Differential.DifferentialMetricResponseReceipt.onMetricResponseSameStateReceipt =
      Static.sameStateMetricVolumeReceipt (on pair)
  ; Differential.DifferentialMetricResponseReceipt.CommonCosmologicalRenormalizationConditionReceipt =
      CommonRenormalizationConvention pair
  ; Differential.DifferentialMetricResponseReceipt.commonCosmologicalRenormalizationConditionReceipt =
      commonRenormalizationConvention pair
  }

normalizationDifferenceMatchesMetricResponseDifference :
  (pair : CommonRenormalizedVacuumPair) →
  Differential.physicalDeltaLambda
    (staticPairToDifferentialMetricResponse pair)
  ≡ normalizationToGravityScale pair * (sourceOn pair - sourceOff pair)
normalizationDifferenceMatchesMetricResponseDifference pair =
  Differential.normalizationDifferenceMatchesMetricResponseDifference
    (staticPairToDifferentialMetricResponse pair)

independentDifferentialSameObjectTheoremRequiredAfterTwoStaticReceipts : Bool
independentDifferentialSameObjectTheoremRequiredAfterTwoStaticReceipts = true

independentDifferentialSameObjectTheoremRequiredAfterCommonAffinePair : Bool
independentDifferentialSameObjectTheoremRequiredAfterCommonAffinePair = false

commonAffineCalibrationRequired : Bool
commonAffineCalibrationRequired = true

commonRenormalizationConventionRequired : Bool
commonRenormalizationConventionRequired = true

staticPairToDifferentialCompilerOwned : Bool
staticPairToDifferentialCompilerOwned = true
