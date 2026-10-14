{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityR136StaticPairToDifferentialExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)

import DASHI.Physics.Foundations.CMP119AntigravityR136ToStaticVacuumPromotionExact as R136Static
import DASHI.Physics.Foundations.CMP119AntigravityStaticPairToDifferentialMetricResponseExact as StaticPair
import DASHI.Physics.Foundations.CMP119AntigravityDifferentialMetricResponseFirewallExact as Differential
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Lorentz

------------------------------------------------------------------------
-- TWO R136/LOCAL-C VACUUM ENDPOINTS -> DIFFERENTIAL METRIC RESPONSE
--
-- If OFF and ON have each paid the same-state R136/Local-C vacuum promotion,
-- and both use ONE shared affine normalization/gravity calibration and ONE
-- common cosmological renormalization convention, no independent Delta-object
-- same-object theorem remains.
------------------------------------------------------------------------

record CommonR136AffineVacuumPair : Set₁ where
  field
    sourceOff : ℚ
    sourceOn : ℚ

    vacuumOff : Lorentz.VacuumLikeLorentzianStress
    vacuumOn : Lorentz.VacuumLikeLorentzianStress

    normalizationToGravityScale : ℚ
    commonAdditiveGravityRenormalization : ℚ

    offRhoUsesCommonAffineCalibration :
      Lorentz.rho (Lorentz.stress vacuumOff)
      ≡ normalizationToGravityScale * sourceOff
        + commonAdditiveGravityRenormalization

    onRhoUsesCommonAffineCalibration :
      Lorentz.rho (Lorentz.stress vacuumOn)
      ≡ normalizationToGravityScale * sourceOn
        + commonAdditiveGravityRenormalization

    OffR136LocalCSameStateReceipt : Set
    offR136LocalCSameStateReceipt : OffR136LocalCSameStateReceipt

    OnR136LocalCSameStateReceipt : Set
    onR136LocalCSameStateReceipt : OnR136LocalCSameStateReceipt

    CommonCosmologicalRenormalizationCondition : Set
    commonCosmologicalRenormalizationCondition :
      CommonCosmologicalRenormalizationCondition

open CommonR136AffineVacuumPair public

offPromotion :
  (pair : CommonR136AffineVacuumPair) →
  R136Static.R136StaticVacuumPromotionInput (sourceOff pair)
offPromotion pair = record
  { R136Static.R136StaticVacuumPromotionInput.lorentzianVacuum =
      vacuumOff pair
  ; R136Static.R136StaticVacuumPromotionInput.normalizationToGravityScale =
      normalizationToGravityScale pair
  ; R136Static.R136StaticVacuumPromotionInput.additiveGravityRenormalization =
      commonAdditiveGravityRenormalization pair
  ; R136Static.R136StaticVacuumPromotionInput.vacuumRhoUsesAffineCalibration =
      offRhoUsesCommonAffineCalibration pair
  ; R136Static.R136StaticVacuumPromotionInput.R136LocalCSameStateMetricResponseReceipt =
      OffR136LocalCSameStateReceipt pair
  ; R136Static.R136StaticVacuumPromotionInput.r136LocalCSameStateMetricResponseReceipt =
      offR136LocalCSameStateReceipt pair
  ; R136Static.R136StaticVacuumPromotionInput.CosmologicalRenormalizationCondition =
      CommonCosmologicalRenormalizationCondition pair
  ; R136Static.R136StaticVacuumPromotionInput.cosmologicalRenormalizationCondition =
      commonCosmologicalRenormalizationCondition pair
  }

onPromotion :
  (pair : CommonR136AffineVacuumPair) →
  R136Static.R136StaticVacuumPromotionInput (sourceOn pair)
onPromotion pair = record
  { R136Static.R136StaticVacuumPromotionInput.lorentzianVacuum =
      vacuumOn pair
  ; R136Static.R136StaticVacuumPromotionInput.normalizationToGravityScale =
      normalizationToGravityScale pair
  ; R136Static.R136StaticVacuumPromotionInput.additiveGravityRenormalization =
      commonAdditiveGravityRenormalization pair
  ; R136Static.R136StaticVacuumPromotionInput.vacuumRhoUsesAffineCalibration =
      onRhoUsesCommonAffineCalibration pair
  ; R136Static.R136StaticVacuumPromotionInput.R136LocalCSameStateMetricResponseReceipt =
      OnR136LocalCSameStateReceipt pair
  ; R136Static.R136StaticVacuumPromotionInput.r136LocalCSameStateMetricResponseReceipt =
      onR136LocalCSameStateReceipt pair
  ; R136Static.R136StaticVacuumPromotionInput.CosmologicalRenormalizationCondition =
      CommonCosmologicalRenormalizationCondition pair
  ; R136Static.R136StaticVacuumPromotionInput.cosmologicalRenormalizationCondition =
      commonCosmologicalRenormalizationCondition pair
  }

asCommonStaticPair :
  CommonR136AffineVacuumPair →
  StaticPair.CommonRenormalizedVacuumPair
asCommonStaticPair pair = record
  { StaticPair.CommonRenormalizedVacuumPair.sourceOff = sourceOff pair
  ; StaticPair.CommonRenormalizedVacuumPair.sourceOn = sourceOn pair
  ; StaticPair.CommonRenormalizedVacuumPair.off =
      R136Static.compileR136VacuumToStaticReceipt (offPromotion pair)
  ; StaticPair.CommonRenormalizedVacuumPair.on =
      R136Static.compileR136VacuumToStaticReceipt (onPromotion pair)
  ; StaticPair.CommonRenormalizedVacuumPair.normalizationToGravityScale =
      normalizationToGravityScale pair
  ; StaticPair.CommonRenormalizedVacuumPair.commonAdditiveGravityRenormalization =
      commonAdditiveGravityRenormalization pair
  ; StaticPair.CommonRenormalizedVacuumPair.offAmplitudeUsesCommonAffineCalibration =
      R136Static.compiledStaticAmplitudeUsesAffineCalibration (offPromotion pair)
  ; StaticPair.CommonRenormalizedVacuumPair.onAmplitudeUsesCommonAffineCalibration =
      R136Static.compiledStaticAmplitudeUsesAffineCalibration (onPromotion pair)
  ; StaticPair.CommonRenormalizedVacuumPair.CommonRenormalizationConvention =
      CommonCosmologicalRenormalizationCondition pair
  ; StaticPair.CommonRenormalizedVacuumPair.commonRenormalizationConvention =
      commonCosmologicalRenormalizationCondition pair
  ; StaticPair.CommonRenormalizedVacuumPair.OffUsesCommonRenormalizationConvention =
      CommonCosmologicalRenormalizationCondition pair
  ; StaticPair.CommonRenormalizedVacuumPair.offUsesCommonRenormalizationConvention =
      commonCosmologicalRenormalizationCondition pair
  ; StaticPair.CommonRenormalizedVacuumPair.OnUsesCommonRenormalizationConvention =
      CommonCosmologicalRenormalizationCondition pair
  ; StaticPair.CommonRenormalizedVacuumPair.onUsesCommonRenormalizationConvention =
      commonCosmologicalRenormalizationCondition pair
  }

r136StaticPairToDifferentialMetricResponse :
  CommonR136AffineVacuumPair →
  Differential.DifferentialMetricResponseReceipt
r136StaticPairToDifferentialMetricResponse pair =
  StaticPair.staticPairToDifferentialMetricResponse (asCommonStaticPair pair)

r136PairDeltaLambdaIsCalibratedSourceDifference :
  (pair : CommonR136AffineVacuumPair) →
  Differential.physicalDeltaLambda
    (r136StaticPairToDifferentialMetricResponse pair)
  ≡ normalizationToGravityScale pair * (sourceOn pair - sourceOff pair)
r136PairDeltaLambdaIsCalibratedSourceDifference pair =
  StaticPair.normalizationDifferenceMatchesMetricResponseDifference
    (asCommonStaticPair pair)

r136CanProduceStaticAndDifferentialConsumersWithOneSharedCalibration : Bool
r136CanProduceStaticAndDifferentialConsumersWithOneSharedCalibration = true

independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair : Bool
independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair = false

sharedAffineCalibrationAndCommonRenormalizationStillRequired : Bool
sharedAffineCalibrationAndCommonRenormalizationStillRequired = true
