{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact as Direct

denseL2IsNotMandatoryForDirectRoute :
  Direct.denseL2NormalizationMandatoryForDirectSourceRoute ≡ false
denseL2IsNotMandatoryForDirectRoute =
  Direct.denseL2NormalizationMandatoryForDirectSourceRouteIsFalse

finiteTrajectoryGapIsNotMandatoryForDirectRoute :
  Direct.finiteTrajectoryGapCalibrationMandatoryForDirectSourceRoute ≡ false
finiteTrajectoryGapIsNotMandatoryForDirectRoute =
  Direct.finiteTrajectoryGapCalibrationMandatoryForDirectSourceRouteIsFalse

moscoRecoveryIsNotMandatoryForDirectRoute :
  Direct.paEaMoscoRecoveryMandatoryForDirectSourceRoute ≡ false
moscoRecoveryIsNotMandatoryForDirectRoute =
  Direct.paEaMoscoRecoveryMandatoryForDirectSourceRouteIsFalse

continuumMeasureStillRequired :
  Direct.continuumMeasureCarrierStillRequired ≡ true
continuumMeasureStillRequired =
  Direct.continuumMeasureCarrierStillRequiredIsTrue

osReconstructionStillRequired :
  Direct.osReconstructionStillRequired ≡ true
osReconstructionStillRequired =
  Direct.osReconstructionStillRequiredIsTrue

noClayPromotion :
  Direct.clayPromotion ≡ false
noClayPromotion = Direct.clayPromotionIsFalse


------------------------------------------------------------------------
-- The H1-to-R296 bridge reuses the canonical R313 theorem owner.
------------------------------------------------------------------------

h1MagnitudeIsNotASecondPhysicalLeaf :
  Direct.routeSH1ReusesR313MagnitudeCompiler ≡ false
h1MagnitudeIsNotASecondPhysicalLeaf =
  Direct.routeSH1ReusesR313MagnitudeCompilerIsFalse

