{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceNativeGeometricSeparationRound387Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanSourceNativeGeometricSeparationRound387Exact as R387

fixedHalfIsNotMandatory :
  R387.fixedHalfRatioMandatoryForSpectralContradiction ≡ false
fixedHalfIsNotMandatory =
  R387.fixedHalfRatioMandatoryForSpectralContradictionIsFalse

sourceNativeRatioRetained :
  R387.sourceNativeFastRatioMayBeRetained ≡ true
sourceNativeRatioRetained =
  R387.sourceNativeFastRatioMayBeRetainedIsTrue

physicalTimeCalibrationStillOpen :
  R387.sourceNativeRatioStillNeedsPhysicalTimeCalibration ≡ true
physicalTimeCalibrationStillOpen =
  R387.sourceNativeRatioStillNeedsPhysicalTimeCalibrationIsTrue

noClayPromotion : R387.clayPromotion ≡ false
noClayPromotion = R387.clayPromotionIsFalse
