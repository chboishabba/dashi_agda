module DASHI.Physics.YangMills.BalabanCMP116ParametricToMarkedSourceRound378Validation where

------------------------------------------------------------------------
-- ROUND378 RED / R370 PARAMETRIC DISPLACEMENT -> R351 SOURCE OBJECT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.YangMills.BalabanCMP116ParametricToMarkedSourceRound378Exact as R378

round378R351SourceNoLongerPrimitive :
  R378.r351StandaloneSourceDisplacementPrimitiveAfterRound378 ≡ false
round378R351SourceNoLongerPrimitive =
  R378.r351StandaloneSourceDisplacementPrimitiveAfterRound378IsFalse

round378OnlyScalarCalibrationRemains :
  R378.parametricScaleToMarkedInputCalibrationStillRequired ≡ true
round378OnlyScalarCalibrationRemains =
  R378.parametricScaleToMarkedInputCalibrationStillRequiredIsTrue

round378ReusesR370Sensitivity :
  R378.r370ParametricSensitivityFeedsR351 ≡ true
round378ReusesR370Sensitivity =
  R378.r370ParametricSensitivityFeedsR351IsTrue
