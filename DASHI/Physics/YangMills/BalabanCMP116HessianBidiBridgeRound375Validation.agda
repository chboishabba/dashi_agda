module DASHI.Physics.YangMills.BalabanCMP116HessianBidiBridgeRound375Validation where

------------------------------------------------------------------------
-- ROUND375 RED / FOCUSED HESSIAN BIDI REGRESSION
--
-- This root is intentionally tiny.  It requires the source-facing adapter that
-- sends the R372/R373 direct Cauchy Hessian sensitivity back into the already
-- owned decoupled Cauchy-coefficient / marked boundary carrier.
--
-- The target is architectural, not a new physical estimate:
--   direct selected Hessian sensitivity
--     -> pointwise marked boundary control
--     -> decoupled Hessian coefficient bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.YangMills.BalabanCMP116HessianBidiBridgeRound375Exact as R375

round375BidiFeedsMarkedCoefficient :
  R375.directHessianSensitivityFeedsMarkedCoefficient ≡ true
round375BidiFeedsMarkedCoefficient =
  R375.directHessianSensitivityFeedsMarkedCoefficientIsTrue

round375StandaloneHScaleNotMandatory :
  R375.separateMarkedMajorantHScaleMandatoryAfterRound375 ≡ false
round375StandaloneHScaleNotMandatory =
  R375.separateMarkedMajorantHScaleMandatoryAfterRound375IsFalse

round375SameObjectAttachmentStillRequired :
  R375.sameObjectDecoupledHessianAttachmentStillRequired ≡ true
round375SameObjectAttachmentStillRequired =
  R375.sameObjectDecoupledHessianAttachmentStillRequiredIsTrue
