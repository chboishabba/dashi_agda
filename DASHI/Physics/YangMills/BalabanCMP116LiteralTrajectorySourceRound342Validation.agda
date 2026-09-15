{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Validation where

-- Focused R342/R343 validation surface.
--
-- R342 removes two historical overpayments:
--   * no post-hoc source-magnitude equality;
--   * no theorem over every source-direction pair when the B consumer only
--     asks for the selected mode/time pair.
--
-- R343 is imported below so the same focused root also checks the optional
-- direct dyadic calibration producer.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116DyadicEnvelopeCalibrationRound343Validation

postHocSourceMagnitudeEqualityRemoved :
  R342.postHocSourceMagnitudeEqualityRequired ≡ false
postHocSourceMagnitudeEqualityRemoved =
  R342.postHocSourceMagnitudeEqualityRequiredIsFalse

literalTrajectorySourceIsDirectProducerABI :
  R342.literalTrajectorySourceDirectProducer ≡ true
literalTrajectorySourceIsDirectProducerABI =
  R342.literalTrajectorySourceDirectProducerIsTrue

allSourceDirectionPairsNotRequired :
  R342.allSourceDirectionPairsRequired ≡ false
allSourceDirectionPairsNotRequired =
  R342.allSourceDirectionPairsRequiredIsFalse
