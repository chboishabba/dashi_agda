{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Validation where

-- Focused R342-R344 validation surface.
--
-- R342 removes two historical overpayments:
--   * no post-hoc source-magnitude equality;
--   * no theorem over every source-direction pair when the B consumer only
--     asks for the selected mode/time pair.
--
-- R343 checks the implementation-neutral dyadic envelope producer.
-- R344 checks the shorter producer on the actual shared CMP116 marked shell.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116DyadicEnvelopeCalibrationRound343Validation
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedDirectCalibrationRound344Validation

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
