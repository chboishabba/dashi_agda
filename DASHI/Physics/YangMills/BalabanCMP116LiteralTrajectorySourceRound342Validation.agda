{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Validation where

-- RED regression surface for Round342.
--
-- The desired API removes two historical overpayments:
--   * no post-hoc source-magnitude equality;
--   * no theorem over every source-direction pair when the B consumer only
--     asks for the selected mode/time pair.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342

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
