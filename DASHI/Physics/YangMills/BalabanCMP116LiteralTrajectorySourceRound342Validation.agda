{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Validation where

-- RED regression surface for Round342.
--
-- This module intentionally names the desired literal-source API before the
-- implementation owner exists.  The production change that makes this surface
-- compile is the Round342 source constructor which removes the post-hoc
-- source-magnitude equality from the R341 route.

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
