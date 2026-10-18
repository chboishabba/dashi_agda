{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyConnectedResponseDoesNotPayPartitionB2Exact where

------------------------------------------------------------------------
-- CONNECTED NORMALIZED RESPONSE != ONE-POINT PARTITION RESPONSE.
--
-- The antigravity ordered-Haar closure proves a strict sign for a connected
-- derivative of a normalized insertion.  Preferred cosmology B2 instead uses
-- the first derivative of the partition/effective action.  These response
-- orders cannot be identified by algebra alone.
--
-- The finite normalized-expectation cross numerator is
--
--   C = N' Z - N Z'.
--
-- Holding the same base N=Z=1, the two derivative pairs
--
--   (N',Z') = (0,0),   (N',Z') = (1,1)
--
-- have exactly the same connected cross numerator C=0 while their partition
-- derivatives Z' differ.  Hence a sign/equality theorem about C cannot by
-- itself pay the one-point cosmology B2 partition-response premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ)

import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross

firstConnectedCross : ℚ
firstConnectedCross = Cross.normalizedCrossNumerator 1ℚ 1ℚ 0ℚ 0ℚ

secondConnectedCross : ℚ
secondConnectedCross = Cross.normalizedCrossNumerator 1ℚ 1ℚ 1ℚ 1ℚ

firstConnectedCrossIsZero : firstConnectedCross ≡ 0ℚ
firstConnectedCrossIsZero = refl

secondConnectedCrossIsZero : secondConnectedCross ≡ 0ℚ
secondConnectedCrossIsZero = refl

sameConnectedCrossWithDifferentPartitionDerivative :
  firstConnectedCross ≡ secondConnectedCross
sameConnectedCrossWithDifferentPartitionDerivative = refl

firstPartitionDerivative : ℚ
firstPartitionDerivative = 0ℚ

secondPartitionDerivative : ℚ
secondPartitionDerivative = 1ℚ

firstPartitionDerivativeIsZero : firstPartitionDerivative ≡ 0ℚ
firstPartitionDerivativeIsZero = refl

secondPartitionDerivativeIsOne : secondPartitionDerivative ≡ 1ℚ
secondPartitionDerivativeIsOne = refl

connectedNormalizedResponseDoesNotDeterminePartitionDerivative : Bool
connectedNormalizedResponseDoesNotDeterminePartitionDerivative = true

orderedHaarConnectedTraceCannotDirectlyPayCosmologyB2 : Bool
orderedHaarConnectedTraceCannotDirectlyPayCosmologyB2 = true
