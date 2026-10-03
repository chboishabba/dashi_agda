{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109UnsignedDifferenceNoGoExact where

------------------------------------------------------------------------
-- R109 DIFFERENCE-COORDINATE MAX-CUT.
--
-- Round109 inherits `ordinaryDifference` from
-- `SameFamilySummableScaleIncrement`.  That coordinate is required to be
-- nonnegative.  It is therefore a distance/majorant coordinate, not a signed
-- telescoping increment of the finite expectation sequence.
--
-- This matters for the one-endpoint algebraic compression: one endpoint plus
-- SAME SIGNED increments would determine the whole sequence, but the actual
-- Round109 interface does not provide those signed increments.  A proof route
-- must instead supply an absolute finite-to-completion tail estimate (or a
-- source theorem identifying the nonnegative coordinate with an absolute
-- finite-expectation difference).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source

round109StressDifferenceNonnegative :
  (dataSet : R109.SourceNativeStressScaleCauchy) →
  ∀ start count →
  0ℚ ≤ R109.stressDifference dataSet start count
round109StressDifferenceNonnegative dataSet start count =
  let increment =
        Source.sourceCompatibleSameFamilyIncrement
          (R109.source dataSet)
          (R109.smallHistory dataSet)
          (R109.stressInsertion dataSet)
  in
  substRight
    (Sum.ordinaryDifferenceNonnegative increment start count)
    (R109.stressDifferenceIsOrdinarySourceResponse dataSet start count)
  where
  substRight : ∀ {left right : ℚ} → 0ℚ ≤ right → left ≡ right → 0ℚ ≤ left
  substRight proof Agda.Builtin.Equality.refl = proof

round109DifferenceCoordinateIsNonnegative : Bool
round109DifferenceCoordinateIsNonnegative = true

nonnegativeDifferenceDoesNotDetermineSignedIncrement : Bool
nonnegativeDifferenceDoesNotDetermineSignedIncrement = true

oneEndpointSignedTelescopeIsNotDirectRound109Consumer : Bool
oneEndpointSignedTelescopeIsNotDirectRound109Consumer = true

preferredB1ConsumerIsAbsoluteFiniteToCompletionTail : Bool
preferredB1ConsumerIsAbsoluteFiniteToCompletionTail = true
