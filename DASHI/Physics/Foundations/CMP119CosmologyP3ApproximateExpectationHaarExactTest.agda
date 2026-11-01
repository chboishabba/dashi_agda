{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExactTest where

import DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExact as P3

sameApproximateSequenceRegression =
  P3.compiledHaarUsesSameApproximateF2Sequence

combinedErrorRegression =
  P3.physicalHaarApproximateExpectationUsesCombinedVanishingError

commonLimitRegression =
  P3.compiledCommonLimitNeedsNoPointwiseSourceWeld
