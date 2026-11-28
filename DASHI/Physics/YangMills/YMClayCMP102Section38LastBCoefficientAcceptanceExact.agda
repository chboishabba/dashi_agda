module DASHI.Physics.YangMills.YMClayCMP102Section38LastBCoefficientAcceptanceExact where

------------------------------------------------------------------------
-- Section38 original CMP102: last omitted odd B coefficient paid
-- for EVERY n directly by original CMP109 monotone factorial source.
-- No synthetic series, no numerically fitted bound, no new
-- source positivity premise. Only the true |X|^count Bishop
-- monomial order remains to pay this full wing term.
-- Native Agda 2.9 and source import graph pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import DASHI.Physics.YangMills.YMClayCMP102OriginalLastBCoefficientCeilingExact as Last
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102

originalNativeLastBAtMostSixth : ∀ n →
  R._≤_ (CMP102.bCoefficient n) (R._⋆ (+ 1 / 6))
originalNativeLastBAtMostSixth = Last.originalBAtMostSixth

originalNativeTwiceLastBAtMostThird : ∀ n →
  R._≤_ (R._*_ CMP102.two (CMP102.bCoefficient n))
    (R._⋆ (+ 1 / 3))
originalNativeTwiceLastBAtMostThird = Last.originalTwiceBAtMostThird
