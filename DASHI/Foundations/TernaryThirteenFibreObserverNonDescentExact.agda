{-# OPTIONS --safe #-}
module DASHI.Foundations.TernaryThirteenFibreObserverNonDescentExact where

------------------------------------------------------------------------
-- H2.01 finite analogue: the 12-coordinate prefix observer does not
-- determine the 13th coordinate. This is a NON-DESCENT proof with two
-- concrete whole-word witnesses, NOT a fabricated source observer map.
-- Source relational observer identification is still unpaid.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.TernaryThirteenFibreSplitExact as F
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as P

prefixObserver : F.TritWord 13 → F.TritWord 12
prefixObserver w =
  proj₁ (F.ternaryThirteenSplitTwelvePlusOne w)

lastCoordinateConsumer : F.TritWord 13 → F.Trit
lastCoordinateConsumer = P.lastTrit

baseTwelve : F.TritWord 12
baseTwelve = P.zeroTritWord 12

neutralExtension positiveExtension : F.TritWord 13
neutralExtension =
  F.ternaryThirteenJoinTwelvePlusOne
    (baseTwelve , P.singleTrit F.neutral)
positiveExtension =
  F.ternaryThirteenJoinTwelvePlusOne
    (baseTwelve , P.singleTrit F.positive)

neutralPrefixIsBase :
  prefixObserver neutralExtension ≡ baseTwelve
neutralPrefixIsBase =
  cong proj₁
    (F.ternaryThirteenSplitRoundTrip
      (baseTwelve , P.singleTrit F.neutral))

positivePrefixIsBase :
  prefixObserver positiveExtension ≡ baseTwelve
positivePrefixIsBase =
  cong proj₁
    (F.ternaryThirteenSplitRoundTrip
      (baseTwelve , P.singleTrit F.positive))

neutralLastIsNeutral :
  lastCoordinateConsumer neutralExtension ≡ F.neutral
neutralLastIsNeutral =
  cong (λ q → proj₁ (proj₂ q))
    (F.ternaryThirteenSplitRoundTrip
      (baseTwelve , P.singleTrit F.neutral))

positiveLastIsPositive :
  lastCoordinateConsumer positiveExtension ≡ F.positive
positiveLastIsPositive =
  cong (λ q → proj₁ (proj₂ q))
    (F.ternaryThirteenSplitRoundTrip
      (baseTwelve , P.singleTrit F.positive))

neutralIsNotPositive : ¬ (F.neutral ≡ F.positive)
neutralIsNotPositive ()

-- This shows no function out of the twelve-coordinate prefix can
-- reconstruct the original last trit for all thirteen-trit words.
centralPunctureObserverDescent :
  (f : F.TritWord 12 → F.Trit) →
  ((word : F.TritWord 13) →
    f (prefixObserver word) ≡ lastCoordinateConsumer word) →
  ⊥
centralPunctureObserverDescent f supposed
  rewrite neutralPrefixIsBase
        | positivePrefixIsBase
        | neutralLastIsNeutral
        | positiveLastIsPositive =
  neutralIsNotPositive
    (trans (sym (supposed neutralExtension))
           (supposed positiveExtension))
