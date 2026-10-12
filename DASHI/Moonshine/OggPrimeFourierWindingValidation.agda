module DASHI.Moonshine.OggPrimeFourierWindingValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ; +_)

import DASHI.Moonshine.OggPrimeFourierWindingExact as Winding

------------------------------------------------------------------------
-- Regression contract for the Ogg-prime Fourier-winding layer.

canonicalOggCountIsFifteen : Winding.oggPrimeCount ≡ 15
canonicalOggCountIsFifteen = Winding.oggPrimeCountIsFifteen

canonicalNonOggCountIsFive : Winding.nonOggPrimeCount ≡ 5
canonicalNonOggCountIsFive = Winding.nonOggPrimeCountIsFive

contrastIsCenteredAtZeroFrequency :
  Winding.sumℤ Winding.contrastCoefficients ≡ + 0
contrastIsCenteredAtZeroFrequency = Winding.contrastCoefficientsSumZero

positiveAndNegativeWindingAreConjugateOnC3 :
  (p : Winding.Lane.MonsterPrimeLane) →
  Winding.negativeC3Phase p
  ≡ Winding.Fourier.inversePhase (Winding.positiveC3Phase p)
positiveAndNegativeWindingAreConjugateOnC3 =
  Winding.negativeWindingIsConjugation

windingLayerDoesNotPromoteAnalyticFourierCompletion :
  Winding.analyticFourierCompletionClaimed ≡ false
windingLayerDoesNotPromoteAnalyticFourierCompletion =
  Winding.analyticFourierCompletionClaimedIsFalse
