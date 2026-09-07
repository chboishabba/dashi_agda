module DASHI.Moonshine.JInvariantColourWheelWaveSignedValidation where

------------------------------------------------------------------------
-- Focused validation surface for the colour-wheel / wave / signed-FRACTRAN
-- BIDI tranche.  These are exact finite regression checks only.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using (hex-0; hex-3)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.JInvariantColourWheelWaveSignedBidiExact as Wheel

positiveHalfUncurlsAndRecurls :
  Wheel.curlSix (Wheel.uncurlSix hex-0) ≡ hex-0
positiveHalfUncurlsAndRecurls = Wheel.curlAfterUncurl hex-0

negativeHalfUncurlsAndRecurls :
  Wheel.curlSix (Wheel.uncurlSix hex-3) ≡ hex-3
negativeHalfUncurlsAndRecurls = Wheel.curlAfterUncurl hex-3

mobiusHalfTurnBecomesOrientationFlipAtZero :
  Wheel.uncurlSix (Mobius.mobiusTransport hex-0) ≡
  Wheel.flipUncurledOrientation (Wheel.uncurlSix hex-0)
mobiusHalfTurnBecomesOrientationFlipAtZero =
  Wheel.mobiusTransportIsOrientationFlipAfterUncurl hex-0

signedPositiveNegationBecomesNegativeFrequency :
  Wheel.signedMultiplicityFrequency
    (Signed.negateMultiplicity (Signed.positiveMultiplicity 7))
  ≡ Spectral.frequencyNegative
signedPositiveNegationBecomesNegativeFrequency = refl

signedZeroIsConjugationFixed :
  Wheel.signedMultiplicityFrequency
    (Signed.negateMultiplicity Signed.zeroMultiplicity)
  ≡ Spectral.conjugateFrequency
      (Wheel.signedMultiplicityFrequency Signed.zeroMultiplicity)
signedZeroIsConjugationFixed =
  Wheel.signedNegationBecomesSpectralConjugation Signed.zeroMultiplicity

firstBidiResidualIsComplexPhaseRealisation :
  Wheel.firstColourWheelAnalyticResidual ≡
  Wheel.missingComplexRootOfUnityRealisation
firstBidiResidualIsComplexPhaseRealisation = refl
