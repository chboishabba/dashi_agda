module DASHI.Moonshine.JInvariantColourWheelPolyphaseSpectralBidiExact where

------------------------------------------------------------------------
-- POLYPHASE <-> C3 SPECTRAL FINITE WELD
--
-- This closes a finite transcription gap discovered by the BIDI/introspective
-- pass.  Base369PolyphaseCharacters and the 27 spectral owner independently
-- use three labels for zero/positive/negative phase.  Here they are proved
-- equivalent as finite carriers.  This is NOT a complex root-of-unity theorem,
-- Fourier inversion theorem, theta realization, or analytic j statement.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369PolyphaseCharacters as Polyphase
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.JInvariantColourWheelWaveSignedBidiExact as Wheel

sequenceToFrequency : Polyphase.C3Sequence → Spectral.AxisFrequency
sequenceToFrequency Polyphase.zeroSequence = Spectral.frequencyZero
sequenceToFrequency Polyphase.positiveSequence = Spectral.frequencyPositive
sequenceToFrequency Polyphase.negativeSequence = Spectral.frequencyNegative

frequencyToSequence : Spectral.AxisFrequency → Polyphase.C3Sequence
frequencyToSequence Spectral.frequencyZero = Polyphase.zeroSequence
frequencyToSequence Spectral.frequencyPositive = Polyphase.positiveSequence
frequencyToSequence Spectral.frequencyNegative = Polyphase.negativeSequence

sequenceFrequencyRoundTrip :
  (s : Polyphase.C3Sequence) →
  frequencyToSequence (sequenceToFrequency s) ≡ s
sequenceFrequencyRoundTrip Polyphase.zeroSequence = refl
sequenceFrequencyRoundTrip Polyphase.positiveSequence = refl
sequenceFrequencyRoundTrip Polyphase.negativeSequence = refl

frequencySequenceRoundTrip :
  (f : Spectral.AxisFrequency) →
  sequenceToFrequency (frequencyToSequence f) ≡ f
frequencySequenceRoundTrip Spectral.frequencyZero = refl
frequencySequenceRoundTrip Spectral.frequencyPositive = refl
frequencySequenceRoundTrip Spectral.frequencyNegative = refl

conjugateSequence : Polyphase.C3Sequence → Polyphase.C3Sequence
conjugateSequence Polyphase.zeroSequence = Polyphase.zeroSequence
conjugateSequence Polyphase.positiveSequence = Polyphase.negativeSequence
conjugateSequence Polyphase.negativeSequence = Polyphase.positiveSequence

conjugateSequenceInvolutive :
  (s : Polyphase.C3Sequence) →
  conjugateSequence (conjugateSequence s) ≡ s
conjugateSequenceInvolutive Polyphase.zeroSequence = refl
conjugateSequenceInvolutive Polyphase.positiveSequence = refl
conjugateSequenceInvolutive Polyphase.negativeSequence = refl

polyphaseConjugationMatchesSpectralConjugation :
  (s : Polyphase.C3Sequence) →
  sequenceToFrequency (conjugateSequence s) ≡
  Spectral.conjugateFrequency (sequenceToFrequency s)
polyphaseConjugationMatchesSpectralConjugation Polyphase.zeroSequence = refl
polyphaseConjugationMatchesSpectralConjugation Polyphase.positiveSequence = refl
polyphaseConjugationMatchesSpectralConjugation Polyphase.negativeSequence = refl

------------------------------------------------------------------------
-- Signed-FRACTRAN and polyphase now meet on the SAME finite frequency label.
-- Magnitude remains on the FRACTRAN side and exponent arithmetic remains on
-- the polyphase side; only the three-valued observer is shared.
------------------------------------------------------------------------

signedMultiplicitySequence :
  Wheel.Signed.SignedMultiplicity → Polyphase.C3Sequence
signedMultiplicitySequence m =
  frequencyToSequence (Wheel.signedMultiplicityFrequency m)

signedNegationBecomesSequenceConjugation :
  (m : Wheel.Signed.SignedMultiplicity) →
  signedMultiplicitySequence (Wheel.Signed.negateMultiplicity m) ≡
  conjugateSequence (signedMultiplicitySequence m)
signedNegationBecomesSequenceConjugation (Wheel.Signed.negativeMultiplicity n) = refl
signedNegationBecomesSequenceConjugation Wheel.Signed.zeroMultiplicity = refl
signedNegationBecomesSequenceConjugation (Wheel.Signed.positiveMultiplicity n) = refl

------------------------------------------------------------------------
-- BIDI consequence: with the finite carrier correspondence paid, the first
-- remaining residual in Wheel.colourWheelBidiCut is genuinely analytic.
------------------------------------------------------------------------

finitePolyphaseSpectralWeldPaid :
  Wheel.firstColourWheelAnalyticResidual ≡
  Wheel.missingComplexRootOfUnityRealisation
finitePolyphaseSpectralWeldPaid = refl
