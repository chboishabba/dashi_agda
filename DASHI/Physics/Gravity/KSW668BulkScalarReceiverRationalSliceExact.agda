module DASHI.Physics.Gravity.KSW668BulkScalarReceiverRationalSliceExact where

------------------------------------------------------------------------
-- D2/B3: exact rational RADIAL WAVE FRONT of a 4-spatial-dimensional
-- retarded bulk massless TEST SCALAR. This is NOT a 5D graviton.
--
-- For source q(t)=t_+-2(t-tau)_++(t-2tau)_+ and receiver d>0,
-- phi(t,d)= [sqrt(t²-d²)_+ - 2sqrt((t-tau)²-d²)_+
--             + sqrt((t-2tau)²-d²)_+]/(4*pi²*d²).
-- This formula is derived and checked by
-- scripts/ksw668_brane_scalar_emitter_receiver_retarded.py.
--
-- Rational sample: geometric original 3-4-5 polyline source model:
-- brane path length=10, 5D straight source/receiver separation d=6.
-- Receiver observation proper time t=15/2 lies strictly AFTER d=6,
-- strictly BEFORE brane light time=10. Pulse tau=2, so only the FIRST
-- causal radical contributes. sqrt(t²-d²)=9/2 exactly.
-- Hence 4*pi²*phi=(9/2)/36=1/8>0. This Agda result proves its exact
-- rational radical witness and positive scaled amplitude; it does NOT
-- formalize PDE distributions, transcendental pi, source energy, or a
-- physical receiver. The smooth cylinder uses pi*R and chord 2R.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

sourceReceiverSpatialChord : ℚ
sourceReceiverSpatialChord = (+ 6) / 1

originalBraneRestrictedLightLength : ℚ
originalBraneRestrictedLightLength = (+ 10) / 1

receiverTime : ℚ
receiverTime = (+ 15) / 2

sourcePulseDuration : ℚ
sourcePulseDuration = (+ 2) / 1

radicalValue : ℚ
radicalValue = (+ 9) / 2

scaledReceiverResponse : ℚ
scaledReceiverResponse = (+ 1) / 8

-- Positive numerator equals 3/2: signal arrives after the ambient front.
signalAfterAmbientNullFrontGap :
  receiverTime + - sourceReceiverSpatialChord ≡ (+ 3) / 2
signalAfterAmbientNullFrontGap = solve []

-- Positive numerator equals 5/2: brane photon has not yet arrived.
signalBeforeBranePhotonGap :
  originalBraneRestrictedLightLength + - receiverTime
    ≡ (+ 5) / 2
signalBeforeBranePhotonGap = solve []

-- Subsequent shifted ramp Green functions are causally absent:
-- 6-(15/2-2)=1/2 and 6-(15/2-4)=5/2, positive source delays.
firstDelayedPulseOutsideAmbientFuture :
  sourceReceiverSpatialChord
    + - (receiverTime + - sourcePulseDuration) ≡ (+ 1) / 2
firstDelayedPulseOutsideAmbientFuture = solve []

secondDelayedPulseOutsideAmbientFuture :
  sourceReceiverSpatialChord
    + - (receiverTime + - ((+ 2) / 1 * sourcePulseDuration))
    ≡ (+ 5) / 2
secondDelayedPulseOutsideAmbientFuture = solve []

-- No irrational square root is asserted by definitional simplification:
-- the EXACT rational identity is the witness of a positive root.
actualRadicalSquaredFromSameFiveDimensionalChord :
  radicalValue * radicalValue
    ≡ (receiverTime * receiverTime)
       + - (sourceReceiverSpatialChord * sourceReceiverSpatialChord)
actualRadicalSquaredFromSameFiveDimensionalChord = solve []

-- 4*pi²*phi = (sqrt(t²-d²)/d²) = (9/2)/36 = 1/8,
-- where pi remains a transcendental source parameter, not fake rational.
originalRetardedGreenScaledReceiverPositive :
  (sourceReceiverSpatialChord * sourceReceiverSpatialChord)
    * scaledReceiverResponse ≡ radicalValue
originalRetardedGreenScaledReceiverPositive = solve []

-- Demonstrates the fraction is manifestly positive by a literal normal form.
receiverResponseScaledEqualsPositiveOneEighth :
  scaledReceiverResponse ≡ (+ 1) / 8
receiverResponseScaledEqualsPositiveOneEighth = solve []

-- Literal numbers above are a rigorous rational FRONT example.
-- Physical bulk wave coupling at a brane in the AdS5 Israel model
-- requires a separate time-dependent tensor or scalar boundary problem.
