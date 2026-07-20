module DASHI.Physics.WaveAlgorithmLiftRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ; +_)

open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.WaveAlgorithmLift as WAL

------------------------------------------------------------------------
-- Compact import-and-reduction surface for the exact finite part of the lift.

negativePhaseOpposesPositive :
  WAL.encodeTritWave WAL.neg ≡ WAL.waveNeg (WAL.encodeTritWave WAL.pos)
negativePhaseOpposesPositive = WAL.encodeInvolutionAsPhaseOpposition WAL.pos

positivePhaseOpposesNegative :
  WAL.encodeTritWave WAL.pos ≡ WAL.waveNeg (WAL.encodeTritWave WAL.neg)
positivePhaseOpposesNegative = WAL.encodeInvolutionAsPhaseOpposition WAL.neg

neutralAmplitudeIsZero :
  WAL.encodeTritWave WAL.zero ≡ WAL.zeroWave
neutralAmplitudeIsZero = Agda.Builtin.Equality.refl

supportNormProfile :
  WAL.encodedTritNormSq WAL.neg ≡ + 1
supportNormProfile = WAL.negHasUnitNorm

neutralNormProfile :
  WAL.encodedTritNormSq WAL.zero ≡ + 0
neutralNormProfile = WAL.zeroHasZeroNorm

involutionCloses :
  (t : WAL.Trit) → WAL.tritInvolution (WAL.tritInvolution t) ≡ t
involutionCloses = WAL.tritInvolution²
