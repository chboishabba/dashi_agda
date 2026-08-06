module DASHI.Biology.OrientedZeroWaveTransitionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Signed/oriented zero.
--
-- The coarse discrete carrier identifies both zero germs with one ternary
-- zero.  The transition carrier retains whether zero was approached from the
-- negative or positive side.  This is a path/history refinement, not a fourth
-- truth value in every consumer.

data OrientedTrit : Set where
  negativeOne : OrientedTrit
  negativeZero : OrientedTrit
  positiveZero : OrientedTrit
  positiveOne : OrientedTrit

coarseTrit : OrientedTrit → Triadic.KernelTrit
coarseTrit negativeOne = Triadic.negativeTrit
coarseTrit negativeZero = Triadic.zeroTrit
coarseTrit positiveZero = Triadic.zeroTrit
coarseTrit positiveOne = Triadic.positiveTrit

negativeAndPositiveZeroCoarseAgree :
  coarseTrit negativeZero ≡ coarseTrit positiveZero
negativeAndPositiveZeroCoarseAgree = refl

negativeZeroNotPositiveZero : ¬ (negativeZero ≡ positiveZero)
negativeZeroNotPositiveZero ()

data ApproachDirection : Set where
  fromNegative : ApproachDirection
  fromPositive : ApproachDirection
  stationaryAtZero : ApproachDirection

approachDirection : OrientedTrit → ApproachDirection
approachDirection negativeOne = fromNegative
approachDirection negativeZero = fromNegative
approachDirection positiveZero = fromPositive
approachDirection positiveOne = fromPositive

negateOriented : OrientedTrit → OrientedTrit
negateOriented negativeOne = positiveOne
negateOriented negativeZero = positiveZero
negateOriented positiveZero = negativeZero
negateOriented positiveOne = negativeOne

negateOrientedInvolutive : (x : OrientedTrit) → negateOriented (negateOriented x) ≡ x
negateOrientedInvolutive negativeOne = refl
negateOrientedInvolutive negativeZero = refl
negateOrientedInvolutive positiveZero = refl
negateOrientedInvolutive positiveOne = refl

coarseNegationCommutes :
  (x : OrientedTrit) →
  coarseTrit (negateOriented x) ≡ Triadic.negateTrit (coarseTrit x)
coarseNegationCommutes negativeOne = refl
coarseNegationCommutes negativeZero = refl
coarseNegationCommutes positiveZero = refl
coarseNegationCommutes positiveOne = refl

------------------------------------------------------------------------
-- Finite wave samples.  Magnitude records distance from the coarse boundary;
-- side records the direction of approach.  Magnitude zero does not erase side.

data WaveSide : Set where
  negativeSide : WaveSide
  positiveSide : WaveSide

record WaveSample : Set where
  constructor waveSample
  field
    side : WaveSide
    magnitude : Nat

open WaveSample public

negativeNearZero : WaveSample
negativeNearZero = waveSample negativeSide 1

positiveNearZero : WaveSample
positiveNearZero = waveSample positiveSide 1

negativeExactZero : WaveSample
negativeExactZero = waveSample negativeSide 0

positiveExactZero : WaveSample
positiveExactZero = waveSample positiveSide 0

coarseWave : WaveSample → Triadic.KernelTrit
coarseWave (waveSample negativeSide zero) = Triadic.zeroTrit
coarseWave (waveSample positiveSide zero) = Triadic.zeroTrit
coarseWave (waveSample negativeSide (suc n)) = Triadic.negativeTrit
coarseWave (waveSample positiveSide (suc n)) = Triadic.positiveTrit

waveZeroCoarseAgreement :
  coarseWave negativeExactZero ≡ coarseWave positiveExactZero
waveZeroCoarseAgreement = refl

stepTowardZero : WaveSample → WaveSample
stepTowardZero (waveSample s zero) = waveSample s zero
stepTowardZero (waveSample s (suc n)) = waveSample s n

negativeApproachRetainsSide :
  stepTowardZero negativeNearZero ≡ negativeExactZero
negativeApproachRetainsSide = refl

positiveApproachRetainsSide :
  stepTowardZero positiveNearZero ≡ positiveExactZero
positiveApproachRetainsSide = refl

------------------------------------------------------------------------
-- A coarse observation may agree while the transition residual differs.

record ZeroResidual : Set where
  constructor zeroResidual
  field
    observed : Triadic.KernelTrit
    incoming : ApproachDirection

open ZeroResidual public

negativeZeroResidual : ZeroResidual
negativeZeroResidual = zeroResidual Triadic.zeroTrit fromNegative

positiveZeroResidual : ZeroResidual
positiveZeroResidual = zeroResidual Triadic.zeroTrit fromPositive

record OrientedZeroBoundary : Set where
  constructor orientedZeroBoundary
  field
    coarseEqualityErasesApproachDirection : Bool
    coarseEqualityErasesApproachDirectionIsFalse :
      coarseEqualityErasesApproachDirection ≡ false

    orientedZeroCreatesTwoDiscreteTernaryZeros : Bool
    orientedZeroCreatesTwoDiscreteTernaryZerosIsFalse :
      orientedZeroCreatesTwoDiscreteTernaryZeros ≡ false

    waveApproachRequiresParanormalDynamics : Bool
    waveApproachRequiresParanormalDynamicsIsFalse :
      waveApproachRequiresParanormalDynamics ≡ false

open OrientedZeroBoundary public

canonicalOrientedZeroBoundary : OrientedZeroBoundary
canonicalOrientedZeroBoundary =
  orientedZeroBoundary false refl false refl false refl
