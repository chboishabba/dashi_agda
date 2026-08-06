module DASHI.Biology.OrientedZeroJetTransitionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero

------------------------------------------------------------------------
-- Finite first- and second-jet refinement of oriented zero.  The coarse value
-- can be zero while velocity, acceleration, and passage history remain typed.
-- This is a checked finite interface for a later continuous germ/jet model.

data DerivativeSign : Set where
  negativeDerivative : DerivativeSign
  zeroDerivative : DerivativeSign
  positiveDerivative : DerivativeSign

data PassageKind : Set where
  approachesWithoutCrossing : PassageKind
  crossesNegativeToPositive : PassageKind
  crossesPositiveToNegative : PassageKind
  touchesAndReflectsNegative : PassageKind
  touchesAndReflectsPositive : PassageKind
  sticksAtZero : PassageKind

record OrientedSecondJet : Set where
  constructor orientedSecondJet
  field
    position : Zero.OrientedTrit
    velocity : DerivativeSign
    acceleration : DerivativeSign
    passage : PassageKind

open OrientedSecondJet public

coarseJetPosition : OrientedSecondJet → Triadic.KernelTrit
coarseJetPosition jet = Zero.coarseTrit (position jet)

negativeApproachJet : OrientedSecondJet
negativeApproachJet =
  orientedSecondJet
    Zero.negativeZero
    positiveDerivative
    zeroDerivative
    approachesWithoutCrossing

positiveApproachJet : OrientedSecondJet
positiveApproachJet =
  orientedSecondJet
    Zero.positiveZero
    negativeDerivative
    zeroDerivative
    approachesWithoutCrossing

negativeToPositiveCrossingJet : OrientedSecondJet
negativeToPositiveCrossingJet =
  orientedSecondJet
    Zero.negativeZero
    positiveDerivative
    positiveDerivative
    crossesNegativeToPositive

positiveToNegativeCrossingJet : OrientedSecondJet
positiveToNegativeCrossingJet =
  orientedSecondJet
    Zero.positiveZero
    negativeDerivative
    negativeDerivative
    crossesPositiveToNegative

negativeReflectionJet : OrientedSecondJet
negativeReflectionJet =
  orientedSecondJet
    Zero.negativeZero
    zeroDerivative
    negativeDerivative
    touchesAndReflectsNegative

positiveReflectionJet : OrientedSecondJet
positiveReflectionJet =
  orientedSecondJet
    Zero.positiveZero
    zeroDerivative
    positiveDerivative
    touchesAndReflectsPositive

stickingJet : OrientedSecondJet
stickingJet =
  orientedSecondJet
    Zero.positiveZero
    zeroDerivative
    zeroDerivative
    sticksAtZero

------------------------------------------------------------------------
-- Coarse equality does not collapse the jet.

oppositeApproachesShareCoarseZero :
  coarseJetPosition negativeApproachJet
  ≡ coarseJetPosition positiveApproachJet
oppositeApproachesShareCoarseZero = refl

crossingAndReflectionShareCoarseZero :
  coarseJetPosition negativeToPositiveCrossingJet
  ≡ coarseJetPosition negativeReflectionJet
crossingAndReflectionShareCoarseZero = refl

negativeAndPositiveCrossingKindsDiffer :
  ¬ (passage negativeToPositiveCrossingJet
     ≡ passage positiveToNegativeCrossingJet)
negativeAndPositiveCrossingKindsDiffer ()

crossingAndReflectionKindsDiffer :
  ¬ (passage negativeToPositiveCrossingJet
     ≡ passage negativeReflectionJet)
crossingAndReflectionKindsDiffer ()

reflectionAndStickingKindsDiffer :
  ¬ (passage positiveReflectionJet ≡ passage stickingJet)
reflectionAndStickingKindsDiffer ()

------------------------------------------------------------------------
-- Reflection reverses the oriented carrier and derivative signs.

negateDerivative : DerivativeSign → DerivativeSign
negateDerivative negativeDerivative = positiveDerivative
negateDerivative zeroDerivative = zeroDerivative
negateDerivative positiveDerivative = negativeDerivative

negateDerivativeInvolutive :
  (sign : DerivativeSign) → negateDerivative (negateDerivative sign) ≡ sign
negateDerivativeInvolutive negativeDerivative = refl
negateDerivativeInvolutive zeroDerivative = refl
negateDerivativeInvolutive positiveDerivative = refl

reflectPassage : PassageKind → PassageKind
reflectPassage approachesWithoutCrossing = approachesWithoutCrossing
reflectPassage crossesNegativeToPositive = crossesPositiveToNegative
reflectPassage crossesPositiveToNegative = crossesNegativeToPositive
reflectPassage touchesAndReflectsNegative = touchesAndReflectsPositive
reflectPassage touchesAndReflectsPositive = touchesAndReflectsNegative
reflectPassage sticksAtZero = sticksAtZero

reflectPassageInvolutive :
  (kind : PassageKind) → reflectPassage (reflectPassage kind) ≡ kind
reflectPassageInvolutive approachesWithoutCrossing = refl
reflectPassageInvolutive crossesNegativeToPositive = refl
reflectPassageInvolutive crossesPositiveToNegative = refl
reflectPassageInvolutive touchesAndReflectsNegative = refl
reflectPassageInvolutive touchesAndReflectsPositive = refl
reflectPassageInvolutive sticksAtZero = refl

reflectJet : OrientedSecondJet → OrientedSecondJet
reflectJet (orientedSecondJet x velocity acceleration kind) =
  orientedSecondJet
    (Zero.negateOriented x)
    (negateDerivative velocity)
    (negateDerivative acceleration)
    (reflectPassage kind)

reflectJetInvolutive : (jet : OrientedSecondJet) → reflectJet (reflectJet jet) ≡ jet
reflectJetInvolutive
  (orientedSecondJet x velocity acceleration kind)
  rewrite Zero.negateOrientedInvolutive x
        | negateDerivativeInvolutive velocity
        | negateDerivativeInvolutive acceleration
        | reflectPassageInvolutive kind = refl

reflectionExchangesCrossingDirection :
  reflectJet negativeToPositiveCrossingJet
  ≡ positiveToNegativeCrossingJet
reflectionExchangesCrossingDirection = refl

record OrientedZeroJetBoundary : Set where
  constructor orientedZeroJetBoundary
  field
    coarseZeroDeterminesPassageKind : Bool
    coarseZeroDeterminesPassageKindIsFalse :
      coarseZeroDeterminesPassageKind ≡ false

    finiteJetIsAContinuumODESolution : Bool
    finiteJetIsAContinuumODESolutionIsFalse :
      finiteJetIsAContinuumODESolution ≡ false

    reflectionErasesVelocityAndAcceleration : Bool
    reflectionErasesVelocityAndAccelerationIsFalse :
      reflectionErasesVelocityAndAcceleration ≡ false

    higherJetRefinementCanPreserveCrossingHistory : Bool
    higherJetRefinementCanPreserveCrossingHistoryIsTrue :
      higherJetRefinementCanPreserveCrossingHistory ≡ true

open OrientedZeroJetBoundary public

canonicalOrientedZeroJetBoundary : OrientedZeroJetBoundary
canonicalOrientedZeroJetBoundary =
  orientedZeroJetBoundary false refl false refl false refl true refl
