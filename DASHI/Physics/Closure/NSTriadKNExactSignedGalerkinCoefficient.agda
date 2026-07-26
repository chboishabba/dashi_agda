module DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Exact signed velocity-form Fourier coefficient.
--
-- The primitive coefficient is the real tested value of
--
--   - i P_k [ (u_p · q) u_q ]
--
-- and the ordered-pair contribution is the literal p,q term plus the q,p
-- term.  No positive part, absolute value, phase ansatz, or factor 1/2 is
-- inserted at this layer.
------------------------------------------------------------------------

record VelocityGalerkinLaws
    {m v s : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    scalarZero imaginaryUnit : Scalar
    scalarAdd scalarMultiply : Scalar → Scalar → Scalar
    scalarNegate conjugate realPart : Scalar → Scalar

    vectorAdd : Vector → Vector → Vector
    vectorScale : Scalar → Vector → Vector
    bilinearDot hermitianPairing : Vector → Vector → Scalar

    waveVector : Mode → Vector
    lerayProject : Mode → Vector → Vector

open VelocityGalerkinLaws public

minusImaginary :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  VelocityGalerkinLaws Mode Vector Scalar → Scalar
minusImaginary L = scalarNegate L (imaginaryUnit L)

orderedVelocityInteraction :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  VelocityGalerkinLaws Mode Vector Scalar →
  Mode → Mode → Mode → Vector → Vector → Vector
orderedVelocityInteraction L k p q uP uQ =
  vectorScale L (minusImaginary L)
    (lerayProject L k
      (vectorScale L
        (bilinearDot L uP (waveVector L q))
        uQ))

orderedVelocityInteractionIsGalerkinTerm :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (L : VelocityGalerkinLaws Mode Vector Scalar)
    (k p q : Mode) (uP uQ : Vector) →
  orderedVelocityInteraction L k p q uP uQ
  ≡
  vectorScale L (scalarNegate L (imaginaryUnit L))
    (lerayProject L k
      (vectorScale L
        (bilinearDot L uP (waveVector L q))
        uQ))
orderedVelocityInteractionIsGalerkinTerm L k p q uP uQ = refl

orderedPairVelocityInteraction :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  VelocityGalerkinLaws Mode Vector Scalar →
  Mode → Mode → Mode → Vector → Vector → Vector
orderedPairVelocityInteraction L k p q uP uQ =
  vectorAdd L
    (orderedVelocityInteraction L k p q uP uQ)
    (orderedVelocityInteraction L k q p uQ uP)

orderedPairHasNoHiddenHalfFactor :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (L : VelocityGalerkinLaws Mode Vector Scalar)
    (k p q : Mode) (uP uQ : Vector) →
  orderedPairVelocityInteraction L k p q uP uQ
  ≡
  vectorAdd L
    (orderedVelocityInteraction L k p q uP uQ)
    (orderedVelocityInteraction L k q p uQ uP)
orderedPairHasNoHiddenHalfFactor L k p q uP uQ = refl

testedSignedCoefficient :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  VelocityGalerkinLaws Mode Vector Scalar →
  Mode → Mode → Mode → Vector → Vector → Vector → Scalar
testedSignedCoefficient L k p q uP uQ testK =
  realPart L
    (hermitianPairing L testK
      (orderedVelocityInteraction L k p q uP uQ))

testedOrderedPairCoefficient :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  VelocityGalerkinLaws Mode Vector Scalar →
  Mode → Mode → Mode → Vector → Vector → Vector → Scalar
testedOrderedPairCoefficient L k p q uP uQ testK =
  realPart L
    (hermitianPairing L testK
      (orderedPairVelocityInteraction L k p q uP uQ))

testedSignedCoefficientIsExactGalerkinCoefficient :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (L : VelocityGalerkinLaws Mode Vector Scalar)
    (k p q : Mode) (uP uQ testK : Vector) →
  testedSignedCoefficient L k p q uP uQ testK
  ≡
  realPart L
    (hermitianPairing L testK
      (vectorScale L (scalarNegate L (imaginaryUnit L))
        (lerayProject L k
          (vectorScale L
            (bilinearDot L uP (waveVector L q))
            uQ))))
testedSignedCoefficientIsExactGalerkinCoefficient L k p q uP uQ testK = refl

------------------------------------------------------------------------
-- Projection, reality, and phase are audits of this coefficient rather
-- than alternate definitions.
------------------------------------------------------------------------

record LerayTestReduction
    {m v s : Level}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    (L : VelocityGalerkinLaws Mode Vector Scalar) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    TransverseAt : Mode → Vector → Set s

    transverseProjectionFixed :
      ∀ k test → TransverseAt k test →
      lerayProject L k test ≡ test

    projectionSelfAdjoint :
      ∀ k test value →
      hermitianPairing L test (lerayProject L k value)
      ≡
      hermitianPairing L (lerayProject L k test) value

open LerayTestReduction public

removeLerayFromTransverseTest :
  ∀ {m v s} {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    {L : VelocityGalerkinLaws Mode Vector Scalar}
    (P : LerayTestReduction L)
    (k : Mode) (test value : Vector) →
  TransverseAt P k test →
  hermitianPairing L test (lerayProject L k value)
  ≡ hermitianPairing L test value
removeLerayFromTransverseTest {L = L} P k test value transverse
  rewrite projectionSelfAdjoint P k test value
        | transverseProjectionFixed P k test transverse
  = refl

record RealityAudit
    {m v s : Level}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    (L : VelocityGalerkinLaws Mode Vector Scalar) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    negateMode : Mode → Mode
    conjugateVector : Vector → Vector

    negateInvolutive : ∀ k → negateMode (negateMode k) ≡ k
    waveVectorReality :
      ∀ k → waveVector L (negateMode k) ≡ conjugateVector (waveVector L k)
    projectionReality :
      ∀ k value →
      lerayProject L (negateMode k) (conjugateVector value)
      ≡ conjugateVector (lerayProject L k value)

open RealityAudit public

record PhaseCoordinateDerivation
    {m v s : Level}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    (L : VelocityGalerkinLaws Mode Vector Scalar) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Phase Amplitude Polarisation : Set

    synthesize :
      Amplitude → Phase → Polarisation → Vector

    amplitudeGeometry phaseCombination phaseFunction :
      Mode → Mode → Mode →
      Amplitude → Amplitude → Amplitude →
      Phase → Phase → Phase →
      Polarisation → Polarisation → Polarisation →
      Scalar

    exactPhaseExpansion :
      ∀ k p q aP aQ aK φP φQ φK eP eQ eK →
      testedSignedCoefficient L k p q
        (synthesize aP φP eP)
        (synthesize aQ φQ eQ)
        (synthesize aK φK eK)
      ≡
      scalarMultiply L
        (amplitudeGeometry k p q
          aP aQ aK φP φQ φK eP eQ eK)
        (phaseFunction k p q
          aP aQ aK φP φQ φK eP eQ eK)

open PhaseCoordinateDerivation public

------------------------------------------------------------------------
-- Positive kernels are majorants, never definitionally the signed operator.
------------------------------------------------------------------------

record SignedMajorant
    {s : Level}
    (Scalar : Set s) : Set (lsuc s) where
  field
    _≤_ : Scalar → Scalar → Set s
    positiveMajorant : Scalar → Scalar
    signedBelowPositive :
      ∀ coefficient → coefficient ≤ positiveMajorant coefficient

open SignedMajorant public

positiveMajorantDominatesExactCoefficient :
  ∀ {s} {Scalar : Set s}
    (M : SignedMajorant Scalar)
    (coefficient : Scalar) →
  _≤_ M coefficient (positiveMajorant M coefficient)
positiveMajorantDominatesExactCoefficient = signedBelowPositive

exactSignedGalerkinCoefficientImplemented : Bool
exactSignedGalerkinCoefficientImplemented = true

exactSignedGalerkinCoefficientImplementedIsTrue :
  exactSignedGalerkinCoefficientImplemented ≡ true
exactSignedGalerkinCoefficientImplementedIsTrue = refl

positivePartIdentifiedWithExactOperator : Bool
positivePartIdentifiedWithExactOperator = false

positivePartIdentifiedWithExactOperatorIsFalse :
  positivePartIdentifiedWithExactOperator ≡ false
positivePartIdentifiedWithExactOperatorIsFalse = refl
