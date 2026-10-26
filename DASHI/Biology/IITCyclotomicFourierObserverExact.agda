module DASHI.Biology.IITCyclotomicFourierObserverExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as Fourier
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- IIT / CYCLOTOMIC FOURIER OBSERVER WELD
--
-- The exact C3^3 Fourier transform is bijective on the repo's 27-value
-- cyclotomic signal carrier.  Therefore it is a sufficient observer for the
-- identity consumer.  By contrast, coefficient selection is lossy: an exact
-- collision is exhibited below.  This is the precise distinction needed before
-- asking whether any IIT quantity factors through a spectral representation.
------------------------------------------------------------------------

fourier27IdentitySufficient :
  Descent.ConsumerSufficient Fourier.fourier27 (λ signal → signal)
fourier27IdentitySufficient left right sameSpectrum =
  trans
    (sym (Fourier.cubeFourierInversion left))
    (trans
      (cong Fourier.inverseFourier27 sameSpectrum)
      (Fourier.cubeFourierInversion right))

zeroTriple : Fourier.Triple Fourier.Cyclotomic3
zeroTriple = Fourier.triple Fourier.zeroC Fourier.zeroC Fourier.zeroC

zeroMatrix : Fourier.Triple (Fourier.Triple Fourier.Cyclotomic3)
zeroMatrix = Fourier.triple zeroTriple zeroTriple zeroTriple

zeroSignal : Fourier.CubeSignal
zeroSignal = Fourier.triple zeroMatrix zeroMatrix zeroMatrix

hiddenTail : Fourier.Triple Fourier.Cyclotomic3
hiddenTail = Fourier.triple Fourier.zeroC Fourier.zeroC Fourier.oneC

hiddenMatrix : Fourier.Triple (Fourier.Triple Fourier.Cyclotomic3)
hiddenMatrix = Fourier.triple zeroTriple zeroTriple hiddenTail

hiddenSignal : Fourier.CubeSignal
hiddenSignal = Fourier.triple zeroMatrix zeroMatrix hiddenMatrix

firstCoefficient : Fourier.CubeSignal → Fourier.Cyclotomic3
firstCoefficient signal =
  Fourier.t0 (Fourier.t0 (Fourier.t0 signal))

lastCoefficient : Fourier.CubeSignal → Fourier.Cyclotomic3
lastCoefficient signal =
  Fourier.t2 (Fourier.t2 (Fourier.t2 signal))

firstCoefficientCollision :
  firstCoefficient zeroSignal ≡ firstCoefficient hiddenSignal
firstCoefficientCollision = refl

zeroCyclotomicNotOne : Fourier.zeroC ≡ Fourier.oneC → ⊥
zeroCyclotomicNotOne ()

firstCoefficientLosesTail :
  Descent.ConsumerNonDescentWitness
    firstCoefficient
    lastCoefficient
firstCoefficientLosesTail =
  Descent.consumerNonDescentWitness
    zeroSignal
    hiddenSignal
    refl
    zeroCyclotomicNotOne

firstCoefficientCannotRecoverTail :
  Descent.FactorsThrough firstCoefficient lastCoefficient → ⊥
firstCoefficientCannotRecoverTail =
  Descent.nonDescentWitnessBlocksFactorization
    firstCoefficientLosesTail

record CyclotomicIITObserverBoundary : Set where
  constructor cyclotomicIITObserverBoundary
  field
    exactFourier27IsInvertible : Bool
    invertibleReparameterisationLosesStateInformation : Bool
    coefficientSelectionCanLoseStateInformation : Bool
    spectralInvertibilityAutomaticallyPreservesEveryIITPartitionAlgorithm : Bool
    sameCyclotomicCarrierMeansSamePhysicalOrPhenomenalSemantics : Bool
    IITInvarianceNeedsExplicitIntertwiningProof : Bool

open CyclotomicIITObserverBoundary public

canonicalCyclotomicIITObserverBoundary : CyclotomicIITObserverBoundary
canonicalCyclotomicIITObserverBoundary =
  cyclotomicIITObserverBoundary
    true false true false false true

spectralStateRecoveryIsExact :
  exactFourier27IsInvertible canonicalCyclotomicIITObserverBoundary ≡ true
spectralStateRecoveryIsExact = refl

spectralRepresentationDoesNotSelfAuthorizeIITInvariance :
  spectralInvertibilityAutomaticallyPreservesEveryIITPartitionAlgorithm
    canonicalCyclotomicIITObserverBoundary ≡ false
spectralRepresentationDoesNotSelfAuthorizeIITInvariance = refl
