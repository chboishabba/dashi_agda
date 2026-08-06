module DASHI.Biology.TernaryMotifNeuralObservationQuotientExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.TernaryVisualMotifSemiconjugacyExact as Semiconjugacy
import DASHI.Biology.VisualMotifTransitionOperator as Motif
import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural

------------------------------------------------------------------------
-- Cross-fibre quotient: distinct ternary/motif phases may have distinct
-- microscopic Laplacian variation while sharing one coarse regional
-- observation.  This composes the Round Three visual operator with the Round
-- Five neural observation collision.
--
-- Source-facing provenance is inherited from the neural and visual source
-- atlases; no new empirical identification is promoted here.

activationOfTrit :
  Triadic.KernelTrit → Neural.PopulationActivation
activationOfTrit Triadic.negativeTrit = Neural.microActivationA
activationOfTrit Triadic.zeroTrit = Neural.microActivationB
activationOfTrit Triadic.positiveTrit = Neural.populationActivation 2 2 2

motifPhase : Triadic.KernelTrit → Motif.MotifState
motifPhase = Semiconjugacy.motifOfTrit

negativeAndZeroShareCoarseObservation :
  Neural.fmriLikeObservation (activationOfTrit Triadic.negativeTrit)
  ≡
  Neural.fmriLikeObservation (activationOfTrit Triadic.zeroTrit)
negativeAndZeroShareCoarseObservation =
  Neural.fmriProjectionCollision

negativeAndZeroHaveDifferentVariation :
  Neural.laplacianVariation (activationOfTrit Triadic.negativeTrit) ≡ 2
  ×
  Neural.laplacianVariation (activationOfTrit Triadic.zeroTrit) ≡ 3
negativeAndZeroHaveDifferentVariation =
  Neural.microVariationDiffersDespiteSameObservation

negativeAndZeroHaveDifferentMotifs :
  motifPhase Triadic.negativeTrit ≡ motifPhase Triadic.zeroTrit → ⊥
negativeAndZeroHaveDifferentMotifs ()

record TernaryNeuralObservationCollision : Set where
  constructor ternaryNeuralObservationCollision
  field
    firstPhase : Triadic.KernelTrit
    secondPhase : Triadic.KernelTrit
    firstMotif : Motif.MotifState
    secondMotif : Motif.MotifState
    sameCoarseObservation :
      Neural.fmriLikeObservation (activationOfTrit firstPhase)
      ≡
      Neural.fmriLikeObservation (activationOfTrit secondPhase)
    distinctMotif : firstMotif ≡ secondMotif → ⊥
    firstMotifIsProjection : firstMotif ≡ motifPhase firstPhase
    secondMotifIsProjection : secondMotif ≡ motifPhase secondPhase

open TernaryNeuralObservationCollision public

canonicalTernaryNeuralObservationCollision :
  TernaryNeuralObservationCollision
canonicalTernaryNeuralObservationCollision =
  ternaryNeuralObservationCollision
    Triadic.negativeTrit
    Triadic.zeroTrit
    Motif.latticeMotif
    Motif.tunnelMotif
    negativeAndZeroShareCoarseObservation
    (λ ())
    refl
    refl

record TernaryMotifNeuralBoundary : Set where
  constructor ternaryMotifNeuralBoundary
  field
    coarseObservationIdentifiesTernaryPhase : Bool
    coarseObservationIdentifiesTernaryPhaseIsFalse :
      coarseObservationIdentifiesTernaryPhase ≡ false

    motifIdentifiesMicroscopicActivation : Bool
    motifIdentifiesMicroscopicActivationIsFalse :
      motifIdentifiesMicroscopicActivation ≡ false

canonicalTernaryMotifNeuralBoundary : TernaryMotifNeuralBoundary
canonicalTernaryMotifNeuralBoundary =
  ternaryMotifNeuralBoundary false refl false refl
