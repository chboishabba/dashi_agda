module DASHI.Biology.NeuralFixedTransverseObserverBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Biology.NondegenerateObserverAdmissionExact as Observer
import DASHI.Biology.TernaryFixedTransverseFiniteExact as C3

------------------------------------------------------------------------
-- Cross-pollination of Aristotle's fixed/transverse decomposition and observer
-- admission gate with the existing DASHI neural observation quotient.

activationSignal : Neural.PopulationActivation → Observer.TripleSignal
activationSignal a =
  Observer.tripleSignal
    (Neural.sensoryActivity a)
    (Neural.associationActivity a)
    (Neural.planningActivity a)

microAMassIsSix :
  Observer.signalMass (activationSignal Neural.microActivationA) ≡ 6
microAMassIsSix = refl

microBMassIsSix :
  Observer.signalMass (activationSignal Neural.microActivationB) ≡ 6
microBMassIsSix = refl

microAVariationIsFour :
  Observer.signalVariation (activationSignal Neural.microActivationA) ≡ 4
microAVariationIsFour = refl

microBVariationIsSix :
  Observer.signalVariation (activationSignal Neural.microActivationB) ≡ 6
microBVariationIsSix = refl

sameCommonMassDifferentRelationalVariation :
  Observer.signalMass (activationSignal Neural.microActivationA)
  ≡
  Observer.signalMass (activationSignal Neural.microActivationB)
  ×
  Observer.signalVariation (activationSignal Neural.microActivationA)
  ≢
  Observer.signalVariation (activationSignal Neural.microActivationB)
sameCommonMassDifferentRelationalVariation = refl , (λ ())

microAObserverAreaCodeIsTwentyFour :
  Observer.observedAreaCode
    (Observer.tripleSignal 1 1 0)
    (activationSignal Neural.microActivationA)
  ≡ 8
microAObserverAreaCodeIsTwentyFour = refl

------------------------------------------------------------------------
-- Coarse fMRI projection collision survives while transverse variation differs.

coarseCollisionPersists :
  Neural.fmriLikeObservation Neural.microActivationA
  ≡
  Neural.fmriLikeObservation Neural.microActivationB
coarseCollisionPersists = Neural.fmriProjectionCollision

relationalVariationSurvivesCoarseCollision :
  Observer.signalVariation (activationSignal Neural.microActivationA)
  ≢
  Observer.signalVariation (activationSignal Neural.microActivationB)
relationalVariationSurvivesCoarseCollision = λ ()

------------------------------------------------------------------------
-- Common amplitude and relational phase are typed independently.

neuralC3StateA : C3.FixedTransverseState
neuralC3StateA = C3.fixedTransverseState 6 C3.transversePhaseZero

neuralC3StateB : C3.FixedTransverseState
neuralC3StateB = C3.fixedTransverseState 6 C3.transversePhaseOne

neuralStatesShareCommonAmplitude :
  C3.commonAmplitude neuralC3StateA ≡ C3.commonAmplitude neuralC3StateB
neuralStatesShareCommonAmplitude = refl

neuralStatesDifferRelationally :
  C3.relationalMode neuralC3StateA ≡ C3.relationalMode neuralC3StateB → ⊥
neuralStatesDifferRelationally ()

record NeuralObserverBridgeBoundary : Set where
  constructor neuralObserverBridgeBoundary
  field
    sameCoarseReadoutImpliesSameRelationalMode : Bool
    sameCoarseReadoutImpliesSameRelationalModeIsFalse :
      sameCoarseReadoutImpliesSameRelationalMode ≡ false

    commonActivationIsPhenomenalConsciousness : Bool
    commonActivationIsPhenomenalConsciousnessIsFalse :
      commonActivationIsPhenomenalConsciousness ≡ false

canonicalNeuralObserverBridgeBoundary : NeuralObserverBridgeBoundary
canonicalNeuralObserverBridgeBoundary =
  neuralObserverBridgeBoundary false refl false refl
