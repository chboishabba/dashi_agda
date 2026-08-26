module DASHI.Biology.NeuralFixedTransverseObserverBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Biology.NondegenerateObserverAdmissionExact as Observer
import DASHI.Biology.TernaryFixedTransverseFiniteExact as C3

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

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

microBVariationIsFour :
  Observer.signalVariation (activationSignal Neural.microActivationB) ≡ 4
microBVariationIsFour = refl

sameCommonMassAndVariation :
  Observer.signalMass (activationSignal Neural.microActivationA)
  ≡
  Observer.signalMass (activationSignal Neural.microActivationB)
  ×
  Observer.signalVariation (activationSignal Neural.microActivationA)
  ≡
  Observer.signalVariation (activationSignal Neural.microActivationB)
sameCommonMassAndVariation = refl , refl

microAObserverAreaCodeIsEight :
  Observer.observedAreaCode
    (Observer.tripleSignal 1 1 0)
    (activationSignal Neural.microActivationA)
  ≡ 8
microAObserverAreaCodeIsEight = refl

microBObserverAreaCodeIsEight :
  Observer.observedAreaCode
    (Observer.tripleSignal 1 1 0)
    (activationSignal Neural.microActivationB)
  ≡ 8
microBObserverAreaCodeIsEight = refl

------------------------------------------------------------------------
-- Coarse fMRI projection and norm-like observer codes can both collide while
-- an order-sensitive Laplacian quantity remains distinct.

coarseCollisionPersists :
  Neural.fmriLikeObservation Neural.microActivationA
  ≡
  Neural.fmriLikeObservation Neural.microActivationB
coarseCollisionPersists = Neural.fmriProjectionCollision

orderedLaplacianVariationStillDiffers :
  Neural.laplacianVariation Neural.microActivationA
  ≢
  Neural.laplacianVariation Neural.microActivationB
orderedLaplacianVariationStillDiffers = λ ()

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

    sameNormLikeCodeIdentifiesOrderedState : Bool
    sameNormLikeCodeIdentifiesOrderedStateIsFalse :
      sameNormLikeCodeIdentifiesOrderedState ≡ false

    commonActivationIsPhenomenalConsciousness : Bool
    commonActivationIsPhenomenalConsciousnessIsFalse :
      commonActivationIsPhenomenalConsciousness ≡ false

canonicalNeuralObserverBridgeBoundary : NeuralObserverBridgeBoundary
canonicalNeuralObserverBridgeBoundary =
  neuralObserverBridgeBoundary false refl false refl false refl
