module DASHI.Biology.NeuralRepresentationLaplacianExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DynamicEffectiveTopology as DynamicTopology
import DASHI.Biology.SpectralGrokkingLatticeExact as Grokking

------------------------------------------------------------------------
-- Finite separation of representational geometry, activation state, dynamics,
-- connectivity, diffusion/Laplacian structure, and measurement.

data NeuralNode : Set where
  sensoryNode : NeuralNode
  associationNode : NeuralNode
  planningNode : NeuralNode

record PopulationActivation : Set where
  constructor populationActivation
  field
    sensoryActivity : Nat
    associationActivity : Nat
    planningActivity : Nat

open PopulationActivation public

natDistance : Nat → Nat → Nat
natDistance a b = (a ∸ b) + (b ∸ a)

laplacianVariation : PopulationActivation → Nat
laplacianVariation (populationActivation s a p) =
  natDistance s a + natDistance a p

uniformActivationHasZeroVariation :
  laplacianVariation (populationActivation 2 2 2) ≡ 0
uniformActivationHasZeroVariation = refl

nonuniformActivationHasFiniteVariation :
  laplacianVariation (populationActivation 0 2 1) ≡ 3
nonuniformActivationHasFiniteVariation = refl

data ModulatoryRegime : Set where
  inhibitedRegime : ModulatoryRegime
  permissiveRegime : ModulatoryRegime
  recurrentRegime : ModulatoryRegime

activationUpdate :
  ModulatoryRegime → PopulationActivation → PopulationActivation
activationUpdate inhibitedRegime (populationActivation s a p) =
  populationActivation s 0 p
activationUpdate permissiveRegime (populationActivation s a p) =
  populationActivation s (s + a) p
activationUpdate recurrentRegime (populationActivation s a p) =
  populationActivation s (s + a) (a + p)

sameInputDifferentRegimeDifferentActivation :
  activationUpdate inhibitedRegime (populationActivation 1 1 1)
  ≡ populationActivation 1 0 1
  ×
  activationUpdate recurrentRegime (populationActivation 1 1 1)
  ≡ populationActivation 1 2 2
sameInputDifferentRegimeDifferentActivation = refl , refl

------------------------------------------------------------------------
-- Coarse fMRI-like observation.  Distinct population states can have the same
-- regional aggregate, so the observation is a many-to-one projection.

record CoarseRegionalObservation : Set where
  constructor coarseRegionalObservation
  field
    anteriorAggregate : Nat
    posteriorAggregate : Nat

open CoarseRegionalObservation public

fmriLikeObservation : PopulationActivation → CoarseRegionalObservation
fmriLikeObservation (populationActivation s a p) =
  coarseRegionalObservation (s + a) p

microActivationA : PopulationActivation
microActivationA = populationActivation 1 2 3

microActivationB : PopulationActivation
microActivationB = populationActivation 2 1 3

fmriProjectionCollision :
  fmriLikeObservation microActivationA
  ≡ fmriLikeObservation microActivationB
fmriProjectionCollision = refl

microVariationDiffersDespiteSameObservation :
  laplacianVariation microActivationA ≡ 2
  × laplacianVariation microActivationB ≡ 3
microVariationDiffersDespiteSameObservation = refl , refl

------------------------------------------------------------------------
-- Representation-manifold/Laplacian/grokking bridge.

record NeuralRepresentationSystem : Set where
  constructor neuralRepresentationSystem
  field
    representationalDimension : Nat
    effectiveEdgeCount : Nat
    laplacianModeCount : Nat
    latentDynamicDimension : Nat
    observationDimension : Nat
    symmetryAdapted : Bool

open NeuralRepresentationSystem public

canonicalFiniteNeuralRepresentation : NeuralRepresentationSystem
canonicalFiniteNeuralRepresentation =
  neuralRepresentationSystem 3 2 3 3 2 true

canonicalModesMatchGrokkingThreeModeCarrier :
  laplacianModeCount canonicalFiniteNeuralRepresentation
  ≡ Grokking.symmetryAdaptedComponentCount Grokking.cleanupPhase
canonicalModesMatchGrokkingThreeModeCarrier = refl

record NeuralLaplacianBoundary : Set where
  constructor neuralLaplacianBoundary
  field
    graphLaplacianEqualsCompleteNeuralSystem : Bool
    graphLaplacianEqualsCompleteNeuralSystemIsFalse :
      graphLaplacianEqualsCompleteNeuralSystem ≡ false

    fMRIRecoversMicroscopicActivation : Bool
    fMRIRecoversMicroscopicActivationIsFalse :
      fMRIRecoversMicroscopicActivation ≡ false

    representationGeometryFixesDynamics : Bool
    representationGeometryFixesDynamicsIsFalse :
      representationGeometryFixesDynamics ≡ false

    activationStateEqualsLearnedRepresentation : Bool
    activationStateEqualsLearnedRepresentationIsFalse :
      activationStateEqualsLearnedRepresentation ≡ false

    LaplacianCanEncodeCoarseRelationalVariation : Bool
    LaplacianCanEncodeCoarseRelationalVariationIsTrue :
      LaplacianCanEncodeCoarseRelationalVariation ≡ true

open NeuralLaplacianBoundary public

canonicalNeuralLaplacianBoundary : NeuralLaplacianBoundary
canonicalNeuralLaplacianBoundary =
  neuralLaplacianBoundary false refl false refl false refl false refl true refl
