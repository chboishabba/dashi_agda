module DASHI.ComputerScience.FlyPesticideNDimCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact as FlyNDim
import DASHI.ComputerScience.FlyPesticideSituatedObservationExact as Toxicology

------------------------------------------------------------------------
-- FLY NDIM × PESTICIDE OBSERVATION CROSS-POLLINATION
--
-- The shared architecture is observational, not biological identity.  Fly NDim
-- fibres encode candidate structural/network roles; pesticide observations
-- encode exposure/assay/tissue/source roles.  Neither coordinate determines the
-- other.  The finite collisions below are DASHI synthesis and do not attribute
-- new wiring or toxicology claims to the cited literature.
------------------------------------------------------------------------

data IntegratedFlyWorld : Set where
  directNeuralWorld : IntegratedFlyWorld
  commonInputNeuralWorld : IntegratedFlyWorld
  directReproductiveWorld : IntegratedFlyWorld
  directGenotoxicWorld : IntegratedFlyWorld
  heldOutDirectNeuralWorld : IntegratedFlyWorld

data EvaluationCarrierRole : Set where
  trainingObservation : EvaluationCarrierRole
  heldOutPairObservation : EvaluationCarrierRole
  heldOutRegionObservation : EvaluationCarrierRole

data CoarseFlyPesticideEndpoint : Set where
  neuralEndpoint : CoarseFlyPesticideEndpoint
  reproductiveEndpoint : CoarseFlyPesticideEndpoint
  genotoxicEndpoint : CoarseFlyPesticideEndpoint

worldFibre : IntegratedFlyWorld → FlyNDim.StructuralFibre
worldFibre directNeuralWorld = FlyNDim.directForward
worldFibre commonInputNeuralWorld = FlyNDim.commonInput
worldFibre directReproductiveWorld = FlyNDim.directForward
worldFibre directGenotoxicWorld = FlyNDim.directForward
worldFibre heldOutDirectNeuralWorld = FlyNDim.directForward

worldEndpoint : IntegratedFlyWorld → CoarseFlyPesticideEndpoint
worldEndpoint directNeuralWorld = neuralEndpoint
worldEndpoint commonInputNeuralWorld = neuralEndpoint
worldEndpoint directReproductiveWorld = reproductiveEndpoint
worldEndpoint directGenotoxicWorld = genotoxicEndpoint
worldEndpoint heldOutDirectNeuralWorld = neuralEndpoint

worldEvaluationRole : IntegratedFlyWorld → EvaluationCarrierRole
worldEvaluationRole directNeuralWorld = trainingObservation
worldEvaluationRole commonInputNeuralWorld = trainingObservation
worldEvaluationRole directReproductiveWorld = trainingObservation
worldEvaluationRole directGenotoxicWorld = trainingObservation
worldEvaluationRole heldOutDirectNeuralWorld = heldOutRegionObservation

------------------------------------------------------------------------
-- Orthogonality witnesses.
------------------------------------------------------------------------

endpointCannotRecoverStructuralFibre :
  INF.FactorsThrough worldEndpoint worldFibre → ⊥
endpointCannotRecoverStructuralFibre =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      directNeuralWorld
      commonInputNeuralWorld
      refl
      (λ ()))

structuralFibreCannotRecoverToxicologyEndpoint :
  INF.FactorsThrough worldFibre worldEndpoint → ⊥
structuralFibreCannotRecoverToxicologyEndpoint =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      directNeuralWorld
      directReproductiveWorld
      refl
      (λ ()))

structuralFibreCannotRecoverEvaluationRole :
  INF.FactorsThrough worldFibre worldEvaluationRole → ⊥
structuralFibreCannotRecoverEvaluationRole =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      directNeuralWorld
      heldOutDirectNeuralWorld
      refl
      (λ ()))

------------------------------------------------------------------------
-- Product carrier: both coordinates may coexist, but coexistence is not a
-- mechanism theorem.  Existing Fly NDim held-out/null boundaries remain live.
------------------------------------------------------------------------

record FlyPesticideNDimObservation : Set where
  constructor fly-pesticide-ndim-observation
  field
    situatedToxicology : Toxicology.FlyPesticideSituatedObservation
    structuralFibre : FlyNDim.StructuralFibre
    evaluationRole : EvaluationCarrierRole
    interpretation : String
open FlyPesticideNDimObservation public

thiaclopridSleepDirectFixture : FlyPesticideNDimObservation
thiaclopridSleepDirectFixture = fly-pesticide-ndim-observation
  Toxicology.thiaclopridSleepObservation
  FlyNDim.directForward
  trainingObservation
  "repository-local product fixture only: retaining a direct-forward structural coordinate does not claim that this fibre mediates the source toxicology endpoint"

------------------------------------------------------------------------
-- WrongType / mechanism firewalls.
------------------------------------------------------------------------

data ConnectomeFibreCreatesPesticideEffect : Set where
data ToxicologyEndpointCreatesPairSpecificWiringMechanism : Set where
data SharedBrainRegionCreatesSameMeasurementObject : Set where
data HeldOutToxicologyObservationCreatesUnseenRegionGeneralization : Set where
data PesticideEffectRejectsStrengthPreservingWiringNull : Set where

connectomeFibreDoesNotCreatePesticideEffect :
  ConnectomeFibreCreatesPesticideEffect → ⊥
connectomeFibreDoesNotCreatePesticideEffect ()

toxicologyEndpointDoesNotCreatePairSpecificWiringMechanism :
  ToxicologyEndpointCreatesPairSpecificWiringMechanism → ⊥
toxicologyEndpointDoesNotCreatePairSpecificWiringMechanism ()

sharedBrainRegionDoesNotCreateSameMeasurementObject :
  SharedBrainRegionCreatesSameMeasurementObject → ⊥
sharedBrainRegionDoesNotCreateSameMeasurementObject ()

heldOutToxicologyDoesNotCreateUnseenRegionGeneralization :
  HeldOutToxicologyObservationCreatesUnseenRegionGeneralization → ⊥
heldOutToxicologyDoesNotCreateUnseenRegionGeneralization ()

pesticideEffectDoesNotRejectStrengthPreservingWiringNull :
  PesticideEffectRejectsStrengthPreservingWiringNull → ⊥
pesticideEffectDoesNotRejectStrengthPreservingWiringNull ()

------------------------------------------------------------------------
-- Existing NDim interpretation remains authoritative: the wiring null is paid
-- but not rejected, so this bridge cannot upgrade pair-specific wiring claims.
------------------------------------------------------------------------

existingFlyNDimInterpretation : FlyNDim.CurrentFlyNDimInterpretation
existingFlyNDimInterpretation = FlyNDim.currentFlyNDimInterpretation

record FlyPesticideNDimCrossPollinationBoundary : Set where
  constructor fly-pesticide-ndim-cross-pollination-boundary
  field
    structuralAndToxicologyCoordinatesIndependent : Bool
    trainingHeldOutRoleRetained : Bool
    sourceToxicologyAttributionRetained : Bool
    flyNDimNullBoundaryRetained : Bool
    connectomeFibreCreatesPesticideEffect : Bool
    toxicologyEndpointCreatesPairSpecificWiringMechanism : Bool
    pesticideEffectRejectsStrengthPreservingWiringNull : Bool
    sameEndpointCreatesSameStructuralFibre : Bool
    sameStructuralFibreCreatesSameEndpoint : Bool
open FlyPesticideNDimCrossPollinationBoundary public

canonicalFlyPesticideNDimCrossPollinationBoundary : FlyPesticideNDimCrossPollinationBoundary
canonicalFlyPesticideNDimCrossPollinationBoundary =
  fly-pesticide-ndim-cross-pollination-boundary
    true true true true
    false false false false false
