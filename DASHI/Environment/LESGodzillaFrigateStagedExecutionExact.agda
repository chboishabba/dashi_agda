module DASHI.Environment.LESGodzillaFrigateStagedExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESPhysicalWorldEngineRTXCrossPollinationExact as World
import DASHI.Environment.LESGodzillaFrigateMultiphysicsSceneExact as Scene
import DASHI.Environment.LESMultiphysicsFidelityEscalationExact as Fidelity

------------------------------------------------------------------------
-- STAGED EXECUTION KERNEL
--
-- This is deliberately a composition over ONE LES world state.  The order is
-- explicit so contact/hull/fluid/air/secondary/EM/render updates cannot be
-- silently evaluated from mutually stale states.
------------------------------------------------------------------------

data SceneStage : Set where
  contactStage : SceneStage
  structuralStage : SceneStage
  waterStage : SceneStage
  airStage : SceneStage
  secondaryPhaseStage : SceneStage
  acousticStage : SceneStage
  electromagneticStage : SceneStage
  opticalObserverStage : SceneStage

record GodzillaFrigateStepKernel
    (world : World.LESWorldEngineCarrier) : Set₁ where
  constructor godzilla-frigate-step-kernel
  field
    contactAdvance : World.WorldState world → World.WorldState world
    structuralAdvance : World.WorldState world → World.WorldState world
    waterAdvance : World.WorldState world → World.WorldState world
    airAdvance : World.WorldState world → World.WorldState world
    secondaryPhaseAdvance : World.WorldState world → World.WorldState world
    acousticAdvance : World.WorldState world → World.WorldState world
    electromagneticAdvance : World.WorldState world → World.WorldState world
    opticalObserverAdvance : World.WorldState world → World.WorldState world

    contactBackend : Fidelity.PhysicsBackendOwner
    structuralBackend : Fidelity.PhysicsBackendOwner
    waterBackend : Fidelity.PhysicsBackendOwner
    airBackend : Fidelity.PhysicsBackendOwner
    secondaryPhaseBackend : Fidelity.PhysicsBackendOwner
    acousticBackend : Fidelity.PhysicsBackendOwner
    electromagneticBackend : Fidelity.PhysicsBackendOwner
    opticalBackend : Fidelity.PhysicsBackendOwner

    contactAuthorityReference : String
    structuralAuthorityReference : String
    waterAuthorityReference : String
    airAuthorityReference : String
    secondaryPhaseAuthorityReference : String
    acousticAuthorityReference : String
    electromagneticAuthorityReference : String
    opticalAuthorityReference : String

open GodzillaFrigateStepKernel public

runPhysicalStep :
  ∀ {world : World.LESWorldEngineCarrier} →
  GodzillaFrigateStepKernel world →
  World.WorldState world →
  World.WorldState world
runPhysicalStep kernel state =
  opticalObserverAdvance kernel
    (electromagneticAdvance kernel
      (acousticAdvance kernel
        (secondaryPhaseAdvance kernel
          (airAdvance kernel
            (waterAdvance kernel
              (structuralAdvance kernel
                (contactAdvance kernel state)))))))

------------------------------------------------------------------------
-- Intermediate states are retained for debugging, provenance and adaptive
-- escalation; the final output is definitionally the staged composition.
------------------------------------------------------------------------

record GodzillaFrigateStepTrace
    {world : World.LESWorldEngineCarrier}
    (kernel : GodzillaFrigateStepKernel world)
    (initial : World.WorldState world) : Set₁ where
  constructor godzilla-frigate-step-trace
  field
    afterContact : World.WorldState world
    afterStructure : World.WorldState world
    afterWater : World.WorldState world
    afterAir : World.WorldState world
    afterSecondaryPhase : World.WorldState world
    afterAcoustics : World.WorldState world
    afterElectromagnetism : World.WorldState world
    finalState : World.WorldState world

    contactLaw : afterContact ≡ contactAdvance kernel initial
    structureLaw : afterStructure ≡ structuralAdvance kernel afterContact
    waterLaw : afterWater ≡ waterAdvance kernel afterStructure
    airLaw : afterAir ≡ airAdvance kernel afterWater
    secondaryLaw :
      afterSecondaryPhase ≡ secondaryPhaseAdvance kernel afterAir
    acousticLaw : afterAcoustics ≡ acousticAdvance kernel afterSecondaryPhase
    electromagneticLaw :
      afterElectromagnetism ≡ electromagneticAdvance kernel afterAcoustics
    opticalLaw :
      finalState ≡ opticalObserverAdvance kernel afterElectromagnetism

open GodzillaFrigateStepTrace public

record StepConservationAndResidualReceipt
    {world : World.LESWorldEngineCarrier}
    {kernel : GodzillaFrigateStepKernel world}
    {initial : World.WorldState world}
    (trace : GodzillaFrigateStepTrace kernel initial) : Set₁ where
  constructor step-conservation-and-residual-receipt
  field
    momentumLedgerReference : String
    massLedgerReference : String
    energyLedgerReference : String
    chargeLedgerReference : String
    contactResidualReference : String
    structureResidualReference : String
    waterResidualReference : String
    airResidualReference : String
    acousticResidualReference : String
    electromagneticResidualReference : String
    observerResidualReference : String
    tolerancePolicyReference : String
    escalationDecisionReference : String

open StepConservationAndResidualReceipt public

------------------------------------------------------------------------
-- Same-scene weld: a fixture supplies physical meaning; a kernel supplies the
-- transition implementation.  Neither manufactures the other.
------------------------------------------------------------------------

record GodzillaFrigateExecutableFixture
    {world : World.LESWorldEngineCarrier}
    (fixture : Scene.GodzillaFrigateWorldFixture world)
    (kernel : GodzillaFrigateStepKernel world) : Set₁ where
  constructor godzilla-frigate-executable-fixture
  field
    sceneToKernelContactReference : String
    sceneToKernelStructureReference : String
    sceneToKernelWaterReference : String
    sceneToKernelAirReference : String
    sceneToKernelAcousticReference : String
    sceneToKernelEMReference : String
    sceneToKernelOpticsReference : String
    sameWorldStateReference : String
    sameSpaceTimeReference : String
    validationReference : String

open GodzillaFrigateExecutableFixture public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data OrderedOperatorSplitIsExactCoupledSolution : Set where
orderedOperatorSplitIsNotExactCoupledSolution :
  OrderedOperatorSplitIsExactCoupledSolution → ⊥
orderedOperatorSplitIsNotExactCoupledSolution ()

data FinalImageValidatesIntermediatePhysics : Set where
finalImageDoesNotValidateIntermediatePhysics : FinalImageValidatesIntermediatePhysics → ⊥
finalImageDoesNotValidateIntermediatePhysics ()

data SameWorldStateMeansSameNumericalDiscretisation : Set where
sameWorldStateDoesNotMeanSameNumericalDiscretisation :
  SameWorldStateMeansSameNumericalDiscretisation → ⊥
sameWorldStateDoesNotMeanSameNumericalDiscretisation ()
