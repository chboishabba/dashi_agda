module DASHI.Biology.DrosophilaConnectomeFunctionalEffectorStateSpaceVisualisationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BioacousticStateSpaceVisualisationExact as StateSpace
import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly
import DASHI.Biology.DrosophilaConnectomeFunctionalRegistrationBridge as Registration
import DASHI.Biology.DrosophilaMotorEffectorPhysiologyBridge as Physiology

------------------------------------------------------------------------
-- FLY CONNECTOME / FUNCTION / EFFECTOR STATE-SPACE VISUALISATION
--
-- This specializes the birdsong-derived state-space observer idea to the
-- existing end-to-end Drosophila carrier:
--
--   sensory/environment
--     -> neural state
--     -> motor command / motor drive
--     -> effector state
--     -> body / biomechanics
--     -> behavioural observation
--     -> sensory return.
--
-- The rendered manifold is an observer over this chain.  It is not another
-- biological state and it does not identify connectome geometry with
-- functional-state geometry.
------------------------------------------------------------------------

record FlyLinkedStateSpaceViews
    {C : Fly.MaleCNSStructuralCarrier}
    (E : Fly.NeuralToEffectorSurface C) : Set₁ where
  field
    VisualPoint : Set
    HistoryState : Set
    RenderedFrame : Set

    neuralPoint : Fly.NeuralState E → VisualPoint
    motorCommandPoint : Fly.MotorCommand E → VisualPoint
    motorDrivePoint : Fly.MotorNeuronDrive E → VisualPoint
    effectorPoint : Fly.EffectorState E → VisualPoint
    bodyPoint : Fly.BodyState E → VisualPoint
    behaviourPoint : Fly.BehaviourObservation E → VisualPoint
    sensoryReturnPoint : Fly.SensoryReturn E → VisualPoint

    emptyHistory : HistoryState
    appendPoint : VisualPoint → HistoryState → HistoryState
    renderHistory : HistoryState → RenderedFrame

    neuralViewReading : String
    motorViewReading : String
    effectorViewReading : String
    bodyViewReading : String
    behaviourViewReading : String
    sensoryReturnViewReading : String

open FlyLinkedStateSpaceViews public

------------------------------------------------------------------------
-- A synchronized episode keeps all biological coordinates distinct before
-- the visual projection.  The same VisualPoint carrier may be reused by the
-- renderer, but equality in that carrier has no biological meaning unless an
-- explicit consumer theorem supplies one.
------------------------------------------------------------------------

record FlySensorimotorEpisode
    {C : Fly.MaleCNSStructuralCarrier}
    {E : Fly.NeuralToEffectorSurface C}
    (views : FlyLinkedStateSpaceViews E) : Set₁ where
  field
    neuralState : Fly.NeuralState E
    motorCommand : Fly.MotorCommand E
    motorDrive : Fly.MotorNeuronDrive E
    effectorState : Fly.EffectorState E
    bodyState : Fly.BodyState E
    behaviour : Fly.BehaviourObservation E
    sensoryReturn : Fly.SensoryReturn E

    neuralVisual : VisualPoint views
    motorVisual : VisualPoint views
    effectorVisual : VisualPoint views
    bodyVisual : VisualPoint views
    behaviourVisual : VisualPoint views
    sensoryReturnVisual : VisualPoint views

    neuralVisualIsProjection :
      neuralVisual ≡ neuralPoint views neuralState
    motorVisualIsProjection :
      motorVisual ≡ motorCommandPoint views motorCommand
    effectorVisualIsProjection :
      effectorVisual ≡ effectorPoint views effectorState
    bodyVisualIsProjection :
      bodyVisual ≡ bodyPoint views bodyState
    behaviourVisualIsProjection :
      behaviourVisual ≡ behaviourPoint views behaviour
    sensoryReturnVisualIsProjection :
      sensoryReturnVisual ≡ sensoryReturnPoint views sensoryReturn

open FlySensorimotorEpisode public

------------------------------------------------------------------------
-- Structural connectome and time-varying functional geometry are separate
-- carriers.  A point in an embedding can be annotated with structural evidence
-- only through an explicit mapping receipt.
------------------------------------------------------------------------

data FunctionalToStructuralIdentityState : Set where
  exactTraceIdentity : FunctionalToStructuralIdentityState
  candidateNeuronMapping : FunctionalToStructuralIdentityState
  unresolvedFunctionalIdentity : FunctionalToStructuralIdentityState

record FunctionalStructuralAnnotation
    {C : Fly.MaleCNSStructuralCarrier}
    {E : Fly.NeuralToEffectorSurface C}
    (views : FlyLinkedStateSpaceViews E) : Set₁ where
  field
    TraceIdentity : Set
    StructuralCandidate : Set

    point : VisualPoint views
    traceIdentity : TraceIdentity
    structuralCandidate : StructuralCandidate
    identityState : FunctionalToStructuralIdentityState
    evidenceReading : String

open FunctionalStructuralAnnotation public

------------------------------------------------------------------------
-- ROM is downstream of the neural/motor interface and retains its residual.
-- A rendered reduced-effector trajectory therefore cannot manufacture an exact
-- full-effector trajectory.
------------------------------------------------------------------------

record FlyEffectorROMVisualisation
    {C : Fly.MaleCNSStructuralCarrier}
    {E : Fly.NeuralToEffectorSurface C}
    (rom : Fly.EffectorROM E) : Set₁ where
  field
    ROMPoint : Set
    coefficientPoint : Fly.Coefficient rom → ROMPoint
    residualReading : Fly.Residual rom → String
    visualisationReading : String

open FlyEffectorROMVisualisation public

------------------------------------------------------------------------
-- Fail-closed scientific boundary.
------------------------------------------------------------------------

record FlyStateSpaceVisualisationBoundary : Set where
  field
    visualProximityImpliesAnatomicalProximity : Bool
    visualProximityImpliesAnatomicalProximityIsFalse :
      visualProximityImpliesAnatomicalProximity ≡ false

    visualRecurrenceImpliesSameNeuronSet : Bool
    visualRecurrenceImpliesSameNeuronSetIsFalse :
      visualRecurrenceImpliesSameNeuronSet ≡ false

    structuralPathImpliesFunctionalActivation : Bool
    structuralPathImpliesFunctionalActivationIsFalse :
      structuralPathImpliesFunctionalActivation ≡ false

    functionalActivationImpliesCausalNecessity : Bool
    functionalActivationImpliesCausalNecessityIsFalse :
      functionalActivationImpliesCausalNecessity ≡ false

    functionalTraceIdentityImpliesMaleCNSNeuronIdentity : Bool
    functionalTraceIdentityImpliesMaleCNSNeuronIdentityIsFalse :
      functionalTraceIdentityImpliesMaleCNSNeuronIdentity ≡ false

    neuralStateImpliesEffectorState : Bool
    neuralStateImpliesEffectorStateIsFalse :
      neuralStateImpliesEffectorState ≡ false

    effectorStateImpliesRealisedBiomechanics : Bool
    effectorStateImpliesRealisedBiomechanicsIsFalse :
      effectorStateImpliesRealisedBiomechanics ≡ false

    renderedTrajectoryIsBiologicalAuthority : Bool
    renderedTrajectoryIsBiologicalAuthorityIsFalse :
      renderedTrajectoryIsBiologicalAuthority ≡ false

    provenanceMustRemainDrillable : Bool
    provenanceMustRemainDrillableIsTrue :
      provenanceMustRemainDrillable ≡ true

open FlyStateSpaceVisualisationBoundary public

canonicalFlyStateSpaceVisualisationBoundary :
  FlyStateSpaceVisualisationBoundary
canonicalFlyStateSpaceVisualisationBoundary =
  record
    { visualProximityImpliesAnatomicalProximity = false
    ; visualProximityImpliesAnatomicalProximityIsFalse = refl
    ; visualRecurrenceImpliesSameNeuronSet = false
    ; visualRecurrenceImpliesSameNeuronSetIsFalse = refl
    ; structuralPathImpliesFunctionalActivation = false
    ; structuralPathImpliesFunctionalActivationIsFalse = refl
    ; functionalActivationImpliesCausalNecessity = false
    ; functionalActivationImpliesCausalNecessityIsFalse = refl
    ; functionalTraceIdentityImpliesMaleCNSNeuronIdentity = false
    ; functionalTraceIdentityImpliesMaleCNSNeuronIdentityIsFalse = refl
    ; neuralStateImpliesEffectorState = false
    ; neuralStateImpliesEffectorStateIsFalse = refl
    ; effectorStateImpliesRealisedBiomechanics = false
    ; effectorStateImpliesRealisedBiomechanicsIsFalse = refl
    ; renderedTrajectoryIsBiologicalAuthority = false
    ; renderedTrajectoryIsBiologicalAuthorityIsFalse = refl
    ; provenanceMustRemainDrillable = true
    ; provenanceMustRemainDrillableIsTrue = refl
    }

------------------------------------------------------------------------
-- Navigation receipts: these are the already-existing authorities consumed by
-- this specialization.  They are kept as values so the owner is grep-friendly
-- without copying their scientific content.
------------------------------------------------------------------------

bioacousticOwner : String
bioacousticOwner =
  "DASHI.Biology.BioacousticStateSpaceVisualisationExact"

maleCNSOwner : String
maleCNSOwner =
  "DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge"

functionalRegistrationOwner : String
functionalRegistrationOwner =
  "DASHI.Biology.DrosophilaConnectomeFunctionalRegistrationBridge"

motorEffectorOwner : String
motorEffectorOwner =
  "DASHI.Biology.DrosophilaMotorEffectorPhysiologyBridge"

bioacousticBoundary : StateSpace.BioacousticVisualisationBoundary
bioacousticBoundary = StateSpace.canonicalBioacousticVisualisationBoundary
