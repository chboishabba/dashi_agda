module DASHI.Environment.LESMultiphysicsFidelityEscalationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Environment.SurrogateCalibration as Surrogate
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESPhysicalPhotonTransportFibreExact as Photon

------------------------------------------------------------------------
-- LES MULTIPHYSICS FIDELITY ESCALATION
--
-- Spatial/sampling refinement and physical-model fidelity are independent.
-- A renderer can spend more samples without changing the constitutive model;
-- conversely one local cell can escalate to a higher-authority physical kernel
-- without globally refining the entire world.
------------------------------------------------------------------------

data PhysicsBackendKind : Set where
  learnedOrScreeningSurrogate : PhysicsBackendKind
  radiometricTransport : PhysicsBackendKind
  geometricalOptics : PhysicsBackendKind
  waveOptics : PhysicsBackendKind
  continuumFluid : PhysicsBackendKind
  reactionTransport : PhysicsBackendKind
  molecularAtomistic : PhysicsBackendKind
  quantumAtomic : PhysicsBackendKind
  gaugeField : PhysicsBackendKind
  applicationSpecificAuthoritative : PhysicsBackendKind

data FidelityReason : Set where
  residualExceeded : FidelityReason
  uncertaintyExceeded : FidelityReason
  conservationFailed : FidelityReason
  outsideCalibrationSupport : FidelityReason
  interfaceOrDiscontinuity : FidelityReason
  coherenceOrDiffractionRequired : FidelityReason
  molecularInteractionRequired : FidelityReason
  quantumTransitionRequired : FidelityReason
  gaugeInteractionRequired : FidelityReason
  policyOrValidationCritical : FidelityReason
  applicationSpecificReason : FidelityReason

record PhysicsBackendOwner : Set₁ where
  constructor physics-backend-owner
  field
    kind : PhysicsBackendKind
    repositoryOwner : String
    theoremOrRuntimeOwner : String
    externalAuthorityReference : String
    declaredRegime : String
    emittedObservables : String
    unresolvedBoundary : String

open PhysicsBackendOwner public

navierStokesFluidBackend : PhysicsBackendOwner
navierStokesFluidBackend =
  physics-backend-owner
    continuumFluid
    "chboishabba/dashi_agda"
    Fluid.nsProofLaneReference
    "application-specific fluid reduction + separately attributed Navier-Stokes authority"
    "LES fluid applications whose state/geometry/forcing/constitutive reduction has been supplied"
    "velocity, pressure, density, viscosity, flow and application-specific transport observables"
    "LES application realization is not the Clay Navier-Stokes theorem and the proof lane is not automatically a numerical LES solver"

atomicQuantumBackend : PhysicsBackendOwner
atomicQuantumBackend =
  physics-backend-owner
    quantumAtomic
    "chboishabba/dashi_agda"
    "application-selected DASHI atomic/quantum owner; constants from DASHI.Constants.Registry"
    "source/model-specific quantum or atomic interaction authority required"
    "local events whose chemistry/spectroscopy/transition model requires quantum or atomistic resolution"
    "transition amplitudes, spectra, energies or application-specific quantum observables"
    "SI h/hbar/e constants do not create a quantum dynamics model; exact atomic owner and state realization remain required"

yangMillsGaugeBackend : PhysicsBackendOwner
yangMillsGaugeBackend =
  physics-backend-owner
    gaugeField
    "chboishabba/dashi_agda"
    "DASHI.Physics.YangMills / Balaban source-native physical lanes"
    "Wilson/Balaban/gauge-theory source authority as declared by the selected owner"
    "only local/application states with an explicit gauge-field realization"
    "gauge-field observables supplied by the selected owner"
    "the current Yang-Mills proof programme is not a general-purpose real-time world-engine kernel and no Clay completion is imported"

------------------------------------------------------------------------
-- Local demand and promotion receipt.
------------------------------------------------------------------------

record LocalPhysicsDemand (Cell Time : Set) : Set₁ where
  constructor local-physics-demand
  field
    cell : Cell
    time : Time
    currentBackend : PhysicsBackendOwner
    requestedBackend : PhysicsBackendOwner
    reason : FidelityReason
    stateIdentificationReference : String
    inputProjectionReference : String
    outputProjectionReference : String
    spatialSupportReference : String
    temporalSupportReference : String
    conservationReference : String
    sourceAuthorityReference : String

open LocalPhysicsDemand public

record LocalFidelityAdmission
    {Cell Time : Set}
    (demand : LocalPhysicsDemand Cell Time) : Set₁ where
  constructor local-fidelity-admission
  field
    calibrationAssessment : Surrogate.SurrogateAssessment
    latentLaneBefore : Latent.ModelLane
    latentLaneAfter : Latent.ModelLane
    laneTransitionLaw :
      latentLaneAfter ≡
      Latent.chooseLane latentLaneBefore
        (Surrogate.assessmentEscalation calibrationAssessment)

    physicalBackendCompatibilityReference : String
    stateTransferReference : String
    unitAndCoordinateCompatibilityReference : String
    boundaryConditionTransferReference : String
    authorityAdmissionReference : String
    rollbackOrComparisonReference : String
    localValidationReference : String

open LocalFidelityAdmission public

------------------------------------------------------------------------
-- Adaptive sampling/refinement is a separate axis from physical backend depth.
------------------------------------------------------------------------

record LocalResolutionState (Cell : Set) : Set where
  constructor local-resolution-state
  field
    cell : Cell
    spatialDepth : Nat
    temporalSubsteps : Nat
    rayOrPacketBudget : Nat
    activePhysicsBackend : PhysicsBackendKind

open LocalResolutionState public

record ResolutionRefinementReceipt
    {Cell : Set}
    (before after : LocalResolutionState Cell) : Set where
  constructor resolution-refinement-receipt
  field
    samePhysicalCell : cell before ≡ cell after
    refinementReasonReference : String
    errorEstimatorReference : String
    budgetReference : String
    heldOutBiasReference : String

open ResolutionRefinementReceipt public

record PhysicsEscalationReceipt
    {Cell : Set}
    (before after : LocalResolutionState Cell) : Set where
  constructor physics-escalation-receipt
  field
    samePhysicalCell : cell before ≡ cell after
    backendRealisationReference : String
    commonStateProjectionReference : String
    crossBackendResidualReference : String
    authorityReference : String
    conservationReference : String

open PhysicsEscalationReceipt public

------------------------------------------------------------------------
-- Photon-specific escalation example: coarse radiometric transport can remain
-- coarse or locally promote to explicit packet/photon/wave semantics.
------------------------------------------------------------------------

record PhotonFidelityEscalation
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set}
    (fibre : Photon.PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    : Set₁ where
  constructor photon-fidelity-escalation
  field
    coarseSemantics : Photon.TransportTokenSemantics
    refinedSemantics : Photon.TransportTokenSemantics
    retainedPhotonFibre : Photon.PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight
    retainedPhotonFibreIsSameObject : retainedPhotonFibre ≡ fibre
    realization : Photon.PhysicalPhotonRealisation fibre
    escalationReason : FidelityReason
    eventWeightReinterpretationReference : String
    energyConservationReference : String
    crossLevelObserverAgreementReference : String
    heldOutValidationReference : String

open PhotonFidelityEscalation public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data MoreSamplesMeansMoreFundamentalPhysics : Set where
moreSamplesDoesNotMeanMoreFundamentalPhysics :
  MoreSamplesMeansMoreFundamentalPhysics → ⊥
moreSamplesDoesNotMeanMoreFundamentalPhysics ()

data MoreFundamentalBackendIsAutomaticallyMoreAccurate : Set where
moreFundamentalBackendIsNotAutomaticallyMoreAccurate :
  MoreFundamentalBackendIsAutomaticallyMoreAccurate → ⊥
moreFundamentalBackendIsNotAutomaticallyMoreAccurate ()

data LocalEscalationRequiresGlobalWorldEscalation : Set where
localEscalationDoesNotRequireGlobalWorldEscalation :
  LocalEscalationRequiresGlobalWorldEscalation → ⊥
localEscalationDoesNotRequireGlobalWorldEscalation ()

data NavierStokesProofLaneIsRealtimeWorldEngineSolver : Set where
navierStokesProofLaneIsNotRealtimeWorldEngineSolver :
  NavierStokesProofLaneIsRealtimeWorldEngineSolver → ⊥
navierStokesProofLaneIsNotRealtimeWorldEngineSolver ()

data YangMillsProofProgrammeIsRealtimeGaugeKernel : Set where
yangMillsProofProgrammeIsNotRealtimeGaugeKernel :
  YangMillsProofProgrammeIsRealtimeGaugeKernel → ⊥
yangMillsProofProgrammeIsNotRealtimeGaugeKernel ()

data SIConstantsAloneProvideAtomicDynamics : Set where
siConstantsAloneDoNotProvideAtomicDynamics : SIConstantsAloneProvideAtomicDynamics → ⊥
siConstantsAloneDoNotProvideAtomicDynamics ()
