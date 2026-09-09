module DASHI.Environment.LESPhysicalWorldEngineRTXCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESDomainBasisBidiFrontierExact as Domain
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESPhysicalPhotonTransportFibreExact as Photon
import DASHI.Environment.LESWaterPhotonInteractionExact as Water
import DASHI.Environment.LESMultiphysicsFidelityEscalationExact as Fidelity
import DASHI.Environment.DashiRTXPhotosyntheticAdaptiveTransportCrossPollinationExact as Adaptive
import DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact as Photo

------------------------------------------------------------------------
-- LIVING ENVIRONMENT SIMULATOR WORLD-ENGINE CONTRACT
--
-- Project specification provenance:
--   chboishabba/Living-Environment-System README.md (main)
--
-- The README defines LES as a modular, multi-scale, bidirectionally coupled
-- world engine with a common state registry, adaptive/sub-stepped time,
-- conservative couplers, prototype/HPC execution paths and visualization /
-- Unreal/Unity bridges.  That project document is architecture provenance, not
-- external scientific authority for any constitutive law below.
------------------------------------------------------------------------

lesProjectRepository : String
lesProjectRepository = "chboishabba/Living-Environment-System"

lesProjectSpecification : String
lesProjectSpecification = "README.md@main: modular multi-scale bidirectional world engine; common state registry; adaptive/sub-stepped time; conservative couplers; Python/HPC paths; interactive-engine bridge"

record LESWorldEngineCarrier : Set₁ where
  constructor les-world-engine-carrier
  field
    WorldState : Set
    Cell : Set
    Time : Set
    Event : Set
    Observation : Set

    stateAt : WorldState → Cell → Time → Event
    observeWorld : WorldState → Observation

    spatialRegistryReference : String
    temporalRegistryReference : String
    unitMetadataReference : String
    coordinateReference : String
    eventBusReference : String
    checkpointReference : String
    reproducibilityReference : String

open LESWorldEngineCarrier public

------------------------------------------------------------------------
-- Modules exchange projections of ONE world state.  Merely taking products of
-- model states is not evidence that a physically meaningful coupling exists.
------------------------------------------------------------------------

record WorldModuleProjection
    (world : LESWorldEngineCarrier)
    (ModuleState : Set) : Set₁ where
  constructor world-module-projection
  field
    project : WorldState world → ModuleState
    injectUpdate : ModuleState → WorldState world → WorldState world
    variableContractReference : String
    unitContractReference : String
    supportReference : String
    authorityReference : String

open WorldModuleProjection public

record ConservativeWorldExchange
    {world : LESWorldEngineCarrier}
    {SourceState TargetState Flux : Set}
    (source : WorldModuleProjection world SourceState)
    (target : WorldModuleProjection world TargetState) : Set₁ where
  constructor conservative-world-exchange
  field
    sourceToFlux : SourceState → Flux
    applyFlux : Flux → TargetState → TargetState
    exchangeFrequencyReference : String
    conservativeRemappingReference : String
    commonSpaceTimeReference : String
    balanceReference : String
    numericalResidualReference : String
    validationReference : String

open ConservativeWorldExchange public

------------------------------------------------------------------------
-- Photon/ray transport is one world-module fibre.  It can carry a radiometric
-- sample, packet, literal photon event or coherent-wave packet only according
-- to the explicit realization in LESPhysicalPhotonTransportFibreExact.
------------------------------------------------------------------------

record WorldPhotonProjection
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set}
    (world : LESWorldEngineCarrier)
    (photon : Photon.PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    : Set₁ where
  constructor world-photon-projection
  field
    worldToFinePhotonEventsReference : String
    photonEventsToWorldUpdateReference : String
    worldCellMatchesPhotonCellReference : String
    worldTimeMatchesPhotonTimeReference : String
    energyLedgerReference : String
    provenanceReference : String

open WorldPhotonProjection public

------------------------------------------------------------------------
-- Water is the first explicit medium interaction: same world state -> fluid
-- state + optical state + photon interaction, with separate calibration.
------------------------------------------------------------------------

record WorldWaterPhotonWeld
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set}
    {Scalar Temperature Salinity : Set}
    (world : LESWorldEngineCarrier)
    (photon : Photon.PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    (fluid : Fluid.FluidReductionReceipt)
    (optics : Water.WaterOpticalCalibration Scalar Wavelength Temperature Salinity)
    (water : Water.WaterFluidOpticsWeld fluid optics) : Set₁ where
  constructor world-water-photon-weld
  field
    worldToWaterStateReference : String
    worldToPhotonEventReference : String
    sameCellReference : String
    sameTimeReference : String
    freeSurfaceGeometryReference : String
    fluidToOpticalFeedbackReference : String
    absorbedEnergyToWorldLedgerReference : String
    validationReference : String

open WorldWaterPhotonWeld public

------------------------------------------------------------------------
-- Local adaptive computation and local physical fidelity are independent but
-- may share one sensitivity/error observer.
------------------------------------------------------------------------

record WorldAdaptivePhysicsController
    {world : LESWorldEngineCarrier}
    {Cell Scalar : Set}
    (adaptiveAlgebra : Adaptive.AdaptiveTransportAlgebra Scalar)
    (allocation : Adaptive.DashiRTXAdaptiveAllocationReceipt {Cell = Cell} adaptiveAlgebra)
    : Set₁ where
  constructor world-adaptive-physics-controller
  field
    worldCellToAdaptiveCellReference : String
    errorObserverReference : String
    importanceObserverReference : String
    refreshBudgetReference : String

    requestPhysics : Cell → Fidelity.PhysicsBackendOwner
    requestReason : Cell → Fidelity.FidelityReason

    physicalEscalationPolicyReference : String
    computationalRefinementPolicyReference : String
    policiesRemainIndependentReference : String
    heldOutBiasReference : String
    performanceReceiptReference : String

open WorldAdaptivePhysicsController public

------------------------------------------------------------------------
-- Photosynthesis is one consumer of the general photon transport state, not
-- the world engine's defining purpose.
------------------------------------------------------------------------

record WorldPhotosynthesisConsumer
    {world : LESWorldEngineCarrier}
    {LeafPoint Wavelength PhotonFlux : Set}
    (field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux)
    : Set₁ where
  constructor world-photosynthesis-consumer
  field
    worldPhotonFieldProjectionReference : String
    leafGeometryProjectionReference : String
    plantAtmosphereProjectionReference : String
    waterHydraulicProjectionReference : String
    assimilationObservationReference : String
    consumerValidationReference : String

open WorldPhotosynthesisConsumer public

------------------------------------------------------------------------
-- Cross-domain escalation seam.  DomainMechanismSocket supplies the common
-- state/control/observation shape; a new backend must provide a realization,
-- not merely share variable names.
------------------------------------------------------------------------

record WorldDomainMechanismRealisation
    (world : LESWorldEngineCarrier)
    (domain : Domain.DomainMechanismSocket) : Set₁ where
  constructor world-domain-mechanism-realisation
  field
    stateProjectionReference : String
    controlProjectionReference : String
    observationProjectionReference : String
    evolutionSchedulingReference : String
    discrepancyReference : String
    conservationReference : String
    authorityReference : String
    heldOutValidationReference : String

open WorldDomainMechanismRealisation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data LESIsOneMonolithicHighestFidelityModel : Set where
lesIsNotOneMonolithicHighestFidelityModel : LESIsOneMonolithicHighestFidelityModel → ⊥
lesIsNotOneMonolithicHighestFidelityModel ()

data ProductOfModuleStatesIsPhysicalCoupling : Set where
productOfModuleStatesIsNotPhysicalCoupling : ProductOfModuleStatesIsPhysicalCoupling → ⊥
productOfModuleStatesIsNotPhysicalCoupling ()

data RendererPerformanceImpliesPhysicalAccuracy : Set where
rendererPerformanceDoesNotImplyPhysicalAccuracy : RendererPerformanceImpliesPhysicalAccuracy → ⊥
rendererPerformanceDoesNotImplyPhysicalAccuracy ()

data PhotosynthesisDefinesGeneralPhotonTransport : Set where
photosynthesisDoesNotDefineGeneralPhotonTransport : PhotosynthesisDefinesGeneralPhotonTransport → ⊥
photosynthesisDoesNotDefineGeneralPhotonTransport ()

data InteractiveEngineVisualFidelityImpliesScientificValidity : Set where
interactiveEngineVisualFidelityDoesNotImplyScientificValidity :
  InteractiveEngineVisualFidelityImpliesScientificValidity → ⊥
interactiveEngineVisualFidelityDoesNotImplyScientificValidity ()

data SharedObserverAddressDeterminesFineWorldState : Set where
sharedObserverAddressDoesNotDetermineFineWorldState :
  SharedObserverAddressDeterminesFineWorldState → ⊥
sharedObserverAddressDoesNotDetermineFineWorldState ()
