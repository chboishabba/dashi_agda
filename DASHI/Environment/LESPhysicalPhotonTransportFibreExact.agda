module DASHI.Environment.LESPhysicalPhotonTransportFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LES PHYSICAL PHOTON / RAY-BUNDLE TRANSPORT FIBRE
--
-- This is the world-engine transport carrier, not a renderer-specific ray type.
-- A transport token may be a radiometric sample, a photon packet, a literal
-- single-photon event, a coherent wave packet, or an application-specific
-- bundle.  Promotion between those meanings requires an explicit realization
-- receipt; Monte-Carlo ray count is never identified with physical photon count
-- by definition.
--
-- Internal proof-shape inspiration (not imported as authority):
--   DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact
--   DASHI.Moonshine.JInvariantFormulaic369PantsRendererExact
-- on branch agent/j-invariant-base369-introspective-xpoll.
-- The reused lesson is only:
--   coarse observer != fine state;
--   same-point fibre context may be independent of the coarse observer;
--   local path segments glue only across compatible seams.
------------------------------------------------------------------------

data TransportTokenSemantics : Set where
  radiometricRaySample : TransportTokenSemantics
  photonPacket : TransportTokenSemantics
  singlePhotonEvent : TransportTokenSemantics
  coherentWavePacket : TransportTokenSemantics
  applicationSpecificBundle : TransportTokenSemantics

record PhotonTransportFibre
    (FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set)
    : Set₁ where
  constructor photon-transport-fibre
  field
    fineToRay : FineEvent → RayBundle
    fineToCell : FineEvent → Cell
    eventTime : FineEvent → Time
    wavelength : FineEvent → Wavelength
    polarization : FineEvent → Polarization
    mediumAt : FineEvent → Medium
    statisticalWeight : FineEvent → Weight

    sourceGeometryReference : String
    propagationLawReference : String
    interactionLawReference : String
    timeIntegrationReference : String
    conservationReference : String
    provenanceReference : String

open PhotonTransportFibre public

record PhysicalPhotonRealisation
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set}
    (fibre : PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    : Set₁ where
  constructor physical-photon-realisation
  field
    semantics : TransportTokenSemantics
    transportEquationAuthorityReference : String
    photonOrBundleMeaningReference : String
    energyFrequencyLawReference : String
    statisticalWeightMeaningReference : String
    coherenceRegimeReference : String
    detectorOrConsumerReference : String

open PhysicalPhotonRealisation public

------------------------------------------------------------------------
-- Same coarse ray can hide different fine physical states.
------------------------------------------------------------------------

record SameRayHiddenFibreWitness
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set}
    (fibre : PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    : Set₁ where
  constructor same-ray-hidden-fibre-witness
  field
    left right : FineEvent
    sameCoarseRay : fineToRay fibre left ≡ fineToRay fibre right
    fineEventsDistinct : left ≡ right → ⊥
    hiddenDifferenceReference : String

open SameRayHiddenFibreWitness public

record SamePointContextObserver
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight Context : Set}
    (fibre : PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    : Set₁ where
  constructor same-point-context-observer
  field
    contextAt : FineEvent → Context
    observerRoleReference : String
    contextCalibrationReference : String
    contextNotRequiredToFactorThroughRay : String

open SamePointContextObserver public

------------------------------------------------------------------------
-- Local path-segment gluing.  This is the transport analogue of the existing
-- pants/gluing discipline: a shared coarse address alone is not a valid seam.
------------------------------------------------------------------------

record TransportSegment
    {FineEvent SegmentId : Set}
    : Set₁ where
  constructor transport-segment
  field
    segmentId : SegmentId
    sourceEvent : FineEvent
    targetEvent : FineEvent
    propagationReceipt : String
    interactionReceipt : String

open TransportSegment public

record SegmentGluingReceipt
    {FineEvent SegmentId : Set}
    (left right : TransportSegment {FineEvent = FineEvent} {SegmentId = SegmentId})
    : Set₁ where
  constructor segment-gluing-receipt
  field
    literalSharedEvent : targetEvent left ≡ sourceEvent right
    timeCompatibilityReference : String
    spatialCompatibilityReference : String
    mediumBoundaryCompatibilityReference : String
    wavelengthEnergyCompatibilityReference : String
    polarizationCoherenceCompatibilityReference : String
    provenanceCompatibilityReference : String

open SegmentGluingReceipt public

------------------------------------------------------------------------
-- Boundary firewall.
------------------------------------------------------------------------

record LESPhotonTransportBoundary : Set where
  constructor les-photon-transport-boundary
  field
    rendererRayIsPhysicalPhotonByDefinition : Bool
    rendererRayIsPhysicalPhotonByDefinitionIsFalse :
      rendererRayIsPhysicalPhotonByDefinition ≡ false

    equalCoarseRayDeterminesFinePhotonState : Bool
    equalCoarseRayDeterminesFinePhotonStateIsFalse :
      equalCoarseRayDeterminesFinePhotonState ≡ false

    monteCarloWeightIsPhotonCountByDefinition : Bool
    monteCarloWeightIsPhotonCountByDefinitionIsFalse :
      monteCarloWeightIsPhotonCountByDefinition ≡ false

    segmentAddressEqualityIsPhysicalGluing : Bool
    segmentAddressEqualityIsPhysicalGluingIsFalse :
      segmentAddressEqualityIsPhysicalGluing ≡ false

    explicitRealisationRequiredForLiteralPhotonSemantics : Bool
    explicitRealisationRequiredForLiteralPhotonSemanticsIsTrue :
      explicitRealisationRequiredForLiteralPhotonSemantics ≡ true

canonicalLESPhotonTransportBoundary : LESPhotonTransportBoundary
canonicalLESPhotonTransportBoundary =
  les-photon-transport-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
