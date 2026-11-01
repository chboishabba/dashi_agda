module DASHI.Physics.Foundations.CSIArrayGoniometerSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Physics.Foundations.PhasedArrayRFSensingSourceAtlasExact as Sources
import DASHI.Physics.Foundations.RFSensingThroughWallExact as RF
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer

------------------------------------------------------------------------
-- A finite observer ladder for the cross-pollination:
--
--   coarse Wi-Fi/CSI disturbance
--     -> retained relative phase
--     -> angle-of-arrival style angular observation
--     -> phased-array / interferometric DF role
--     -> common angle-estimation role also instantiated by a goniometer.
--
-- This is an information/observation formalisation.  It deliberately omits
-- deployment geometry, operational tracking, targeting, and weapon control.
------------------------------------------------------------------------

data CSISpatialWorld : Set where
  csiWorldA : CSISpatialWorld
  csiWorldB : CSISpatialWorld

data CoarseCSIObservation : Set where
  sameCoarseCSI : CoarseCSIObservation

data RelativePhaseObservation : Set where
  relativePhaseA : RelativePhaseObservation
  relativePhaseB : RelativePhaseObservation

coarseCSI : CSISpatialWorld -> CoarseCSIObservation
coarseCSI _ = sameCoarseCSI

relativePhaseCSI : CSISpatialWorld -> RelativePhaseObservation
relativePhaseCSI csiWorldA = relativePhaseA
relativePhaseCSI csiWorldB = relativePhaseB

aoaFromPhase : RelativePhaseObservation -> Array.ArrayBearing
aoaFromPhase relativePhaseA = Array.bearingA
aoaFromPhase relativePhaseB = Array.bearingB

aoaFromWorld : CSISpatialWorld -> Array.ArrayBearing
aoaFromWorld world = aoaFromPhase (relativePhaseCSI world)

bearingAIsNotBearingB : Array.bearingA ≡ Array.bearingB -> ⊥
bearingAIsNotBearingB ()

------------------------------------------------------------------------
-- Failed factorisation: the coarse CSI surface cannot answer the AoA query in
-- this witness because both worlds project to the same coarse observation but
-- the phase-sensitive consumer gives different bearings.
------------------------------------------------------------------------

CoarseCSIFactorsToAoA : Set
CoarseCSIFactorsToAoA =
  Σ (CoarseCSIObservation -> Array.ArrayBearing) λ recover ->
    (world : CSISpatialWorld) ->
    recover (coarseCSI world) ≡ aoaFromWorld world

coarseCSICannotRecoverAoA : ¬ CoarseCSIFactorsToAoA
coarseCSICannotRecoverAoA (recover , factors) =
  bearingAIsNotBearingB
    (trans
      (sym (factors csiWorldA))
      (factors csiWorldB))

record PhaseRefinementReceipt : Set where
  constructor phase-refinement-receipt
  field
    coarseSurfaceCollidesForAoA : Bool
    coarseSurfaceCollidesForAoAIsTrue : coarseSurfaceCollidesForAoA ≡ true
    relativePhaseSeparatesWitness : Bool
    relativePhaseSeparatesWitnessIsTrue : relativePhaseSeparatesWitness ≡ true
    phaseCoordinateFeedsAngularConsumer : Bool
    phaseCoordinateFeedsAngularConsumerIsTrue :
      phaseCoordinateFeedsAngularConsumer ≡ true
    phaseObservationDeterminesExactWorld : Bool
    phaseObservationDeterminesExactWorldIsFalse :
      phaseObservationDeterminesExactWorld ≡ false
open PhaseRefinementReceipt public

canonicalPhaseRefinementReceipt : PhaseRefinementReceipt
canonicalPhaseRefinementReceipt =
  phase-refinement-receipt true refl true refl true refl false refl

------------------------------------------------------------------------
-- Keep the modern phased-array/interferometric endpoint and historical
-- goniometer endpoint explicit.  They share an angular-observation role; the
-- common role is not hardware identity.
------------------------------------------------------------------------

record PhasedArrayEndpointReceipt : Set where
  constructor phased-array-endpoint-receipt
  field
    relativePhaseCoordinateRetained : Bool
    relativePhaseCoordinateRetainedIsTrue :
      relativePhaseCoordinateRetained ≡ true
    arrayGeometryCoordinateRetained : Bool
    arrayGeometryCoordinateRetainedIsTrue :
      arrayGeometryCoordinateRetained ≡ true
    electronicallySteeredArrayCarriesAngularRole :
      Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
      ≡ Array.angularObservationRole
    phaseComparisonArrayCarriesAngularRole :
      Array.supportsAngularObservation Array.phaseComparisonInterferometer
      ≡ Array.angularObservationRole
open PhasedArrayEndpointReceipt public

canonicalPhasedArrayEndpointReceipt : PhasedArrayEndpointReceipt
canonicalPhasedArrayEndpointReceipt =
  phased-array-endpoint-receipt true refl true refl refl refl

record GoniometerEndpointReceipt : Set where
  constructor goniometer-endpoint-receipt
  field
    mechanicalGoniometerCarriesAngleRole :
      Goniometer.implementationRole Goniometer.mechanicalAngleReadout
      ≡ Goniometer.angleEstimationRole
    phaseComparisonCarriesAngleRole :
      Goniometer.implementationRole Goniometer.phaseComparison
      ≡ Goniometer.angleEstimationRole
    goniometerRoleRetainedAfterElectronicRefinement : Bool
    goniometerRoleRetainedAfterElectronicRefinementIsTrue :
      goniometerRoleRetainedAfterElectronicRefinement ≡ true
open GoniometerEndpointReceipt public

canonicalGoniometerEndpointReceipt : GoniometerEndpointReceipt
canonicalGoniometerEndpointReceipt =
  goniometer-endpoint-receipt refl refl true refl

------------------------------------------------------------------------
-- Discovery/admission: failed factorisation proposes the missing phase/array
-- coordinates, while external primary literature can pay the physical claim.
-- Proof search itself cannot manufacture source truth.
------------------------------------------------------------------------

data CSIArrayAxis : Set where
  coarseCSIAmplitudeAxis : CSIArrayAxis
  relativePhaseAxis : CSIArrayAxis
  antennaArrayGeometryAxis : CSIArrayAxis
  angleOfArrivalAxis : CSIArrayAxis
  phasedArrayDirectionFindingAxis : CSIArrayAxis
  goniometerAngleRoleAxis : CSIArrayAxis
  primaryAoASourceAxis : CSIArrayAxis

relativePhaseProposal : Discovery.AxisProposal CSIArrayAxis
relativePhaseProposal = Discovery.axis-proposal
  relativePhaseAxis
  Discovery.failedFactorsThrough
  "angle-of-arrival consumer"
  "can the retained RF observation distinguish the angular answer?"
  "coarseCSICannotRecoverAoA gives an exact same-coarse/different-bearing obstruction"
  "phase/AoA physical interpretation must remain source-bounded"
  "observation refinement creates neither identity nor operational authority"

arrayGeometryProposal : Discovery.AxisProposal CSIArrayAxis
arrayGeometryProposal = Discovery.axis-proposal
  antennaArrayGeometryAxis
  Discovery.proofSearch
  "phase-sensitive angular observation"
  "which additional coordinate relates relative phase to spatial angle?"
  "existing PhasedArrayDirectionFindingExact keeps relative phase and array orientation distinct"
  "primary AoA literature pays only the bounded measurement relationship"
  "array geometry does not identify an emitter world"

goniometerRoleProposal : Discovery.AxisProposal CSIArrayAxis
goniometerRoleProposal = Discovery.axis-proposal
  goniometerAngleRoleAxis
  Discovery.externalKnowledgeComparison
  "historical/electronic direction-finding role comparison"
  "does the historical goniometer remain a valid endpoint in the observer lineage?"
  "RadioRadarGoniometerDirectionFindingExact proves the shared angle-estimation role"
  "repository-derived role equivalence is not an exact hardware provenance claim"
  "shared measurement role does not imply same instrument or mission"

record CSIArraySnowballRoute : Set where
  constructor csi-array-snowball-route
  field
    proofRoute : ProofSearch.RouteAdmission
    phaseRepair : Discovery.AxisProposal CSIArrayAxis
    geometryRepair : Discovery.AxisProposal CSIArrayAxis
    historicalRoleRetention : Discovery.AxisProposal CSIArrayAxis
    failedFactorisationDrivesRepair : Bool
    failedFactorisationDrivesRepairIsTrue :
      failedFactorisationDrivesRepair ≡ true
    proofSearchCreatesPhysicalTruth : Bool
    proofSearchCreatesPhysicalTruthIsFalse :
      proofSearchCreatesPhysicalTruth ≡ false
    oldGoniometerRoleMayBeDroppedAfterArrayRefinement : Bool
    oldGoniometerRoleMayBeDroppedAfterArrayRefinementIsFalse :
      oldGoniometerRoleMayBeDroppedAfterArrayRefinement ≡ false
open CSIArraySnowballRoute public

canonicalCSIArraySnowballRoute : CSIArraySnowballRoute
canonicalCSIArraySnowballRoute =
  csi-array-snowball-route
    ProofSearch.canonicalRouteAdmission
    relativePhaseProposal
    arrayGeometryProposal
    goniometerRoleProposal
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Attribution payment: reuse the exact source-atlas objects.  SpotFi/AoA
-- sources can be added to that atlas without changing this bridge's source
-- identity discipline.
------------------------------------------------------------------------

csiSurveySnowballReceipt :
  SnowballAttribution.SourceRoleSnowballReceipt Sources.csiWifiSurvey
csiSurveySnowballReceipt =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt Sources.csiWifiSurvey

csiModelSurveySnowballReceipt :
  SnowballAttribution.SourceRoleSnowballReceipt Sources.csiModelSurvey
csiModelSurveySnowballReceipt =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt Sources.csiModelSurvey

record ObserverIdentityFirewall : Set where
  constructor observer-identity-firewall
  field
    commodityCSIEqualsMechanicalGoniometer : Bool
    commodityCSIEqualsMechanicalGoniometerIsFalse :
      commodityCSIEqualsMechanicalGoniometer ≡ false
    commodityCSIEqualsPhasedArrayHardware : Bool
    commodityCSIEqualsPhasedArrayHardwareIsFalse :
      commodityCSIEqualsPhasedArrayHardware ≡ false
    mechanicalGoniometerEqualsPhasedArrayHardware : Bool
    mechanicalGoniometerEqualsPhasedArrayHardwareIsFalse :
      mechanicalGoniometerEqualsPhasedArrayHardware ≡ false
    sharedPhaseMachineryImpliesSameConsumer : Bool
    sharedPhaseMachineryImpliesSameConsumerIsFalse :
      sharedPhaseMachineryImpliesSameConsumer ≡ false
    sharedAngleRoleImpliesSameHardware : Bool
    sharedAngleRoleImpliesSameHardwareIsFalse :
      sharedAngleRoleImpliesSameHardware ≡ false
    angularObservationDeterminesExactEmitterWorld : Bool
    angularObservationDeterminesExactEmitterWorldIsFalse :
      angularObservationDeterminesExactEmitterWorld ≡ false
    observationCapabilityCreatesOperationalAuthority : Bool
    observationCapabilityCreatesOperationalAuthorityIsFalse :
      observationCapabilityCreatesOperationalAuthority ≡ false
open ObserverIdentityFirewall public

canonicalObserverIdentityFirewall : ObserverIdentityFirewall
canonicalObserverIdentityFirewall =
  observer-identity-firewall
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
