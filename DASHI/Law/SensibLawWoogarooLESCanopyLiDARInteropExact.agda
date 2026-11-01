module DASHI.Law.SensibLawWoogarooLESCanopyLiDARInteropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooS102TreeGISCompletionExact as S102
import DASHI.Law.SensibLawWoogaroo9281NegotiatedApprovedGeometryExact as Geometry

------------------------------------------------------------------------
-- WOOGAROO × LES CANOPY/LIDAR INTEROP
--
-- Cross-pollination with the existing Living Environment Simulator (LES)
-- architecture.  LES owns runtime GIS/model execution/calibration/evidence
-- serialisation; dashi_agda owns the semantic contracts, promotion gates and
-- legal consumer boundaries.  LiDAR acquisition is intentionally deferred.
------------------------------------------------------------------------

data LESSpatialCarrierKind : Set where
  rasterField : LESSpatialCarrierKind
  vectorLayer : LESSpatialCarrierKind
  pointCloud : LESSpatialCarrierKind
  treePointSet : LESSpatialCarrierKind
  crownPolygonSet : LESSpatialCarrierKind
  canopyHeightField : LESSpatialCarrierKind
  habitatField : LESSpatialCarrierKind
  observationPointSet : LESSpatialCarrierKind

data LESCanopyObservable : Set where
  treeLocation : LESCanopyObservable
  heightMax : LESCanopyObservable
  crownFootprint : LESCanopyObservable
  crownExtent : LESCanopyObservable
  canopyDensityProxy : LESCanopyObservable
  laiProxy : LESCanopyObservable
  roughnessProxy : LESCanopyObservable
  fuelDistributionProxy : LESCanopyObservable
  oldGrowthPatchCandidate : LESCanopyObservable
  optionalSpeciesHypothesis : LESCanopyObservable

data LESPromotionStage : Set where
  rawAcquisition : LESPromotionStage
  calibratedSpatialCarrier : LESPromotionStage
  derivedRemoteSensingObject : LESPromotionStage
  ecologicalInterpretation : LESPromotionStage
  legalConsumerInput : LESPromotionStage

record LESWoogarooContract : Set where
  constructor les-woogaroo-contract
  field
    sourceName : String
    sourceRole : String
    carrierKind : LESSpatialCarrierKind
    emittedObservable : LESCanopyObservable
    promotionStage : LESPromotionStage
    evidenceUse : String
    nonPromotionBoundary : String

open LESWoogarooContract public

lidarTreeLocationContract : LESWoogarooContract
lidarTreeLocationContract = les-woogaroo-contract
  "LES LiDAR/canopy lane"
  "runtime GIS/point-cloud execution owner"
  pointCloud
  treeLocation
  derivedRemoteSensingObject
  "Derive candidate stem/apex/tree positions after terrain normalisation and calibrated segmentation; join later to the negotiated 9281 clearing envelope."
  "A point-cloud-derived candidate is not automatically a botanical individual, species identification, protected tree, habitat-function proof or legal trigger."

lidarHeightContract : LESWoogarooContract
lidarHeightContract = les-woogaroo-contract
  "LES LiDAR/canopy lane"
  "runtime canopy metric owner"
  canopyHeightField
  heightMax
  derivedRemoteSensingObject
  "Provide per-candidate/tree maximum height and canopy-height context for mature-forest / restoration-lag / structural-habitat analysis."
  "Height is a structural metric; it does not by itself determine tree age, old-growth status, hollow-bearing status, ecological value or statutory significance."

lidarCrownContract : LESWoogarooContract
lidarCrownContract = les-woogaroo-contract
  "LES LiDAR/canopy lane"
  "runtime crown segmentation owner"
  crownPolygonSet
  crownFootprint
  derivedRemoteSensingObject
  "Produce crown footprints/extent for canopy continuity, clearing-envelope intersection and local tree-density estimates."
  "A segmented crown is not guaranteed one-to-one with a biological tree; crown merge/split errors remain independent calibration residuals."

canopyDensityContract : LESWoogarooContract
canopyDensityContract = les-woogaroo-contract
  "LES vegetation-field lane"
  "runtime forest-structure model owner"
  rasterField
  canopyDensityProxy
  ecologicalInterpretation
  "Compare canopy density and continuity inside/outside approved clearing and bushfire-clearing surfaces; retain temporal comparison for mature-existing versus planted/regrowth habitat."
  "Canopy-density change is not individual-tree enumeration and does not itself establish habitat essentiality or significant detrimental effect."

oldGrowthCandidateContract : LESWoogarooContract
oldGrowthCandidateContract = les-woogaroo-contract
  "LES vegetation succession / structural inference lane"
  "runtime ecological model owner"
  habitatField
  oldGrowthPatchCandidate
  ecologicalInterpretation
  "Combine structural metrics, historical imagery/change and later field evidence to identify candidate mature/old-growth patches for targeted verification."
  "Remote-sensing maturity inference is a candidate classification only; exact stand age/old-growth status requires independently appropriate evidence."

frogObservationContract : LESWoogarooContract
frogObservationContract = les-woogaroo-contract
  "LES observation/evidence layer"
  "runtime GIS join owner"
  observationPointSet
  optionalSpeciesHypothesis
  calibratedSpatialCarrier
  "Retain FrogID 948283 and 948284 as dated observation points for spatial relation to Opossum Creek, habitat and approved works."
  "Pending observer-selected taxonomy is not expert validation, agency finding or legal species fact."

------------------------------------------------------------------------
-- Deferred-acquisition discipline.
------------------------------------------------------------------------

data AcquisitionStatus : Set where
  deferred : AcquisitionStatus
  available : AcquisitionStatus
  acquired : AcquisitionStatus
  calibrated : AcquisitionStatus

record DeferredLiDARContract : Set where
  constructor deferred-lidar-contract
  field
    acquisition : AcquisitionStatus
    formalInterfaceSpecified : Bool
    runtimeOwnerSeparated : Bool
    legalPromotionGated : Bool
    mayContinueAgdaWithoutPointCloud : Bool
    futureRuntimeRequirement : String

currentDeferredLiDARContract : DeferredLiDARContract
currentDeferredLiDARContract = deferred-lidar-contract
  deferred
  true
  true
  true
  true
  "When LiDAR is acquired later, LES should emit provenance-bearing terrain-normalised point/cloud or canopy products with CRS, acquisition time, point density/resolution, processing version and uncertainty/calibration receipts before Woogaroo legal consumers ingest derived tree/crown evidence."

------------------------------------------------------------------------
-- LES Path-A/B/C style escalation: cheapest adequate carrier first.
------------------------------------------------------------------------

data SpatialEscalationPath : Set where
  pathAPlanAndOpenGIS : SpatialEscalationPath
  pathBHighResolutionImagery : SpatialEscalationPath
  pathCLiDARCanopyStructure : SpatialEscalationPath

record SpatialEscalationPolicy : Set where
  constructor spatial-escalation-policy
  field
    firstPath : SpatialEscalationPath
    secondPath : SpatialEscalationPath
    thirdPath : SpatialEscalationPath
    escalateOnlyOnConsumerResidual : Bool
    lidarNotPrivilegedByDefault : Bool
    exactConsumer : String

canonicalWoogarooSpatialEscalation : SpatialEscalationPolicy
canonicalWoogarooSpatialEscalation = spatial-escalation-policy
  pathAPlanAndOpenGIS
  pathBHighResolutionImagery
  pathCLiDARCanopyStructure
  true
  true
  "NCA ss 102-107 threatening-process / likely significant detrimental effect consumer, with reuse for EPBC habitat/offset and NCA s 13 habitat-function questions."

------------------------------------------------------------------------
-- Runtime evidence packet expected from LES later.
------------------------------------------------------------------------

record LESCanopyEvidencePacketSchema : Set where
  constructor les-canopy-evidence-packet-schema
  field
    crs : String
    acquisitionTime : String
    sourceDataset : String
    pointDensityOrResolution : String
    terrainNormalisationReceipt : String
    segmentationVersion : String
    uncertaintyReceipt : String
    treeOrCrownCarrier : String
    approvedGeometryJoin : String
    habitatJoin : String
    observationJoin : String

futureLESCanopyEvidencePacket : LESCanopyEvidencePacketSchema
futureLESCanopyEvidencePacket = les-canopy-evidence-packet-schema
  "required"
  "required"
  "required"
  "required"
  "required"
  "required"
  "required"
  "candidate tree points and/or crown polygons with structural metrics"
  "A12705838 negotiated approved extent-of-work / bushfire-clearing / retention interfaces"
  "Queensland habitat/corridor/vegetation surfaces plus project-specific ecology"
  "FrogID/iNaturalist and any later validated occurrence points"

------------------------------------------------------------------------
-- Current completion state: formal contract can advance before LiDAR arrives.
------------------------------------------------------------------------

record LESInteropCompletion : Set where
  constructor les-interop-completion
  field
    existingLESArchitectureReused : Bool
    runtimeVsProofOwnershipSeparated : Bool
    treeLocationSchemaPaid : Bool
    canopyHeightSchemaPaid : Bool
    crownSchemaPaid : Bool
    maturityCandidateSchemaPaid : Bool
    observationJoinSchemaPaid : Bool
    lidarAcquisitionRequiredNow : Bool
    lidarRuntimeExecutionDone : Bool
    legalPromotionDone : Bool

currentLESInteropCompletion : LESInteropCompletion
currentLESInteropCompletion = les-interop-completion
  true true true true true true true
  false false false

record LESInteropNextCut : Set where
  constructor les-interop-next-cut
  field
    agdaNow : String
    runtimeLater : String
    legalUseLater : String

currentLESInteropNextCut : LESInteropNextCut
currentLESInteropNextCut = les-interop-next-cut
  "Keep formal work on consumer-indexed contracts, provenance, calibration receipts, crown/tree WrongTypes, mature-existing versus planted/regrowth structural comparisons and approved-geometry joins. LiDAR acquisition is not a blocker for the Agda lane."
  "Later acquire suitable LiDAR/imagery; execute LES terrain normalisation, canopy/tree derivation, calibration and spatial serialisation; preserve exact source/acquisition/version metadata."
  "Only after calibration and same-object joins may derived canopy/tree products be admitted as evidence inputs to s 102, s 13, EPBC or offset consumers; none of those joins determines the legal conclusion automatically."

------------------------------------------------------------------------
-- WrongType / factorisation boundaries.
------------------------------------------------------------------------

data LESRuntimeOutputEqualsLegalConclusion : Set where
data LiDARCrownEqualsBotanicalIndividual : Set where
data TreeHeightEqualsTreeAge : Set where
data TallTreeEqualsOldGrowth : Set where
data CrownCountEqualsHabitatFunction : Set where
data RemoteSpeciesHypothesisEqualsValidatedSpecies : Set where
data PlanTreeLayerEqualsAllSiteTrees : Set where
data LiDARAvailabilityEqualsLiDARAcquisition : Set where
data DeferredAcquisitionBlocksFormalContract : Set where
data SpatialJoinEqualsS102Satisfaction : Set where

lesOutputDoesNotBecomeLegalConclusion : LESRuntimeOutputEqualsLegalConclusion → ⊥
lesOutputDoesNotBecomeLegalConclusion ()

lidarCrownDoesNotBecomeBotanicalIndividual : LiDARCrownEqualsBotanicalIndividual → ⊥
lidarCrownDoesNotBecomeBotanicalIndividual ()

heightDoesNotDetermineAge : TreeHeightEqualsTreeAge → ⊥
heightDoesNotDetermineAge ()

tallDoesNotDetermineOldGrowth : TallTreeEqualsOldGrowth → ⊥
tallDoesNotDetermineOldGrowth ()

crownCountDoesNotDetermineHabitatFunction : CrownCountEqualsHabitatFunction → ⊥
crownCountDoesNotDetermineHabitatFunction ()

remoteSpeciesDoesNotBecomeValidatedSpecies : RemoteSpeciesHypothesisEqualsValidatedSpecies → ⊥
remoteSpeciesDoesNotBecomeValidatedSpecies ()

planTreeLayerDoesNotBecomeAllTrees : PlanTreeLayerEqualsAllSiteTrees → ⊥
planTreeLayerDoesNotBecomeAllTrees ()

availabilityDoesNotBecomeAcquisition : LiDARAvailabilityEqualsLiDARAcquisition → ⊥
availabilityDoesNotBecomeAcquisition ()

deferredAcquisitionDoesNotBlockContract : DeferredAcquisitionBlocksFormalContract → ⊥
deferredAcquisitionDoesNotBlockContract ()

spatialJoinDoesNotDetermineS102 : SpatialJoinEqualsS102Satisfaction → ⊥
spatialJoinDoesNotDetermineS102 ()
