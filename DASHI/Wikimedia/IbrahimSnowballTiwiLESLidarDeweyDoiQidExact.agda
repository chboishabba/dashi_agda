module DASHI.Wikimedia.IbrahimSnowballTiwiLESLidarDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Environment.LESSituatedObservationInteractionExact as LESObservation
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiPredationHabitatDeweyDoiQidExact as Prior

------------------------------------------------------------------------
-- TIWI / LES / LIDAR DEWEY-DOI-QID SNOWBALL
--
-- LiDAR is admitted as one instrument-survey observation channel inside the
-- existing LES situated-observation carrier.  It may provide geometry and
-- vegetation-structure evidence.  It does not replace site, season, management
-- history, ecological relation, knowledge provenance, justice, Country
-- authority, causal identification, or recommendation.
------------------------------------------------------------------------

lidarQid : Identity.ExternalIdentityDemand
lidarQid = Identity.mkOptionalIdentityDemand
  "Tiwi LES LiDAR Ibrahim continuation" "external sensing-technology identity"
  "lidar / LiDAR / light detection and ranging" Identity.wikidataQid
  (Identity.verified "Q5674822" "Wikidata LiDAR item inspected 2026-09-11; technology identity does not create ecological evidence")

remoteSensingQid : Identity.ExternalIdentityDemand
remoteSensingQid = Identity.mkOptionalIdentityDemand
  "Tiwi LES LiDAR Ibrahim continuation" "external observation-method identity"
  "remote sensing" Identity.wikidataQid
  (Identity.verified "Q199687" "Wikidata remote-sensing concept inspected 2026-09-11")

forestCanopyQid : Identity.ExternalIdentityDemand
forestCanopyQid = Identity.mkOptionalIdentityDemand
  "Tiwi LES LiDAR Ibrahim continuation" "external vegetation-structure identity"
  "forest canopy" Identity.wikidataQid
  (Identity.verified "Q105427924" "Wikidata forest-canopy concept inspected 2026-09-11; distinct from generic architectural canopy Q1589116")

terrestrialLaserScanningQid : Identity.ExternalIdentityDemand
terrestrialLaserScanningQid = Identity.mkOptionalIdentityDemand
  "Tiwi LES LiDAR Ibrahim continuation" "external sensing-method identity"
  "terrestrial laser scanning"
  Identity.wikidataQid
  (Identity.unresolved "No safely verified direct Wikidata concept item promoted in this tranche; scholarly-article items are not method identities")

------------------------------------------------------------------------
-- Dewey / DOI / QID coordinates.  Exact DDC for LiDAR itself remains open;
-- ecological use is safely placed only at the consumer side.
------------------------------------------------------------------------

lidarMethodCoordinate : Traversal.DashiKnowledgeCoordinate
lidarMethodCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiLESLidarDeweyDoiQidExact.agda"
  "LiDAR / remote-sensing observation method"
  "DDC unresolved for LiDAR method itself; no neighbouring engineering class promoted as exact"
  "Q5674822; Q199687"
  "DOI 10.1071/BT25031; DOI 10.1002/rse2.177"

forestStructureCoordinate : Traversal.DashiKnowledgeCoordinate
forestStructureCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiLESLidarDeweyDoiQidExact.agda"
  "forest / savanna vegetation-structure consumer"
  "577.3 — forest ecology; ecological classification coordinate only"
  "Q105427924"
  "DOI 10.1071/BT25031"

habitatStructureCoordinate : Traversal.DashiKnowledgeCoordinate
habitatStructureCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiLESLidarDeweyDoiQidExact.agda"
  "arboreal habitat / den-tree structure consumer"
  "577 — ecology; 599.x taxon placement remains separate"
  "Q52105"
  "DOI 10.1002/rse2.177"

lidarSupportsForestStructure : Traversal.DashiFirstLinkEdge
lidarSupportsForestStructure = Traversal.dashi-first-link-edge
  lidarMethodCoordinate forestStructureCoordinate Traversal.supportedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "ALS point clouds can support DTM/DSM/CHM and individual-crown geometry; method identity is not ecological interpretation"
  true

forestStructureSupportsHabitat : Traversal.DashiFirstLinkEdge
forestStructureSupportsHabitat = Traversal.dashi-first-link-edge
  forestStructureCoordinate habitatStructureCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "vegetation structure may support habitat consumers, but canopy geometry alone does not determine den use, abundance, connectivity or predation"
  true

------------------------------------------------------------------------
-- Primary source roles.
------------------------------------------------------------------------

data LidarLESSourceRole : Set where
  landscapeCanopyGeometryMethod
  arborealDenTreeTLSStudy : LidarLESSourceRole

record LidarLESPrimarySource : Set where
  constructor lidar-les-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : LidarLESSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open LidarLESPrimarySource public

normanEtAl2025 : LidarLESPrimarySource
normanEtAl2025 = lidar-les-primary-source
  "P. Norman; T. R. Bhatt; J. Wraith; B. Mackey"
  "Landscape-wide modelling of canopy tree crowns and heights using LiDAR: a case study in the Northern Rivers of New South Wales, Australia"
  "Australian Journal of Botany 73(7):BT25031"
  2025
  "DOI 10.1071/BT25031"
  landscapeCanopyGeometryMethod
  "Primary ALS study using publicly available airborne laser scanning, LiDAR-derived canopy-height modelling and Dalponte individual-crown segmentation across approximately 3.1 million ha; reports 180,709,102 modelled tree crowns."
  "Methodological transferability does not create Tiwi calibration, species identity, habitat quality, carbon, productivity, biodiversity, management benefit or authority over Country."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

stoboWilsonEtAl2021 : LidarLESPrimarySource
stoboWilsonEtAl2021 = lidar-les-primary-source
  "Alyson M. Stobo-Wilson; Brett P. Murphy; Teigan Cremona; Susan M. Carthew; Shaun R. Levick"
  "Illuminating den-tree selection by an arboreal mammal using terrestrial laser scanning in northern Australia"
  "Remote Sensing in Ecology and Conservation 7(2):154-168"
  2021
  "DOI 10.1002/rse2.177"
  arborealDenTreeTLSStudy
  "Primary northern-Australian terrestrial-laser-scanning study measuring three-dimensional den-tree and surrounding canopy structure for Petaurus ariel; demonstrates a fauna-facing structural observation carrier and discusses repeated-disturbance / fire applications for den-tree attrition."
  "Den-tree selection does not identify Tiwi black-footed tree-rat or possum den use, does not establish fire causality, and does not convert TLS structure into population abundance or predation exposure."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

------------------------------------------------------------------------
-- LES observation weld: instrument survey is a method coordinate, not the
-- whole situated state.
------------------------------------------------------------------------

data LidarObservationProduct : Set where
  pointCloud
  digitalTerrainModel
  digitalSurfaceModel
  canopyHeightModel
  individualCrownGeometry
  treeHeight
  verticalStructure
  denTreeGeometry
  hollowProxy : LidarObservationProduct

record LidarSituatedObservationReceipt : Set where
  constructor lidar-situated-observation-receipt
  field
    lesObservationMethod : LESObservation.ObservationMethod
    methodIsInstrumentSurvey : lesObservationMethod ≡ LESObservation.instrumentSurvey
    siteReference : String
    seasonOrAcquisitionWindow : String
    sensorPlatformReference : String
    rawPointCloudReference : String
    terrainModelReference : String
    surfaceModelReference : String
    verticalDatumReference : String
    georegistrationReference : String
    structuralProduct : LidarObservationProduct
    structuralProductReference : String
    uncertaintyReference : String
    validationReference : String
    source : LidarLESPrimarySource
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsWeldOnly : dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open LidarSituatedObservationReceipt public

record TiwiLidarHabitatMediationFrontier : Set where
  constructor tiwi-lidar-habitat-mediation-frontier
  field
    tiwiFireHistoryAcquired : Bool
    tiwiVegetationEvidenceAcquired : Bool
    lidarMethodEvidenceAcquired : Bool
    northernArborealTLSCarrierAcquired : Bool
    predatorHabitatEvidenceAcquired : Bool
    exactTiwiLidarAcquired : Bool
    exactTiwiPlotJoinPaid : Bool
    lidarToVegetationStructurePaid : Bool
    structureToDenAvailabilityPaid : Bool
    structureToPredatorExposurePaid : Bool
    predatorExposureToTaxonResponsePaid : Bool
    samePopulationAndWindowPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInferenceOnly : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open TiwiLidarHabitatMediationFrontier public

canonicalTiwiLidarHabitatFrontier : TiwiLidarHabitatMediationFrontier
canonicalTiwiLidarHabitatFrontier = tiwi-lidar-habitat-mediation-frontier
  true true true true true
  false false false false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Snowball acquisition/payment.
------------------------------------------------------------------------

record LidarLESSnowballAcquisitionState : Set where
  constructor lidar-les-snowball-acquisition-state
  field
    lidarQidAcquired : Bool
    remoteSensingQidAcquired : Bool
    forestCanopyQidAcquired : Bool
    deweyEcologyCoordinateAcquired : Bool
    exactLidarDeweyResolved : Bool
    NormanPrimaryAcquired : Bool
    StoboWilsonTLSPrimaryAcquired : Bool
    pointCloudAcquired : Bool
    dtmAcquired : Bool
    dsmAcquired : Bool
    chmAcquired : Bool
    crownGeometryAcquired : Bool
    denTreeStructureAcquired : Bool
    TiwiFireEvidenceAcquired : Bool
    TiwiFaunaEvidenceAcquired : Bool
    CountryGovernanceEvidenceRetained : Bool
    outOfOrderEvidenceRetained : Bool

open LidarLESSnowballAcquisitionState public

record LidarLESSnowballPaymentState : Set where
  constructor lidar-les-snowball-payment-state
  field
    lidarQidIdentityPaid : Bool
    remoteSensingIdentityPaid : Bool
    forestCanopyIdentityPaid : Bool
    exactDeweyMethodPaid : Bool
    sourceIdentityPaid : Bool
    sourceRoleAttributionPaid : Bool
    exactSensorPlatformPaid : Bool
    exactSitePaid : Bool
    exactAcquisitionWindowPaid : Bool
    verticalDatumPaid : Bool
    georegistrationPaid : Bool
    pointClassificationPaid : Bool
    terrainSurfaceSeparationPaid : Bool
    chmDerivationPaid : Bool
    structuralValidationPaid : Bool
    exactTiwiPlotJoinPaid : Bool
    habitatInterpretationPaid : Bool
    denAvailabilityPaid : Bool
    predationExposurePaid : Bool
    taxonResponsePaid : Bool
    managementHistoryRetained : Bool
    knowledgeProvenanceRetained : Bool
    CountryAuthorityRetained : Bool
    causalMediationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open LidarLESSnowballPaymentState public

snowballAcquisitionDoesNotAdvanceLidarLESPayment :
  LidarLESSnowballAcquisitionState → LidarLESSnowballPaymentState → LidarLESSnowballPaymentState
snowballAcquisitionDoesNotAdvanceLidarLESPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data LidarQidMeansMeasurement : Set where
data PointCloudMeansCanopyHeightModel : Set where
data CanopyHeightMeansHabitatQuality : Set where
data IndividualCrownMeansSpeciesIdentity : Set where
data TLSStructureMeansDenUse : Set where
data DenTreeStructureMeansPopulationBenefit : Set where
data RemoteObservationMeansWholeLESState : Set where
data BetterRemoteSensingCreatesCountryAuthority : Set where
data DeweyClassCreatesSemanticParent : Set where
data DOIIdentifiesEcologicalConcept : Set where
data NorthernAustraliaMeansSameTiwiCarrier : Set where
data LidarStructureMeansPredationMediation : Set where
data AcquisitionCreatesPayment : Set where

lidarQidDoesNotCreateMeasurement : LidarQidMeansMeasurement → ⊥
lidarQidDoesNotCreateMeasurement ()

pointCloudDoesNotCreateCHM : PointCloudMeansCanopyHeightModel → ⊥
pointCloudDoesNotCreateCHM ()

canopyHeightDoesNotCreateHabitatQuality : CanopyHeightMeansHabitatQuality → ⊥
canopyHeightDoesNotCreateHabitatQuality ()

crownDoesNotCreateSpeciesIdentity : IndividualCrownMeansSpeciesIdentity → ⊥
crownDoesNotCreateSpeciesIdentity ()

tlsStructureDoesNotCreateDenUse : TLSStructureMeansDenUse → ⊥
tlsStructureDoesNotCreateDenUse ()

denTreeStructureDoesNotCreatePopulationBenefit : DenTreeStructureMeansPopulationBenefit → ⊥
denTreeStructureDoesNotCreatePopulationBenefit ()

remoteObservationDoesNotCreateWholeLESState : RemoteObservationMeansWholeLESState → ⊥
remoteObservationDoesNotCreateWholeLESState ()

betterRemoteSensingDoesNotCreateCountryAuthority : BetterRemoteSensingCreatesCountryAuthority → ⊥
betterRemoteSensingDoesNotCreateCountryAuthority ()

deweyDoesNotCreateSemanticParent : DeweyClassCreatesSemanticParent → ⊥
deweyDoesNotCreateSemanticParent ()

doiDoesNotIdentifyEcologicalConcept : DOIIdentifiesEcologicalConcept → ⊥
doiDoesNotIdentifyEcologicalConcept ()

northernAustraliaDoesNotMeanSameTiwiCarrier : NorthernAustraliaMeansSameTiwiCarrier → ⊥
northernAustraliaDoesNotMeanSameTiwiCarrier ()

lidarStructureDoesNotCreatePredationMediation : LidarStructureMeansPredationMediation → ⊥
lidarStructureDoesNotCreatePredationMediation ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

------------------------------------------------------------------------
-- Reuse prior owners rather than fork them.
------------------------------------------------------------------------

priorPredationSnowball :
  Prior.PredationHabitatAcquisitionState → Prior.PredationHabitatPaymentState → Prior.PredationHabitatPaymentState
priorPredationSnowball = Prior.snowballAcquisitionDoesNotAdvancePredationHabitatPayment

lesObservationBoundary : LESObservation.ObserveInteractPlanningBoundary
lesObservationBoundary = LESObservation.canonicalObserveInteractPlanningBoundary

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
