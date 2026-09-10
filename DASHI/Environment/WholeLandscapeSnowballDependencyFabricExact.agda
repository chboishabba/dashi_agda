module DASHI.Environment.WholeLandscapeSnowballDependencyFabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.TechnicalDependencyHypergraphExact as Technical
import DASHI.Environment.MosaicFireGrazingSnowballExperimentExact as Mosaic
import DASHI.Environment.HolzerPondCascadeTreatmentExperimentExact as Pond
import DASHI.Environment.HolzerPassiveStorageEnergyServiceExact as Storage
import DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact as Nitrogen

------------------------------------------------------------------------
-- WHOLE-LANDSCAPE SNOWBALL DEPENDENCY FABRIC
--
-- Reuses the recent PR snowball rule:
--
--   acquisition order != dependency payment order.
--
-- Evidence may be acquired opportunistically anywhere in the living-landscape
-- system.  It is retained at the exact source/site/time/consumer carrier.
-- Progression through a decision/theorem path advances only through explicit
-- receipt-bearing payment of the first unpaid dependency for that path.
--
-- Attribution rule:
-- external source claim/data != DASHI reconstruction != cross-source inference
-- != causal estimate != recommendation.
------------------------------------------------------------------------

data LandscapeDomain : Set where
  hydrology
  aquaticWaterQuality
  fireRegime
  grazing
  fuel
  soil
  carbon
  nitrogen
  biodiversity
  agroforestry
  livestock
  energy
  passiveStorage
  infrastructure
  governanceAuthority
  economics : LandscapeDomain

data LandscapeEvidenceRole : Set where
  externalSourceObservation
  directSiteMeasurement
  modelOutput
  causalEstimate
  authorityReceipt
  safetyLegalityReceipt
  replicationObservation
  transportObservation
  adjacentMechanismEvidence : LandscapeEvidenceRole

data DependencyKind : Set where
  mechanisticDependency
  conservationDependency
  hydraulicDependency
  energeticDependency
  ecologicalDependency
  failurePropagationDependency
  causalDependency
  authorityConditionDependency
  serviceComparisonDependency
  transportDependency : DependencyKind

data DependencyStrength : Set where
  exactSameObjectReceipt
  directMeasurementReceipt
  causalIdentificationReceipt
  conservationReceipt
  documentedEngineeringBridge
  adjacentMechanismOnly
  unresolvedCandidate : DependencyStrength

record LandscapeEvidenceCell : Set where
  constructor landscape-evidence-cell
  field
    domain : LandscapeDomain
    coordinateReference : String
    siteHistoryReference : String
    spatialBoundaryReference : String
    temporalBoundaryReference : String
    methodReference : String
    uncertaintyReference : String
    evidenceRole : LandscapeEvidenceRole
    sourceReference : String
    sourceOwner : Attribution.ClaimOwner
    carrierReference : String

open LandscapeEvidenceCell public

record WholeLandscapeAcquisitionState : Set where
  constructor whole-landscape-acquisition-state
  field
    acquiredCells : List LandscapeEvidenceCell
    waterEvidenceObserved : Bool
    fireEvidenceObserved : Bool
    grazingEvidenceObserved : Bool
    fuelEvidenceObserved : Bool
    soilEvidenceObserved : Bool
    carbonEvidenceObserved : Bool
    nitrogenEvidenceObserved : Bool
    biodiversityEvidenceObserved : Bool
    infrastructureEvidenceObserved : Bool
    energyEvidenceObserved : Bool
    authorityEvidenceObserved : Bool
    economicsEvidenceObserved : Bool
    replicationEvidenceObserved : Bool
    transportEvidenceObserved : Bool
    outOfOrderEvidenceRetained : Bool

open WholeLandscapeAcquisitionState public

------------------------------------------------------------------------
-- Dependency edges.
--
-- Ecological/physical dependencies are represented directly here.  When an
-- engineering/programmatic bridge is claimed, the existing source-typed
-- TechnicalDependencyHypergraph may be attached as supporting evidence.  Mere
-- domain resemblance is not promoted into a dependency.
------------------------------------------------------------------------

record LandscapeDependencyEdge : Set where
  constructor landscape-dependency-edge
  field
    edgeId : String
    sourceDomains : List LandscapeDomain
    targetDomains : List LandscapeDomain
    dependencyKind : DependencyKind
    strength : DependencyStrength
    sameObjectReference : String
    constitutiveOrMechanismReference : String
    measurementReference : String
    sourceAttributionReference : String
    supportingTechnicalEdges : List Technical.TechnicalHyperedge
    boundedReading : String
    excludedPromotion : String

open LandscapeDependencyEdge public

data LandscapeEdgeDisposition : Set where
  survivesLandscapeDependencyQuotient
  retainedAsAdjacentMechanismCandidate
  retainedAsUnresolvedCandidate : LandscapeEdgeDisposition

edgeDisposition : LandscapeDependencyEdge → LandscapeEdgeDisposition
edgeDisposition edge with strength edge
... | exactSameObjectReceipt = survivesLandscapeDependencyQuotient
... | directMeasurementReceipt = survivesLandscapeDependencyQuotient
... | causalIdentificationReceipt = survivesLandscapeDependencyQuotient
... | conservationReceipt = survivesLandscapeDependencyQuotient
... | documentedEngineeringBridge = survivesLandscapeDependencyQuotient
... | adjacentMechanismOnly = retainedAsAdjacentMechanismCandidate
... | unresolvedCandidate = retainedAsUnresolvedCandidate

record SurvivingLandscapeDependency : Set where
  constructor surviving-landscape-dependency
  field
    edge : LandscapeDependencyEdge
    survives : edgeDisposition edge ≡ survivesLandscapeDependencyQuotient
    paymentReference : String

open SurvivingLandscapeDependency public

------------------------------------------------------------------------
-- Path payment.
------------------------------------------------------------------------

data WholeLandscapeGate : Set where
  interventionIdentityGate
  attributionEntitlementGate
  culturalAuthorityGateWhenClaimed
  safetyLegalityGate
  sameSiteHistoryGate
  waterHydrologyGate
  fireExecutionGate
  grazingExposureGate
  fireGrazingCouplingGate
  fuelStateGate
  nitrogenDeliveryGate
  nitrogenUptakeGate
  soilResponseGate
  carbonResponseGate
  biodiversityResponseGate
  livestockResponseGate
  infrastructureReliabilityGate
  energyServiceGate
  economicBoundaryGate
  causalIdentificationGate
  replicationGate
  transportGate
  recommendationGate : WholeLandscapeGate

record WholeLandscapePaymentState : Set where
  constructor whole-landscape-payment-state
  field
    interventionIdentityPaid : Bool
    attributionEntitlementPaid : Bool
    culturalAuthorityPaidWhenRequired : Bool
    safetyLegalityPaid : Bool
    sameSiteHistoryPaid : Bool
    waterHydrologyPaid : Bool
    fireExecutionPaid : Bool
    grazingExposurePaid : Bool
    fireGrazingCouplingPaid : Bool
    fuelStatePaid : Bool
    nitrogenDeliveryPaid : Bool
    nitrogenUptakePaid : Bool
    soilResponsePaid : Bool
    carbonResponsePaid : Bool
    biodiversityResponsePaid : Bool
    livestockResponsePaid : Bool
    infrastructureReliabilityPaid : Bool
    energyServicePaid : Bool
    economicBoundaryPaid : Bool
    causalIdentificationPaid : Bool
    replicationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open WholeLandscapePaymentState public

record WholeLandscapeSnowballState : Set where
  constructor whole-landscape-snowball-state
  field
    acquisition : WholeLandscapeAcquisitionState
    dependencies : List LandscapeDependencyEdge
    payment : WholeLandscapePaymentState
    canonicalPathReference : String

open WholeLandscapeSnowballState public

-- Exact recent-PR snowball invariant: acquisition cannot mutate payment.
snowballAcquisitionDoesNotAdvancePayment :
  WholeLandscapeAcquisitionState →
  WholeLandscapePaymentState →
  WholeLandscapePaymentState
snowballAcquisitionDoesNotAdvancePayment _ payment = payment

------------------------------------------------------------------------
-- Existing-lane adapters.  These do not reinterpret the underlying owners;
-- they only retain exact carrier references in the whole-landscape snowball.
------------------------------------------------------------------------

record MosaicLaneAdmission : Set where
  constructor mosaic-lane-admission
  field
    mosaicState : Mosaic.MosaicSnowballState
    wholeLandscapeSiteReference : String
    exactPatchCarrierReference : String
    sourceAttributionPreserved : Bool

open MosaicLaneAdmission public

record PondLaneAdmission : Set where
  constructor pond-lane-admission
  field
    experiment : Pond.PondCascadeExperiment
    wholeLandscapeWaterBoundaryReference : String
    stageIdentityPreserved : Bool
    sourceAttributionPreserved : Bool

open PondLaneAdmission public

record NitrogenLaneAdmission : Set where
  constructor nitrogen-lane-admission
  field
    packet : Nitrogen.NitrogenDeliveryPacket
    wholeLandscapeNitrogenBoundaryReference : String
    originAndPathwayPreserved : Bool
    sourceAttributionPreserved : Bool

open NitrogenLaneAdmission public

record PassiveStorageLaneAdmission : Set where
  constructor passive-storage-lane-admission
  field
    comparison : Storage.MatchedStorageEnergyComparison
    wholeLandscapeEnergyBoundaryReference : String
    matchedStorageServicePreserved : Bool
    sourceAttributionPreserved : Bool

open PassiveStorageLaneAdmission public

------------------------------------------------------------------------
-- Cross-lane candidate dependencies.  These are schema-level DASHI
-- reconstruction objects, not empirical claims that the effect exists at a
-- particular site.
------------------------------------------------------------------------

waterToGrazingCandidate : LandscapeDependencyEdge
waterToGrazingCandidate =
  landscape-dependency-edge
    "water-state-to-grazing-distribution"
    (hydrology ∷ [])
    (grazing ∷ livestock ∷ [])
    ecologicalDependency
    unresolvedCandidate
    "same site/history fibre required"
    "water availability may alter animal spatial use; no site effect asserted"
    "measurement/causal receipt required"
    "DASHI cross-domain candidate dependency"
    []
    "Candidate consumer edge for matched LES experiment design."
    "Does not assert that changing water placement causes improved grazing distribution or livestock performance."

fireToFuelCandidate : LandscapeDependencyEdge
fireToFuelCandidate =
  landscape-dependency-edge
    "fire-regime-to-fuel-state"
    (fireRegime ∷ [])
    (fuel ∷ [])
    ecologicalDependency
    unresolvedCandidate
    "same patch and fire event required"
    "fire can alter fuel amount/structure; effect requires measurement"
    "pre/post fuel receipt required"
    "DASHI cross-domain candidate dependency"
    []
    "Candidate fire/fuel edge retained for snowball acquisition."
    "Does not promote observed fuel change into wildfire-risk reduction."

nitrogenToPlantSoilCandidate : LandscapeDependencyEdge
nitrogenToPlantSoilCandidate =
  landscape-dependency-edge
    "nitrogen-delivery-to-soil-plant-state"
    (nitrogen ∷ [])
    (soil ∷ carbon ∷ [])
    conservationDependency
    unresolvedCandidate
    "same nitrogen packet/site/horizon required"
    "delivery, availability, uptake and allocation remain distinct"
    "nitrogen balance and uptake receipts required"
    "DASHI cross-domain candidate dependency"
    []
    "Connects the existing nitrogen consumer fibre to whole-landscape soil/carbon consumers."
    "Does not identify delivered N with uptake, biomass, yield or soil-carbon gain."

energyToWaterInfrastructureCandidate : LandscapeDependencyEdge
energyToWaterInfrastructureCandidate =
  landscape-dependency-edge
    "energy-to-water-infrastructure-service"
    (energy ∷ infrastructure ∷ [])
    (hydrology ∷ aquaticWaterQuality ∷ [])
    energeticDependency
    unresolvedCandidate
    "same device/load/water service required"
    "powered pumping/aeration and passive gravity service require matched-service comparison"
    "load, head, flow and service receipts required"
    "DASHI cross-domain candidate dependency"
    []
    "Whole-landscape energy/water dependency candidate."
    "Does not infer pump displacement, aeration benefit or lower lifecycle energy from gravity/passive labels."

canonicalWholeLandscapeCandidateEdges : List LandscapeDependencyEdge
canonicalWholeLandscapeCandidateEdges =
  waterToGrazingCandidate ∷
  fireToFuelCandidate ∷
  nitrogenToPlantSoilCandidate ∷
  energyToWaterInfrastructureCandidate ∷ []

------------------------------------------------------------------------
-- WrongType / non-promotion barriers.
------------------------------------------------------------------------

data MoreEvidenceMeansMorePaymentPermission : Set where
data AdjacentEdgeMeansDependencyPermission : Set where
data SurvivingDependencyMeansCausalEffectPermission : Set where
data SameConsumerMeansSamePracticePermission : Set where
data SameOutcomeMeansSameProvenancePermission : Set where
data CarbonImprovementMeansWholeSystemBenefitPermission : Set where
data LocalReplicationMeansTransportPermission : Set where
data MultiDomainCoverageMeansRecommendationPermission : Set where

moreEvidenceDoesNotAdvancePaymentByItself : MoreEvidenceMeansMorePaymentPermission → ⊥
moreEvidenceDoesNotAdvancePaymentByItself ()

adjacentMechanismDoesNotBecomeDependency : AdjacentEdgeMeansDependencyPermission → ⊥
adjacentMechanismDoesNotBecomeDependency ()

survivingDependencyDoesNotByItselfIdentifyCausalEffect :
  SurvivingDependencyMeansCausalEffectPermission → ⊥
survivingDependencyDoesNotByItselfIdentifyCausalEffect ()

sameConsumerDoesNotIdentifySameManagementPractice : SameConsumerMeansSamePracticePermission → ⊥
sameConsumerDoesNotIdentifySameManagementPractice ()

sameOutcomeDoesNotEraseSourceProvenance : SameOutcomeMeansSameProvenancePermission → ⊥
sameOutcomeDoesNotEraseSourceProvenance ()

carbonImprovementDoesNotProveWholeSystemBenefit : CarbonImprovementMeansWholeSystemBenefitPermission → ⊥
carbonImprovementDoesNotProveWholeSystemBenefit ()

localReplicationDoesNotAutomaticallyPayTransport : LocalReplicationMeansTransportPermission → ⊥
localReplicationDoesNotAutomaticallyPayTransport ()

broadCoverageDoesNotAutomaticallyPromoteRecommendation : MultiDomainCoverageMeansRecommendationPermission → ⊥
broadCoverageDoesNotAutomaticallyPromoteRecommendation ()

record WholeLandscapeSnowballBoundary : Set where
  constructor whole-landscape-snowball-boundary
  field
    outOfOrderAcquisitionMayBeRetained : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    firstUnpaidDependencyRemainsAuthoritative : Bool
    weakAdjacencyDoesNotSurviveDependencyQuotient : Bool
    sourceOwnershipSurvivesCrossPollination : Bool
    sameConsumerDoesNotErasePracticeIdentity : Bool
    replicationAndTransportRemainDistinct : Bool
    recommendationRequiresExplicitPromotionGate : Bool
    broadEvidenceCoverageAutomaticallyPaysPath : Bool

canonicalWholeLandscapeSnowballBoundary : WholeLandscapeSnowballBoundary
canonicalWholeLandscapeSnowballBoundary =
  whole-landscape-snowball-boundary true true true true true true true true false
