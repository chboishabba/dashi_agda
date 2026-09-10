module DASHI.Environment.MosaicFireGrazingSnowballExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.MosaicFireGrazingSourceAttributionExact as Sources
import DASHI.Governance.SteffensenCulturalFireAuthorityExact as CulturalFire

------------------------------------------------------------------------
-- MOSAIC FIRE / GRAZING SNOWBALL EXPERIMENT
--
-- Exact method reused from recent snowball PR work:
--
--   acquisition order != dependency payment order.
--
-- Evidence can accumulate opportunistically and remain attached to the exact
-- patch/herbivore/time/source carrier.  The scientific/management wall only
-- advances through explicit receipt-bearing payment of its first unpaid gate.
------------------------------------------------------------------------

data FireManagementIdentity : Set where
  patchBurnGrazing
  pyricHerbivoryExperiment
  genericPrescribedMosaicBurn
  IndigenousCulturalBurning : FireManagementIdentity

data HerbivoreKind : Set where
  cattle sheep goats mixedLivestock nativeHerbivore otherHerbivore : HerbivoreKind

data MosaicCoordinate : Set where
  firePatchGeometry
  fireTiming
  fireIntensity
  fuelLoad
  vegetationStructure
  forageQuality
  herbivoreSelection
  stockingPressure
  soilNutrients
  soilCover
  erosion
  woodyEncroachment
  biodiversity
  habitatHeterogeneity
  carbonState
  livestockPerformance
  economicCost
  smokeAirQuality
  culturalAuthority
  safetyLegality : MosaicCoordinate

data AcquisitionEvidenceKind : Set where
  sourceDocument
  burnPlan
  fireWeatherObservation
  patchMap
  remoteSensing
  GPSAnimalTrack
  vegetationSurvey
  forageAssay
  soilAssay
  fuelSurvey
  biodiversitySurvey
  carbonMeasurement
  livestockMeasurement
  economicLedger
  authorityReceipt
  safetyReceipt
  replicationDataset : AcquisitionEvidenceKind

record MosaicEvidenceCell : Set where
  constructor mosaic-evidence-cell
  field
    managementIdentity : FireManagementIdentity
    coordinate : MosaicCoordinate
    evidenceKind : AcquisitionEvidenceKind
    herbivore : HerbivoreKind
    patchIdentity : String
    landscapeIdentity : String
    seasonYearReference : String
    timeSinceFireReference : String
    fireRegimeReference : String
    stockingReference : String
    rainfallReference : String
    vegetationReference : String
    methodReference : String
    uncertaintyReference : String
    source : Sources.FireGrazingSource
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    carrierReference : String

open MosaicEvidenceCell public

record MosaicSnowballAcquisitionState : Set where
  constructor mosaic-snowball-acquisition-state
  field
    acquiredCells : List MosaicEvidenceCell
    interventionIdentityObserved : Bool
    patchGeometryObserved : Bool
    fireExecutionObserved : Bool
    herbivoreExposureObserved : Bool
    herbivoreSelectionObserved : Bool
    vegetationHeterogeneityObserved : Bool
    fuelStateObserved : Bool
    soilResponseObserved : Bool
    biodiversityResponseObserved : Bool
    carbonResponseObserved : Bool
    livestockResponseObserved : Bool
    economicResponseObserved : Bool
    replicationObserved : Bool
    transportCoordinatesObserved : Bool
    outOfOrderEvidenceRetained : Bool

open MosaicSnowballAcquisitionState public

------------------------------------------------------------------------
-- Payment gates.
--
-- These are scientific/management obligations, not a new global planner.
-- A cultural-authority gate is conditionally required only when the intervention
-- is claimed as Indigenous cultural burning or invokes that authority lineage.
------------------------------------------------------------------------

data CulturalAuthorityRequirement : Set where
  culturalAuthorityRequired
  genericFireManagementNoCulturalIdentityClaim : CulturalAuthorityRequirement

data PaymentGate : Set where
  interventionIdentityGate
  culturalAuthorityGate
  fireLegalitySafetyGate
  sameLandscapePatchGate
  fireExecutionGate
  herbivoreExposureGate
  fireGrazingCouplingGate
  heterogeneityEffectGate
  fuelEffectGate
  soilEffectGate
  biodiversityEffectGate
  livestockEffectGate
  carbonEffectGate
  economicEffectGate
  replicationGate
  transportRecommendationGate : PaymentGate

record MosaicPaymentEligibility : Set where
  constructor mosaic-payment-eligibility
  field
    authorityRequirement : CulturalAuthorityRequirement
    interventionIdentityPaid : Bool
    culturalAuthorityPaidWhenRequired : Bool
    legalitySafetyPaid : Bool
    sameLandscapePatchIdentityPaid : Bool
    fireExecutionPaid : Bool
    herbivoreExposurePaid : Bool
    fireGrazingCouplingPaid : Bool
    heterogeneityEffectPaid : Bool
    fuelEffectPaid : Bool
    soilEffectPaid : Bool
    biodiversityEffectPaid : Bool
    livestockEffectPaid : Bool
    carbonEffectPaid : Bool
    economicEffectPaid : Bool
    replicationPaid : Bool
    transportRecommendationPaid : Bool

open MosaicPaymentEligibility public

-- The snowball rule: accumulated acquisition does not manufacture payment.
-- The current payment state must be supplied independently by exact receipts.
record MosaicSnowballState : Set where
  constructor mosaic-snowball-state
  field
    acquisition : MosaicSnowballAcquisitionState
    payment : MosaicPaymentEligibility

open MosaicSnowballState public

snowballAcquisitionDoesNotAlterPayment :
  (acquisition : MosaicSnowballAcquisitionState) →
  (payment : MosaicPaymentEligibility) →
  MosaicPaymentEligibility
snowballAcquisitionDoesNotAlterPayment _ payment = payment

------------------------------------------------------------------------
-- Country-authority weld for cultural-fire claims.
------------------------------------------------------------------------

record CulturalFireClaimAdmission : Set where
  constructor cultural-fire-claim-admission
  field
    interventionReference : String
    claimsIndigenousCulturalBurning : Bool
    existingAuthoritySystemReference : String
    Country : Set
    country : Country
    authorityReceiptReference : String
    authorityOwnerReference : String
    externalScientificStudyDoesNotCreateAuthority : Bool

open CulturalFireClaimAdmission public

culturalFireAuthorityOwnerReuse :
  CulturalFire.system ≡ CulturalFire.system
culturalFireAuthorityOwnerReuse = refl

------------------------------------------------------------------------
-- Causal experiment packet.
------------------------------------------------------------------------

record MosaicFireGrazingExperiment : Set where
  constructor mosaic-fire-grazing-experiment
  field
    managementIdentity : FireManagementIdentity
    authorityRequirement : CulturalAuthorityRequirement
    beforeAfterOrComparatorReference : String
    landscapeBoundaryReference : String
    patchAllocationReference : String
    fireTimingIntensityReference : String
    herbivoreSpeciesReference : String
    stockingDensityReference : String
    rainfallWeatherReference : String
    fuelReference : String
    vegetationBaselineReference : String
    outcomeCoordinates : List MosaicCoordinate
    acquiredEvidence : MosaicSnowballAcquisitionState
    paidGates : MosaicPaymentEligibility
    causalEstimandReference : String
    assignmentOrIdentificationReference : String
    uncertaintyReference : String
    sourceAttributionReference : String
    dashiExperimentOwner : Attribution.ClaimOwner
    dashiOwnsReconstruction :
      dashiExperimentOwner ≡ Attribution.dashiFormalisationOwner

open MosaicFireGrazingExperiment public

------------------------------------------------------------------------
-- WrongType / snowball barriers.
------------------------------------------------------------------------

data DatasetSizeMeansPaymentPermission : Set where
data ObservedPatchSelectionMeansPyricHerbivoryEffectPermission : Set where
data BurnPlusGrazingMeansCausalInteractionPermission : Set where
data CattleResponseMeansGenericHerbivoreResponsePermission : Set where
data HeterogeneityMeansBiodiversityBenefitPermission : Set where
data FuelReductionMeansWildfireRiskReductionPermission : Set where
data CulturalBurningLabelMeansAuthorityPermission : Set where
data PatchBurnLiteratureMeansCulturalBurningValidationPermission : Set where
data CarbonObservationMeansCarbonBenefitPermission : Set where
data ReplicationMeansTransportPermission : Set where

largeDatasetDoesNotPayDependency : DatasetSizeMeansPaymentPermission → ⊥
largeDatasetDoesNotPayDependency ()

observedSelectionDoesNotByItselfPayPyricEffect : ObservedPatchSelectionMeansPyricHerbivoryEffectPermission → ⊥
observedSelectionDoesNotByItselfPayPyricEffect ()

coOccurrenceDoesNotIdentifyFireGrazingInteraction : BurnPlusGrazingMeansCausalInteractionPermission → ⊥
coOccurrenceDoesNotIdentifyFireGrazingInteraction ()

cattleResponseDoesNotGeneraliseToAllHerbivores : CattleResponseMeansGenericHerbivoreResponsePermission → ⊥
cattleResponseDoesNotGeneraliseToAllHerbivores ()

heterogeneityDoesNotDefinitionallyProveBiodiversityBenefit : HeterogeneityMeansBiodiversityBenefitPermission → ⊥
heterogeneityDoesNotDefinitionallyProveBiodiversityBenefit ()

fuelReductionDoesNotDefinitionallyProveWildfireRiskReduction : FuelReductionMeansWildfireRiskReductionPermission → ⊥
fuelReductionDoesNotDefinitionallyProveWildfireRiskReduction ()

culturalBurningLabelDoesNotCreateAuthority : CulturalBurningLabelMeansAuthorityPermission → ⊥
culturalBurningLabelDoesNotCreateAuthority ()

patchBurnScienceDoesNotValidateCulturalBurningAuthority : PatchBurnLiteratureMeansCulturalBurningValidationPermission → ⊥
patchBurnScienceDoesNotValidateCulturalBurningAuthority ()

carbonObservationDoesNotProveNetCarbonBenefit : CarbonObservationMeansCarbonBenefitPermission → ⊥
carbonObservationDoesNotProveNetCarbonBenefit ()

replicationDoesNotAutomaticallyPayTransport : ReplicationMeansTransportPermission → ⊥
replicationDoesNotAutomaticallyPayTransport ()

record MosaicSnowballBoundary : Set where
  constructor mosaic-snowball-boundary
  field
    outOfOrderAcquisitionMayBeRetained : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    observationOfCoordinateDoesNotEqualPayment : Bool
    culturalAuthorityIsConditionalOnClaimLineage : Bool
    culturalAuthorityDelegatedToExistingOwner : Bool
    speciesResponsesRemainIndexed : Bool
    multiOutcomeEffectsRemainDistinct : Bool
    replicationAndTransportRemainDistinct : Bool
    largeDatasetAutomaticallyAdvancesPayment : Bool

canonicalMosaicSnowballBoundary : MosaicSnowballBoundary
canonicalMosaicSnowballBoundary =
  mosaic-snowball-boundary true true true true true true true true false
