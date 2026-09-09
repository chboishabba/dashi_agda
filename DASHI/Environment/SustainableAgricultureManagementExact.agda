module DASHI.Environment.SustainableAgricultureManagementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as Root
import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact as KNFLoop
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- SUSTAINABLE FARMING / MANAGEMENT PRACTICE FAMILY
--
-- Every practice is represented as management applied to a situated system.
-- Practice label, mechanism hypothesis, measured response, causal effect and
-- recommendation are intentionally different coordinates.
------------------------------------------------------------------------

data ManagementTechnique : Set where
  agroecologicalDiversification
  integratedPestManagement
  coverCrop
  noTill
  reducedTill
  conservationCropRotation
  compostOrOrganicAmendment
  nutrientManagement
  agroforestry
  alleyCropping
  riparianForestBuffer
  windbreak
  forestFarming
  silvopasture
  prescribedGrazing
  organicManagement
  koreanNaturalFarming
  permacultureDesign
  biocharAmendment
  waterHarvesting
  mulching
  intercropping
  polyculture
  integratedCropLivestock : ManagementTechnique

data ManagementDomain : Set where
  soilDomain
  cropDomain
  pestDomain
  waterDomain
  nutrientDomain
  livestockDomain
  treeCropDomain
  wholeFarmDomain : ManagementDomain

data MechanismHypothesis : Set where
  erosionProtection
  reducedSoilDisturbance
  increasedLivingCover
  alteredResidueReturn
  alteredNutrientCycling
  alteredWaterRetention
  alteredPestPressure
  alteredPredatorService
  alteredMicrobialProcess
  alteredRootAcquisition
  alteredCarbonStorage
  alteredHeatOrWindExposure
  alteredLivestockForageUse
  increasedFunctionalDiversity
  mechanismUnresolved : MechanismHypothesis

data ResponseCoordinate : Set where
  soilOrganicMatterResponse
  erosionResponse
  infiltrationResponse
  nutrientAvailabilityResponse
  microbialResponse
  cropPerformanceResponse
  pestResponse
  pesticideUseResponse
  biodiversityResponse
  livestockResponse
  waterQualityResponse
  carbonResponse
  labourResponse
  profitabilityResponse
  resilienceResponse : ResponseCoordinate

data EvidenceState : Set where
  practiceDefined
  mechanismProposed
  responseObserved
  effectEstimated
  effectReplicated
  recommendationAdmitted : EvidenceState

record ManagementPractice : Set where
  constructor management-practice
  field
    technique : ManagementTechnique
    source : Sources.SustainableAgricultureSource
    domain : ManagementDomain
    siteContext : String
    timingContext : String
    implementationReference : String

open ManagementPractice public

record ManagementMechanismCandidate : Set where
  constructor management-mechanism-candidate
  field
    practice : ManagementPractice
    mechanism : MechanismHypothesis
    samePracticeSourceFamily : Sources.family (source practice) ≡ Sources.family (source practice)
    mechanismEvidenceReference : String

open ManagementMechanismCandidate public

record ManagementOutcomeEvidence : Set where
  constructor management-outcome-evidence
  field
    practice : ManagementPractice
    response : ResponseCoordinate
    evidenceState : EvidenceState
    measurementMethod : String
    baselineOrComparator : String
    resultReference : String
    geographicScope : String
    temporalScope : String

open ManagementOutcomeEvidence public

------------------------------------------------------------------------
-- Technique-specific canonical practice definitions.
------------------------------------------------------------------------

canonicalCoverCrop : ManagementPractice
canonicalCoverCrop = management-practice
  coverCrop Sources.nrcsCoverCrop340 soilDomain
  "site-specific" "fallow/intercrop window"
  "plant cover crop under applicable local NRCS/FOTG or equivalent agronomic specification"

canonicalNoTill : ManagementPractice
canonicalNoTill = management-practice
  noTill Sources.nrcsNoTill329 soilDomain
  "site-specific" "cropping sequence"
  "minimise soil disturbance under a locally specified no-till system"

canonicalCropRotation : ManagementPractice
canonicalCropRotation = management-practice
  conservationCropRotation Sources.nrcsCropRotation328 cropDomain
  "site-specific" "multi-season sequence"
  "planned crop sequence with conservation objectives"

canonicalIPM : ManagementPractice
canonicalIPM = management-practice
  integratedPestManagement Sources.faoIPM pestDomain
  "site/pest/crop-specific" "monitoring and action-threshold cycle"
  "integrate ecological, biological, physical, cultural and where appropriate chemical controls"

canonicalAgroforestry : ManagementPractice
canonicalAgroforestry = management-practice
  agroforestry Sources.usdaAgroforestry treeCropDomain
  "site-specific" "multi-year perennial horizon"
  "intentional integration of woody perennials with crops and/or livestock"

canonicalSilvopasture : ManagementPractice
canonicalSilvopasture = management-practice
  silvopasture Sources.usdaSilvopasture2025 livestockDomain
  "site-specific" "multi-year tree/forage/livestock horizon"
  "intentional tree/shrub + forage + livestock integration with active grazing/tree management"

canonicalPrescribedGrazing : ManagementPractice
canonicalPrescribedGrazing = management-practice
  prescribedGrazing Sources.nrcsPrescribedGrazing528 livestockDomain
  "site/forage/herd-specific" "adaptive grazing schedule"
  "manage timing, duration, intensity and recovery according to declared objectives"

canonicalOrganicManagement : ManagementPractice
canonicalOrganicManagement = management-practice
  organicManagement Sources.nrcsOrganicHealthySoils wholeFarmDomain
  "certification and site context explicit" "cropping horizon"
  "organic management surface; soil-health practices remain separately specified"

canonicalKNFManagement : ManagementPractice
canonicalKNFManagement = management-practice
  koreanNaturalFarming Sources.knfExistingOwner wholeFarmDomain
  "site/application context explicit" "preparation/application timing explicit"
  "reuse DASHI.Environment.KoreanNaturalFarmingExact application carrier"

canonicalPermacultureManagement : ManagementPractice
canonicalPermacultureManagement = management-practice
  permacultureDesign Sources.permacultureExistingOwner wholeFarmDomain
  "situated landscape context" "iterative design horizon"
  "reuse source-bounded permaculture/LES observation and design carriers"

------------------------------------------------------------------------
-- Cross-domain adapters: existing physics/biology remains authoritative.
------------------------------------------------------------------------

record SoilManagementAdapter
    (soil : Soil.SoilCNProcessNetwork)
    (practice : ManagementPractice) : Set₁ where
  constructor soil-management-adapter
  field
    mechanismCandidate : ManagementMechanismCandidate
    samePractice : ManagementMechanismCandidate.practice mechanismCandidate ≡ practice
    sameSoilNetworkReference : String
    affectedPoolsOrProcessesReference : String
    conservationStillApplies : Bool
    responseEvidence : ManagementOutcomeEvidence

open SoilManagementAdapter public

record RootManagementAdapter
    (root : Root.RootSoilIonWaterMechanism)
    (practice : ManagementPractice) : Set₁ where
  constructor root-management-adapter
  field
    rootMechanism : Root.RootSoilIonWaterMechanism
    sameRoot : rootMechanism ≡ root
    pathwayReference : String
    waterNutrientStateReference : String
    responseEvidence : ManagementOutcomeEvidence

open RootManagementAdapter public

record KNFManagementAdapter : Set where
  constructor knf-management-adapter
  field
    practice : ManagementPractice
    isCanonicalKNF : practice ≡ canonicalKNFManagement
    knfApplication : KNF.KNFApplication
    soilPlantFruitObservation : KNFLoop.SoilPlantFruitObservationPacket

open KNFManagementAdapter public

record SituatedManagementObservation : Set where
  constructor situated-management-observation
  field
    practice : ManagementPractice
    observation : LES.SituatedObservation
    outcome : ManagementOutcomeEvidence

open SituatedManagementObservation public

------------------------------------------------------------------------
-- Multi-practice systems are compositions, not aliases.
------------------------------------------------------------------------

record ManagementStack : Set where
  constructor management-stack
  field
    primary : ManagementPractice
    secondary : ManagementPractice
    interactionReference : String
    compatibilityEvidenceReference : String

open ManagementStack public

coverCropNoTillStack : ManagementStack
coverCropNoTillStack = management-stack
  canonicalCoverCrop canonicalNoTill
  "cover crop termination/residue and no-till implementation interact"
  "requires local compatibility/adaptation evidence"

silvopastureGrazingStack : ManagementStack
silvopastureGrazingStack = management-stack
  canonicalSilvopasture canonicalPrescribedGrazing
  "silvopasture includes managed tree-forage-livestock interaction; grazing schedule remains separately specified"
  "requires tree protection, forage, stocking, recovery and site evidence"

------------------------------------------------------------------------
-- Firewalls / WrongType barriers.
------------------------------------------------------------------------

data SustainableLabelMeansBeneficialPermission : Set where

data SharedGoalMeansSameTechniquePermission : Set where

data PracticeDefinitionMeansMechanismPermission : Set where

data MechanismMeansMeasuredOutcomePermission : Set where

data ObservedOutcomeMeansCausalEffectPermission : Set where

data EffectAtOneSiteMeansPortableRecommendationPermission : Set where

data OrganicMeansSoilHealthyPermission : Set where

data NoTillMeansNoHerbicidePermission : Set where

data AgroforestryMeansSilvopasturePermission : Set where

data IPMMeansNoPesticidePermission : Set where

sustainableLabelDoesNotProveBenefit : SustainableLabelMeansBeneficialPermission → ⊥
sustainableLabelDoesNotProveBenefit ()

sharedGoalDoesNotIdentifyTechniques : SharedGoalMeansSameTechniquePermission → ⊥
sharedGoalDoesNotIdentifyTechniques ()

practiceDefinitionDoesNotProveMechanism : PracticeDefinitionMeansMechanismPermission → ⊥
practiceDefinitionDoesNotProveMechanism ()

mechanismDoesNotProveMeasuredOutcome : MechanismMeansMeasuredOutcomePermission → ⊥
mechanismDoesNotProveMeasuredOutcome ()

observedOutcomeDoesNotByItselfIdentifyCausalEffect : ObservedOutcomeMeansCausalEffectPermission → ⊥
observedOutcomeDoesNotByItselfIdentifyCausalEffect ()

oneSiteEffectDoesNotAutomaticallyTransfer : EffectAtOneSiteMeansPortableRecommendationPermission → ⊥
oneSiteEffectDoesNotAutomaticallyTransfer ()

organicLabelDoesNotProveSoilHealth : OrganicMeansSoilHealthyPermission → ⊥
organicLabelDoesNotProveSoilHealth ()

noTillDoesNotDefinitionallyMeanNoHerbicide : NoTillMeansNoHerbicidePermission → ⊥
noTillDoesNotDefinitionallyMeanNoHerbicide ()

agroforestryIsNotIdenticalToSilvopasture : AgroforestryMeansSilvopasturePermission → ⊥
agroforestryIsNotIdenticalToSilvopasture ()

ipmDoesNotDefinitionallyMeanZeroPesticide : IPMMeansNoPesticidePermission → ⊥
ipmDoesNotDefinitionallyMeanZeroPesticide ()

record SustainableAgricultureManagementBoundary : Set where
  constructor sustainable-agriculture-management-boundary
  field
    practiceFamiliesRemainDistinct : Bool
    mechanismAndOutcomeRemainDistinct : Bool
    outcomeAndCausalEffectRemainDistinct : Bool
    causalEffectAndRecommendationRemainDistinct : Bool
    siteContextIsFirstClass : Bool
    multiPracticeInteractionsNeedEvidence : Bool
    existingSoilRootLESMachineryRemainsAuthoritative : Bool

canonicalSustainableAgricultureManagementBoundary : SustainableAgricultureManagementBoundary
canonicalSustainableAgricultureManagementBoundary =
  sustainable-agriculture-management-boundary true true true true true true true
